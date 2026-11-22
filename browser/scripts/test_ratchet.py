#!/usr/bin/env python3
"""Replays ways of making the ratchet lie, each in a scratch copy of browser/, and requires that the
ratchet objects for the stated reason. Needs the same Verus environment as ratchet.py.

    python3 scripts/test_ratchet.py
"""
from __future__ import annotations

import importlib.util
import json
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

BROWSER = Path(__file__).resolve().parent.parent
BAD = "verus!{ pub fn bad() -> (r: u8) ensures r == 7 { proof { boom(); } 0 } }\n"
PRELUDE = "use vstd::prelude::*;\n"


def load(root: Path):
    spec = importlib.util.spec_from_file_location("ratchet_under_test", root / "scripts/ratchet.py")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod


class RatchetTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        sys.dont_write_bytecode = True
        cls.tmp = Path(tempfile.mkdtemp(prefix="ratchet-test-"))
        cls.site = cls.tmp / "site"
        cls.root = cls.site / "browser"
        cls.files = [p.relative_to(BROWSER) for p in load(BROWSER).tracked_files()]
        for rel in cls.files:
            dest = cls.root / rel
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(BROWSER / rel, dest)
        shutil.copytree(BROWSER.parent / "data", cls.site / "data")
        subprocess.run(["git", "init", "-q"], cwd=cls.site, check=True)
        (cls.site / ".gitignore").write_text("target/\n.cargo/\n")
        cls.r = load(cls.root)
        cls.env = cls.r.stack_env()
        subprocess.run([str(cls.root / "scripts/use-local-verus.sh")], env=cls.env, check=True, capture_output=True)
        cls.target = cls.r.target_directory(cls.env)
        cls.vurl = next(s for s in cls.r.CRATE_SPECS if s.name == "vurl")

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp)

    def setUp(self):
        for d in ("url", "evil"):
            shutil.rmtree(self.root / d, ignore_errors=True)
        for rel in self.files:
            if rel.parts[0] == "url" or len(rel.parts) == 1:
                (self.root / rel).parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(BROWSER / rel, self.root / rel)

    def write(self, rel: str, text: str):
        p = self.root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)

    def edit(self, rel: str, *pairs: tuple[str, str]):
        s = (self.root / rel).read_text()
        for a, b in pairs:
            self.assertEqual(s.count(a), 1, f"{rel}: {a!r}")
            s = s.replace(a, b)
        self.write(rel, s)

    def evil_module(self, text: str):
        self.write("url/src/evil.rs", PRELUDE + text)
        self.edit("url/src/lib.rs", ("pub mod ipv6;\n", "pub mod ipv6;\npub mod evil;\n"))

    def verify(self) -> dict:
        return self.r.verify_crate(self.vurl, self.env, self.target)

    def assertRejected(self, problems: list[str], pattern: str):
        self.assertTrue(any(re.search(pattern, p) for p in problems), f"wanted /{pattern}/ in {problems}")

    # -- controls -----------------------------------------------------------------------------

    def test_unmodified_crate_is_accepted(self):
        v = self.verify()
        self.assertEqual((v["problems"], v["no_cheating"]), ([], True))
        self.assertEqual(self.r.graph_problems(self.env), [])

    def test_honest_addition_is_accepted_and_counted_by_mode(self):
        before = self.verify()
        self.evil_module("verus!{ pub proof fn fine(x: u8) requires x < 4 ensures x < 5 {} }\n")
        v = self.verify()
        self.assertEqual(v["problems"], [])
        want = {**before["functions_by_mode"], "proof": before["functions_by_mode"]["proof"] + 1}
        self.assertEqual(v["functions_by_mode"], want)

    # -- escapes inside the crate -------------------------------------------------------------

    def test_include_outside_src(self):
        self.write("url/proofs/helpers.rs", "verus! { pub proof fn boom() ensures false { admit(); } }\n")
        self.evil_module('include!("../proofs/helpers.rs");\n' + BAD)
        self.assertRejected(self.verify()["problems"], "assume.*not allowed with `--no-cheating`")

    def test_include_marker_is_counted(self):
        self.write("url/proofs/helpers.rs", "verus! { #[verifier::external] pub fn f() {} }\n")
        self.evil_module('include!("../proofs/helpers.rs");\n')
        self.assertRejected(self.verify()["problems"], "trusted `external` marker")

    def test_include_from_outside_the_crate(self):
        self.write("evil/helpers.rs", "verus! { pub fn f() {} }\n")
        self.evil_module('include!("../../evil/helpers.rs");\n')
        self.assertRejected(self.verify()["problems"], "compiles .*evil/helpers.rs from outside")

    def test_axiom_fn(self):
        self.evil_module("verus!{ pub axiom fn boom() ensures false; }\n" + BAD)
        self.assertRejected(self.verify()["problems"], "external_body.*not allowed with `--no-cheating`")

    def test_parenthesised_external_body(self):
        self.evil_module("verus!{ #[verifier(external_body)] pub proof fn boom() ensures false {} }\n" + BAD)
        self.assertRejected(self.verify()["problems"], "external_body.*not allowed with `--no-cheating`")

    def test_renamed_admit(self):
        self.evil_module(
            "use vstd::prelude::admit as qed;\nverus!{ pub proof fn boom() ensures false { qed(); } }\n" + BAD
        )
        self.assertRejected(self.verify()["problems"], "admit.*not allowed with `--no-cheating`")

    def test_external_item(self):
        self.evil_module("verus!{ #[verifier::external] pub fn bad() -> u8 { 0 } }\n")
        self.assertRejected(self.verify()["problems"], "trusted `external` marker")

    def test_diverging_function(self):
        self.evil_module(
            "verus!{ #[verifier::exec_allows_no_decreases_clause] pub fn bad() ensures false { loop {} } }\n"
        )
        self.assertRejected(self.verify()["problems"], "trusted `unproved_termination` marker")

    def test_code_swapped_out_when_verus_is_not_looking(self):
        self.evil_module(
            "#[cfg(verus_keep_ghost)]\nverus!{ pub fn f() -> (r: u8) ensures r == 7 { 7 } }\n"
            "#[cfg(not(verus_keep_ghost))]\npub fn f() -> u8 { 0 }\n"
        )
        self.assertRejected(self.verify()["problems"], "trusted `hidden_from_verus` marker")

    def test_code_outside_verus_macro_is_verified(self):
        self.evil_module("pub fn f(a: u8) -> u8 { a + 1 }\n")
        self.assertRejected(self.verify()["problems"], "possible arithmetic underflow/overflow")

    def test_vacuous_lemma(self):
        self.evil_module("verus!{ pub proof fn lemma_bonus()\n    requires\n        false,\n    ensures 1 == 2 {} }\n")
        self.assertRejected(self.verify()["problems"], "`requires false`")

    # -- escapes through dependencies and manifests -------------------------------------------

    def add_dependency(self):
        self.write(
            "evil/Cargo.toml",
            '[package]\nname = "evil"\nversion = "0.1.0"\nedition = "2021"\n'
            "[dependencies]\nvstd = { workspace = true }\n[package.metadata.verus]\nverify = true\n",
        )
        self.write(
            "evil/src/lib.rs",
            PRELUDE + "verus!{ #[verifier::external_body] pub proof fn boom() ensures false {} }\n",
        )
        self.edit("Cargo.toml", ('    "url",\n', '    "url",\n    "evil",\n'))
        self.edit(
            "url/Cargo.toml",
            ("vstd = { workspace = true }\n", 'vstd = { workspace = true }\nevil = { path = "../evil" }\n'),
        )
        self.evil_module(BAD.replace("boom()", "::evil::boom()"))

    def test_trusted_dependency_in_workspace(self):
        self.add_dependency()
        self.assertRejected(self.r.graph_problems(self.env), "workspace crate evil is not ratcheted")

    def test_trusted_dependency_outside_workspace(self):
        self.add_dependency()
        self.edit("Cargo.toml", ('    "evil",\n', ""), ("[workspace]\n", '[workspace]\nexclude = ["evil"]\n'))
        self.edit("evil/Cargo.toml", ("{ workspace = true }", '"=0.0.0-2026-11-15-0327"'))
        self.assertRejected(self.r.graph_problems(self.env), "dependency evil carries Verus specs")

    def test_extra_verus_metadata(self):
        self.edit("url/Cargo.toml", ("verify = true\n", 'verify = true\ntrusted_crates = ["x"]\n'))
        self.assertRejected(self.r.graph_problems(self.env), "vurl: .package.metadata.verus. is")

    def test_verification_switched_off(self):
        self.edit("url/Cargo.toml", ("verify = true\n", "verify = false\n"))
        self.assertRejected(self.r.graph_problems(self.env), "vurl: .package.metadata.verus. is")

    def test_build_script(self):
        self.write("url/build.rs", "fn main() {}\n")
        self.assertRejected(self.r.graph_problems(self.env), "custom-build")

    # -- spec drift: proofs stay green, the oracle tests must not ------------------------------

    def test_spec_drift_fails_the_encode_set_oracles(self):
        drifts = {
            "SpecialQuery": [
                ("in_query_set(c) || c == 0x27\n", "in_query_set(c)\n"),
                ("EncodeSet::SpecialQuery => query || c == 0x27", "EncodeSet::SpecialQuery => query"),
            ],
            "Fragment": [
                ("c == 0x20 || c == 0x22 || c == 0x3C || c == 0x3E || c == 0x60\n",
                 "c == 0x20 || c == 0x22 || c == 0x3E || c == 0x60\n"),
                ("EncodeSet::Fragment => c0 || c == 0x20 || c == 0x22 || c == 0x3C",
                 "EncodeSet::Fragment => c0 || c == 0x20 || c == 0x22"),
            ],
        }  # fmt: skip
        for name, pairs in drifts.items():
            with self.subTest(name):
                self.setUp()
                self.edit("url/src/percent.rs", *pairs)
                self.assertEqual(self.verify()["problems"], [], "the drift is meant to be invisible to Verus")
                t = self.r.run_tests(self.vurl, self.env)
                self.assertNotEqual(t["exit"], 0)
                self.assertIn(f"{name} byte", t["text"])

    # -- forged or stale telemetry -------------------------------------------------------------

    def forged(self, mutate) -> list[str]:
        rec = json.loads((BROWSER / "ratchet.json").read_text())
        mutate(rec)
        self.write("ratchet.json", json.dumps(rec))
        return self.r.recorded_problems(rec)

    def test_committed_report_is_current(self):
        self.assertEqual(self.forged(lambda r: None), [])

    def test_forged_total(self):
        self.assertRejected(self.forged(lambda r: r["totals"].update(verified=999999)), "totals.verified is not the sum")

    def test_forged_crate(self):
        def mutate(r):
            r["crates"][0]["verified"] += 585
            r["totals"]["verified"] += 585

        self.assertRejected(self.forged(mutate), "vurl: verified/errors differ from its log")

    def test_forged_anything_differs_from_stats(self):
        self.assertRejected(self.forged(lambda r: r.update(vm_benchmarks_geomean_speedup=99)), "stats.json embeds")

    def test_source_change_makes_report_stale(self):
        self.edit("url/src/lib.rs", ("pub mod ipv6;\n", "pub mod ipv6;\n// touched\n"))
        self.assertRejected(self.forged(lambda r: None), "stale")


if __name__ == "__main__":
    unittest.main()
