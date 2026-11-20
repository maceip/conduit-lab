#!/usr/bin/env python3
"""Measure the verified-browser "ratchet": per crate, what Verus actually verified and how much
is trusted. Every number comes from running the tools or scanning the sources; nothing is
estimated. Writes browser/ratchet.json.

Trusted markers counted: assume(, admit(, #[verifier::external_body], #[verifier::external],
assume_specification, unsafe blocks/fns.
"""
from __future__ import annotations

import datetime as dt
import json
import os
import re
import subprocess
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
CRATES = {"vurl": ROOT / "url"}
MARKERS = {
    "assume": re.compile(r"\bassume\s*\("),
    "admit": re.compile(r"\badmit\s*\("),
    "external_body": re.compile(r"verifier::external_body"),
    "external": re.compile(r"verifier::external\b(?!_)"),
    "assume_specification": re.compile(r"\bassume_specification\b"),
    "unsafe": re.compile(r"\bunsafe\s*(\{|fn\b|impl\b)"),
}
RESULT_RE = re.compile(r"verification results::\s*(\d+) verified,\s*(\d+) errors")
TEST_RE = re.compile(r"test result: \w+\. (\d+) passed; (\d+) failed")


def stack_env() -> dict[str, str]:
    env_file = Path(os.environ.get("VERUS_STACK", Path.home() / "workspaces/verus-stack")) / "env.zsh"
    out = subprocess.run(["zsh", "-c", f"source {env_file} >/dev/null && env -0"],
                         capture_output=True, check=True).stdout.decode()
    return dict(kv.split("=", 1) for kv in out.split("\0") if "=" in kv)


def run(cmd: list[str], env: dict[str, str]) -> tuple[int, str, float]:
    t0 = time.monotonic()
    p = subprocess.run(cmd, cwd=ROOT, env=env, capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr, round(time.monotonic() - t0, 2)


def main() -> None:
    env = stack_env()
    subprocess.run([str(ROOT / "scripts/use-local-verus.sh")], env=env, check=True, capture_output=True)
    out = {"generated_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
           "generator": "browser/scripts/ratchet.py", "crates": []}
    _, vv, _ = run(["verus", "--version"], env)
    out["verus"] = next((l.split(":", 1)[1].strip() for l in vv.splitlines() if "Version" in l), None)
    for name, path in CRATES.items():
        (path / "src" / "lib.rs").touch()  # force re-verification rather than a cached result
        code, text, secs = run(["cargo", "verus", "verify", "-p", name, "--", "--triggers-mode", "silent"], env)
        m = RESULT_RE.findall(text)
        tcode, ttext, tsecs = run(["cargo", "test", "-p", name], env)
        tests = TEST_RE.findall(ttext)
        srcs = sorted(path.glob("src/**/*.rs"))
        body = "\n".join(p.read_text() for p in srcs)
        out["crates"].append({
            "name": name,
            "verify_exit": code,
            # the last results line is the crate itself (earlier lines are dependencies like vstd)
            "verified": int(m[-1][0]) if m else None,
            "errors": int(m[-1][1]) if m else None,
            "verify_seconds": secs,
            "trusted": {k: len(r.findall(body)) for k, r in MARKERS.items()},
            "source_lines": sum(len(p.read_text().splitlines()) for p in srcs),
            "tests_exit": tcode,
            "tests_passed": sum(int(a) for a, _ in tests) if tests else None,
            "tests_failed": sum(int(b) for _, b in tests) if tests else None,
            "test_seconds": tsecs,
        })
    (ROOT / "ratchet.json").write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))


if __name__ == "__main__":
    main()
