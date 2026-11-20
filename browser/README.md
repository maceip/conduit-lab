# Verified browser (Phase 1)

Design: [../docs/verified-browser-engine.md](../docs/verified-browser-engine.md).

## `vurl`: the WHATWG URL Standard in Verus

Spec source: whatwg/url@4f461b81 (2026-11-19). Each spec algorithm is transcribed as a Verus
`spec fn`, and the executable code is proved equal to it. There are no `assume`, `admit`,
`external_body` or `unsafe` items (`scripts/ratchet.py` counts them).

| Module | Spec algorithms | Exec proved equal | Spec theorems |
|---|---|---|---|
| `percent` | percent-encode a byte, percent-decode, the 8 percent-encode sets, percent-encode after encoding (UTF-8, no spaceAsPlus) | `percent_encode`, `percent_decode`, `in_set` | the spec's form-urlencoded note; the query-vs-fragment note; the set inclusion chain; decode∘encode = id exactly for sets containing `%` (only component and form-urlencoded), with a counterexample for the other six |
| `ipv4` | strictly split on `.`, IPv4 number parser, IPv4 parser, ends-in-a-number checker | `split_dots`, `ipv4_number`, `ipv4_parse`, `ends_in_a_number` | the spec's note that step 5 of the checker is equivalent to "0x/0X followed by hex digits" |

Not yet modeled: validation errors (only return values), IPv6, opaque/domain hosts, IDNA, the
basic URL parser state machine, and serializers.

Testing (beyond the proofs, which already cover all inputs): WPT `urltestdata.json`
(pinned, see `url/tests/data/PROVENANCE`) for the IPv4 host cases, plus differential tests
against the `url` and `percent-encoding` crates.

## Running

```bash
source ~/workspaces/verus-stack/env.zsh
./scripts/use-local-verus.sh        # point vstd at the Verus source that built `verus`
cargo verus verify -p vurl          # proofs
cargo test -p vurl                  # WPT + differential tests (no Verus needed)
python3 scripts/ratchet.py          # writes ratchet.json: verified / trusted counts
```
