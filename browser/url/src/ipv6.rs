//! WHATWG URL §3.5 the IPv6 parser, transcribed from url.bs at whatwg/url@4f461b81 (2026-11-19).
//!
//! The spec is a pointer-based algorithm with nested loops. Each loop is transcribed as one
//! recursive spec function whose arguments are that loop's variables, so the exec code below
//! can mirror it loop for loop. Validation errors are not modeled; only the return value is.
//! An address is 8 pieces; the spec's pieces are 16-bit, and `lemma`s below show they stay
//! below 0x10000.
use crate::ipv4::is_ascii_digit_exec;
use crate::percent::{hex_val, is_hex};
#[cfg(verus_keep_ghost)]
use crate::ipv4::is_ascii_digit;
#[cfg(verus_keep_ghost)]
use crate::percent::{hex_value, is_ascii_hex_digit};
use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------------------
// Spec
// ---------------------------------------------------------------------------------------

/// "Let value and length be 0. While length is less than 4 and c is an ASCII hex digit, set
/// value to value × 0x10 + c interpreted as a hexadecimal number, and increase pointer and
/// length by 1." (pointer = p + length). Returns (length, value).
pub open spec fn spec_hex_run(input: Seq<u8>, p: nat, length: nat, value: nat) -> (nat, nat)
    decreases 4 - length,
{
    if length < 4 && p + length < input.len() && is_ascii_hex_digit(input[(p + length) as int]) {
        spec_hex_run(input, p, length + 1, value * 16 + hex_value(input[(p + length) as int]))
    } else {
        (length, value)
    }
}

/// The IPv4-in-IPv6 loop ("While c is not the EOF code point: Let ipv4Piece be null ..."),
/// with its inner digit loop folded in: `piece` is the spec's ipv4Piece, None between numbers.
/// Returns (pieceIndex, address, numbersSeen) when c reaches EOF, or None for failure.
pub open spec fn spec_v4_in_v6(
    input: Seq<u8>,
    p: nat,
    pi: nat,
    addr: Seq<nat>,
    seen: nat,
    piece: Option<nat>,
) -> Option<(nat, Seq<nat>, nat)>
    decreases input.len() - p, (if piece is Some {
        1int
    } else {
        0int
    }),
{
    match piece {
        Some(x) => {
            if p < input.len() && is_ascii_digit(input[p as int]) {
                // "Otherwise, if ipv4Piece is 0, ... return failure. Otherwise, set ipv4Piece to
                // ipv4Piece × 10 + number. If ipv4Piece is greater than 255, ... return failure."
                if x == 0 {
                    None
                } else if x * 10 + (input[p as int] - 0x30) > 255 {
                    None
                } else {
                    spec_v4_in_v6(
                        input,
                        p + 1,
                        pi,
                        addr,
                        seen,
                        Some((x * 10 + (input[p as int] - 0x30)) as nat),
                    )
                }
            } else {
                // "Set address[pieceIndex] to address[pieceIndex] × 0x100 + ipv4Piece. Increase
                // numbersSeen by 1. If numbersSeen is 2 or 4, then increase pieceIndex by 1."
                let addr2 = addr.update(pi as int, addr[pi as int] * 256 + x);
                let seen2 = seen + 1;
                let pi2 = if seen2 == 2 || seen2 == 4 {
                    pi + 1
                } else {
                    pi
                };
                spec_v4_in_v6(input, p, pi2, addr2, seen2, None)
            }
        },
        None => {
            if p >= input.len() {
                Some((pi, addr, seen))
            } else if seen > 0 && !(input[p as int] == 0x2E && seen < 4) {
                // "If numbersSeen is greater than 0, then: If c is a U+002E (.) and numbersSeen is
                // less than 4, then increase pointer by 1. Otherwise, ... return failure."
                None
            } else {
                let q: nat = if seen > 0 {
                    p + 1
                } else {
                    p
                };
                if !(q < input.len() && is_ascii_digit(input[q as int])) {
                    // "If c is not an ASCII digit, ... return failure."
                    None
                } else {
                    // first digit: "If ipv4Piece is null, then set ipv4Piece to number."
                    spec_v4_in_v6(
                        input,
                        q + 1,
                        pi,
                        addr,
                        seen,
                        Some((input[q as int] - 0x30) as nat),
                    )
                }
            }
        },
    }
}

/// "While pieceIndex is not 0 and swaps is greater than 0, swap address[pieceIndex] with
/// address[compress + swaps − 1], and then decrease both pieceIndex and swaps by 1."
pub open spec fn spec_swap_loop(addr: Seq<nat>, i: int, swaps: int, compress: int) -> Seq<nat>
    decreases swaps,
{
    if i != 0 && swaps > 0 {
        let j = compress + swaps - 1;
        spec_swap_loop(addr.update(i, addr[j]).update(j, addr[i]), i - 1, swaps - 1, compress)
    } else {
        addr
    }
}

/// The steps after the main loop: undo compression, or fail if there are too few pieces.
pub open spec fn spec_ipv6_finish(pi: nat, compress: Option<nat>, addr: Seq<nat>) -> Option<
    Seq<nat>,
> {
    match compress {
        Some(c) => Some(spec_swap_loop(addr, 7, pi - c, c as int)),
        None => if pi != 8 {
            None
        } else {
            Some(addr)
        },
    }
}

/// The main loop ("While c is not the EOF code point").
pub open spec fn spec_ipv6_main(
    input: Seq<u8>,
    p: nat,
    pi: nat,
    compress: Option<nat>,
    addr: Seq<nat>,
) -> Option<Seq<nat>>
    decreases input.len() - p,
{
    if p >= input.len() {
        spec_ipv6_finish(pi, compress, addr)
    } else if pi == 8 {
        None
    } else if input[p as int] == 0x3A {
        // "If compress is non-null, ... return failure. Increase pointer and pieceIndex by 1,
        // set compress to pieceIndex, and then continue."
        if compress is Some {
            None
        } else {
            spec_ipv6_main(input, p + 1, pi + 1, Some(pi + 1), addr)
        }
    } else {
        let (length, value) = spec_hex_run(input, p, 0, 0);
        let q = p + length;
        if q < input.len() && input[q as int] == 0x2E {
            // "If length is 0, ... return failure. Decrease pointer by length. If pieceIndex is
            // greater than 6, ... return failure." then the IPv4 loop, then "If numbersSeen is
            // not 4, ... return failure. Break."
            if length == 0 {
                None
            } else if pi > 6 {
                None
            } else {
                match spec_v4_in_v6(input, p, pi, addr, 0, None) {
                    None => None,
                    Some(r) => if r.2 != 4 {
                        None
                    } else {
                        spec_ipv6_finish(r.0, compress, r.1)
                    },
                }
            }
        } else if q < input.len() && input[q as int] == 0x3A {
            // "Increase pointer by 1. If c is the EOF code point, ... return failure."
            if q + 1 >= input.len() {
                None
            } else {
                spec_ipv6_main(input, q + 1, pi + 1, compress, addr.update(pi as int, value))
            }
        } else if q < input.len() {
            // "Otherwise, if c is not the EOF code point, ... return failure."
            None
        } else {
            // "Set address[pieceIndex] to value. Increase pieceIndex by 1." then c is EOF.
            spec_ipv6_finish(pi + 1, compress, addr.update(pi as int, value))
        }
    }
}

pub open spec fn zero_address() -> Seq<nat> {
    Seq::new(8, |i: int| 0nat)
}

/// The IPv6 parser. Returns the 8 pieces, or None for failure.
pub open spec fn spec_ipv6_parse(input: Seq<u8>) -> Option<Seq<nat>> {
    if input.len() > 0 && input[0] == 0x3A {
        // "If remaining does not start with U+003A (:), ... return failure. Increase pointer by
        // 2. Increase pieceIndex by 1 and then set compress to pieceIndex."
        if !(input.len() > 1 && input[1] == 0x3A) {
            None
        } else {
            spec_ipv6_main(input, 2, 1, Some(1), zero_address())
        }
    } else {
        spec_ipv6_main(input, 0, 0, None, zero_address())
    }
}

// ---------------------------------------------------------------------------------------
// Exec
// ---------------------------------------------------------------------------------------

pub open spec fn view_nat(s: Seq<u32>) -> Seq<nat> {
    s.map_values(|x: u32| x as nat)
}

pub open spec fn opt_nat(o: Option<usize>) -> Option<nat> {
    match o {
        Some(c) => Some(c as nat),
        None => None,
    }
}

pub open spec fn opt_piece(o: Option<u32>) -> Option<nat> {
    match o {
        Some(c) => Some(c as nat),
        None => None,
    }
}

proof fn lemma_set_view(old: Seq<u32>, new: Seq<u32>, i: int, x: u32)
    requires
        0 <= i < old.len(),
        new == old.update(i, x),
    ensures
        view_nat(new) == view_nat(old).update(i, x as nat),
{
    assert(view_nat(new) =~= view_nat(old).update(i, x as nat));
}

/// The IPv4-in-IPv6 loop. Mutates `addr`; returns (pieceIndex, numbersSeen).
fn v4_in_v6(input: &[u8], p0: usize, pi0: usize, addr: &mut Vec<u32>) -> (res: Option<(usize, usize)>)
    requires
        p0 <= input@.len(),
        pi0 <= 6,
        old(addr)@.len() == 8,
        forall|k: int| 0 <= k < 8 ==> old(addr)@[k] <= 0xFFFF,
        forall|k: int| pi0 <= k < 8 ==> old(addr)@[k] == 0,
    ensures
        final(addr)@.len() == 8,
        forall|k: int| 0 <= k < 8 ==> final(addr)@[k] <= 0xFFFF,
        spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None) is None ==> res is None,
        spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None) matches Some(r) ==> (res == Some((r.0 as usize, r.2 as usize))),
        spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None) matches Some(r) ==> view_nat(final(addr)@) == r.1,
        spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None) matches Some(r) ==> pi0 <= r.0 <= 8 && r.2 <= 4,
{
    let n = input.len();
    let mut p = p0;
    let mut pi = pi0;
    let mut seen: usize = 0;
    let mut piece: Option<u32> = None;
    let ghost goal = spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(addr@), 0, None);
    proof {
        assert(goal == spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None));
    }
    loop
        invariant
            n == input@.len(),
            p <= n,
            pi0 <= 6,
            seen <= 4,
            pi == pi0 + (if seen >= 4 {
                2int
            } else if seen >= 2 {
                1int
            } else {
                0int
            }),
            piece is Some ==> seen < 4,
            piece matches Some(x) ==> x <= 255,
            addr@.len() == 8,
            forall|k: int| 0 <= k < 8 ==> addr@[k] <= 0xFFFF,
            forall|k: int| pi < k < 8 ==> addr@[k] == 0,
            seen < 4 && seen % 2 == 0 ==> addr@[pi as int] == 0,
            seen < 4 && seen % 2 == 1 ==> addr@[pi as int] <= 255,
            goal == spec_v4_in_v6(input@, p0 as nat, pi0 as nat, view_nat(old(addr)@), 0, None),
            goal == spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, opt_piece(piece)),
        decreases n - p, (if piece is Some {
            1int
        } else {
            0int
        }),
    {
        match piece {
            Some(x) => {
                if p < n && is_ascii_digit_exec(input[p]) {
                    let number = (input[p] - 0x30) as u32;
                    if x == 0 {
                        proof {
                            assert(opt_piece(piece) == Some(x as nat));
                            assert(is_ascii_digit(input@[p as int]));
                            assert(spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, Some(x as nat)) is None);
                            assert(goal is None);
                        }
                    return None;
                    }
                    let y = x * 10 + number;
                    if y > 255 {
                        proof {
                            assert(opt_piece(piece) == Some(x as nat));
                            assert(is_ascii_digit(input@[p as int]));
                            assert(spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, Some(x as nat)) is None);
                            assert(goal is None);
                        }
                    return None;
                    }
                    piece = Some(y);
                    p += 1;
                } else {
                    let ghost old_addr = addr@;
                    let w = addr[pi] * 256 + x;
                    addr.set(pi, w);
                    proof {
                        lemma_set_view(old_addr, addr@, pi as int, w);
                    }
                    seen += 1;
                    if seen == 2 || seen == 4 {
                        pi += 1;
                    }
                    piece = None;
                }
            },
            None => {
                if p >= n {
                    proof {
                        assert(opt_piece(piece) is None);
                        assert(spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, None) == Some((pi as nat, view_nat(addr@), seen as nat)));
                        assert(goal == Some((pi as nat, view_nat(addr@), seen as nat)));
                    }
                    return Some((pi, seen));
                }
                if seen > 0 && !(input[p] == 0x2E && seen < 4) {
                    proof {
                        assert(opt_piece(piece) is None);
                        assert(spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, None) is None);
                        assert(goal is None);
                    }
                    proof { assert(goal is None); }
                    return None;
                }
                let q = if seen > 0 {
                    p + 1
                } else {
                    p
                };
                if !(q < n && is_ascii_digit_exec(input[q])) {
                    proof {
                        assert(opt_piece(piece) is None);
                        assert(spec_v4_in_v6(input@, p as nat, pi as nat, view_nat(addr@), seen as nat, None) is None);
                        assert(goal is None);
                    }
                    return None;
                }
                piece = Some((input[q] - 0x30) as u32);
                p = q + 1;
            },
        }
    }
}

fn ipv6_finish(pi: usize, compress: Option<usize>, addr: Vec<u32>) -> (res: Option<Vec<u16>>)
    requires
        pi <= 8,
        addr@.len() == 8,
        forall|k: int| 0 <= k < 8 ==> addr@[k] <= 0xFFFF,
        compress matches Some(c) ==> c <= pi,
    ensures
        match spec_ipv6_finish(pi as nat, opt_nat(compress), view_nat(addr@)) {
            None => res is None,
            Some(a) => res matches Some(v) && v@.len() == 8 && forall|k: int|
                0 <= k < 8 ==> v@[k] as nat == a[k],
        },
{
    let mut addr = addr;
    let ghost goal = spec_ipv6_finish(pi as nat, opt_nat(compress), view_nat(addr@));
    match compress {
        Some(c) => {
            let mut swaps = pi - c;
            let mut i: usize = 7;
            while i != 0 && swaps > 0
                invariant
                    i <= 7,
                    c + swaps <= 8,
                    addr@.len() == 8,
                    forall|k: int| 0 <= k < 8 ==> addr@[k] <= 0xFFFF,
                    goal == Some(spec_swap_loop(view_nat(addr@), i as int, swaps as int, c as int)),
                decreases swaps,
            {
                let j = c + swaps - 1;
                let ghost a0 = addr@;
                let t = addr[i];
                let u = addr[j];
                addr.set(i, u);
                proof {
                    lemma_set_view(a0, addr@, i as int, u);
                }
                let ghost a1 = addr@;
                addr.set(j, t);
                proof {
                    lemma_set_view(a1, addr@, j as int, t);
                }
                i -= 1;
                swaps -= 1;
            }
        },
        None => {
            if pi != 8 {
                return None;
            }
        },
    }
    let mut out: Vec<u16> = Vec::new();
    let mut k: usize = 0;
    while k < 8
        invariant
            k <= 8,
            addr@.len() == 8,
            forall|m: int| 0 <= m < 8 ==> addr@[m] <= 0xFFFF,
            goal == Some(view_nat(addr@)),
            out@.len() == k,
            forall|m: int| 0 <= m < k ==> out@[m] as nat == addr@[m] as nat,
        decreases 8 - k,
    {
        out.push(addr[k] as u16);
        k += 1;
    }
    Some(out)
}

/// The IPv6 parser.
pub fn ipv6_parse(input: &[u8]) -> (res: Option<Vec<u16>>)
    ensures
        match spec_ipv6_parse(input@) {
            None => res is None,
            Some(a) => res matches Some(v) && v@.len() == 8 && forall|k: int|
                0 <= k < 8 ==> v@[k] as nat == a[k],
        },
{
    let n = input.len();
    let mut addr: Vec<u32> = Vec::new();
    while addr.len() < 8
        invariant
            addr@.len() <= 8,
            forall|k: int| 0 <= k < addr@.len() ==> addr@[k] == 0,
        decreases 8 - addr@.len(),
    {
        addr.push(0);
    }
    proof {
        assert(view_nat(addr@) =~= zero_address());
    }
    let mut p: usize = 0;
    let mut pi: usize = 0;
    let mut compress: Option<usize> = None;
    if n > 0 && input[0] == 0x3A {
        if !(n > 1 && input[1] == 0x3A) {
            return None;
        }
        p = 2;
        pi = 1;
        compress = Some(1);
    }
    let ghost goal = spec_ipv6_parse(input@);
    while p < n
        invariant
            n == input@.len(),
            p <= n,
            pi <= 8,
            addr@.len() == 8,
            forall|k: int| 0 <= k < 8 ==> addr@[k] <= 0xFFFF,
            forall|k: int| pi <= k < 8 ==> addr@[k] == 0,
            compress matches Some(c) ==> c <= pi,
            goal == spec_ipv6_parse(input@),
            goal == spec_ipv6_main(input@, p as nat, pi as nat, opt_nat(compress), view_nat(addr@)),
        decreases n - p,
    {
        if pi == 8 {
            return None;
        }
        if input[p] == 0x3A {
            if compress.is_some() {
                return None;
            }
            p += 1;
            pi += 1;
            compress = Some(pi);
            continue;
        }
        let mut value: u32 = 0;
        let mut length: usize = 0;
        while length < 4 && p + length < n && is_hex(input[p + length])
            invariant
                n == input@.len(),
                p < n,
                length <= 4,
                p + length <= n,
                length == 0 ==> value == 0,
                length == 1 ==> value < 16,
                length == 2 ==> value < 256,
                length == 3 ==> value < 4096,
                value < 65536,
                spec_hex_run(input@, p as nat, length as nat, value as nat) == spec_hex_run(
                    input@,
                    p as nat,
                    0,
                    0,
                ),
            decreases 4 - length,
        {
            value = value * 16 + hex_val(input[p + length]) as u32;
            length += 1;
        }
        let q = p + length;
        if q < n && input[q] == 0x2E {
            if length == 0 {
                return None;
            }
            if pi > 6 {
                return None;
            }
            let ghost a_before = view_nat(addr@);
            proof {
                assert(spec_hex_run(input@, p as nat, 0, 0) == (length as nat, value as nat));
                assert(goal == match spec_v4_in_v6(input@, p as nat, pi as nat, a_before, 0, None) {
                    None => None,
                    Some(r) => if r.2 != 4 {
                        None
                    } else {
                        spec_ipv6_finish(r.0, opt_nat(compress), r.1)
                    },
                });
            }
            match v4_in_v6(input, p, pi, &mut addr) {
                None => {
                    return None;
                },
                Some((pi2, seen)) => {
                    if seen != 4 {
                        return None;
                    }
                    return ipv6_finish(pi2, compress, addr);
                },
            }
        } else if q < n && input[q] == 0x3A {
            if q + 1 >= n {
                return None;
            }
            let ghost old_addr = addr@;
            addr.set(pi, value);
            proof {
                lemma_set_view(old_addr, addr@, pi as int, value);
            }
            pi += 1;
            p = q + 1;
        } else if q < n {
            return None;
        } else {
            let ghost old_addr = addr@;
            addr.set(pi, value);
            proof {
                lemma_set_view(old_addr, addr@, pi as int, value);
            }
            pi += 1;
            p = q;
        }
    }
    ipv6_finish(pi, compress, addr)
}

// ---------------------------------------------------------------------------------------
// IPv6 serializer (spec)
// ---------------------------------------------------------------------------------------

/// "find the IPv6 address compressed piece index": the loop over pieces, with its four variables.
pub open spec fn spec_compress_loop(
    addr: Seq<nat>,
    i: nat,
    longest_index: Option<nat>,
    longest_size: nat,
    found_index: Option<nat>,
    found_size: nat,
) -> Option<nat>
    decreases 8 - i,
{
    if i >= 8 {
        // "If foundSize is greater than longestSize, then return foundIndex. Return longestIndex."
        if found_size > longest_size {
            found_index
        } else {
            longest_index
        }
    } else if addr[i as int] != 0 {
        // "If foundSize is greater than longestSize, then set longestIndex to foundIndex and
        // longestSize to foundSize. Set foundIndex to null. Set foundSize to 0."
        if found_size > longest_size {
            spec_compress_loop(addr, i + 1, found_index, found_size, None, 0)
        } else {
            spec_compress_loop(addr, i + 1, longest_index, longest_size, None, 0)
        }
    } else {
        // "If foundIndex is null, then set foundIndex to pieceIndex. Increment foundSize by 1."
        let fi = if found_index is None {
            Some(i)
        } else {
            found_index
        };
        spec_compress_loop(addr, i + 1, longest_index, longest_size, fi, found_size + 1)
    }
}

/// "Let longestIndex be null. Let longestSize be 1. Let foundIndex be null. Let foundSize be 0."
pub open spec fn spec_compressed_index(addr: Seq<nat>) -> Option<nat> {
    spec_compress_loop(addr, 0, None, 1, None, 0)
}

pub open spec fn hex_lower_digit(n: nat) -> u8 {
    if n < 10 {
        (0x30 + n) as u8
    } else {
        (0x61 + n - 10) as u8
    }
}

/// n "represented as the shortest possible lowercase hexadecimal number".
pub open spec fn spec_hex_lower(n: nat) -> Seq<u8>
    decreases n,
{
    if n < 16 {
        seq![hex_lower_digit(n)]
    } else {
        spec_hex_lower(n / 16).push(hex_lower_digit(n % 16))
    }
}

/// The serializer's loop over pieces.
pub open spec fn spec_serialize_loop(
    addr: Seq<nat>,
    i: nat,
    compress: Option<nat>,
    ignore0: bool,
    out: Seq<u8>,
) -> Seq<u8>
    decreases 8 - i,
{
    if i >= 8 {
        out
    } else if ignore0 && addr[i as int] == 0 {
        // "If ignore0 is true and address[pieceIndex] is 0, then continue."
        spec_serialize_loop(addr, i + 1, compress, ignore0, out)
    } else if compress == Some(i) {
        // "Let separator be "::" if pieceIndex is 0; otherwise U+003A (:). Append separator to
        // output. Set ignore0 to true and continue."
        let sep = if i == 0 {
            seq![0x3Au8, 0x3Au8]
        } else {
            seq![0x3Au8]
        };
        spec_serialize_loop(addr, i + 1, compress, true, out + sep)
    } else {
        // "Otherwise, if ignore0 is true, set ignore0 to false." then append the piece and, if
        // pieceIndex is not 7, U+003A (:).
        let tail = if i != 7 {
            seq![0x3Au8]
        } else {
            Seq::<u8>::empty()
        };
        spec_serialize_loop(addr, i + 1, compress, false, out + spec_hex_lower(addr[i as int]) + tail)
    }
}

/// The IPv6 serializer (without the surrounding brackets the host serializer adds).
pub open spec fn spec_ipv6_serialize(addr: Seq<nat>) -> Seq<u8> {
    spec_serialize_loop(addr, 0, spec_compressed_index(addr), false, Seq::<u8>::empty())
}

/// The hex form has no leading zero, i.e. it is the shortest one.
pub proof fn lemma_hex_lower_shortest(n: nat)
    ensures
        spec_hex_lower(n).len() >= 1,
        n > 0 ==> spec_hex_lower(n)[0] != 0x30,
    decreases n,
{
    if n >= 16 {
        lemma_hex_lower_shortest(n / 16);
    }
}

// ---------------------------------------------------------------------------------------
// IPv6 serializer (exec)
// ---------------------------------------------------------------------------------------

pub open spec fn view_u16(s: Seq<u16>) -> Seq<nat> {
    s.map_values(|x: u16| x as nat)
}

fn hex_lower_digit_exec(n: u16) -> (r: u8)
    requires
        n < 16,
    ensures
        r == hex_lower_digit(n as nat),
{
    if n < 10 {
        0x30 + n as u8
    } else {
        0x61 + (n as u8) - 10
    }
}

fn push_hex_lower(n: u16, out: &mut Vec<u8>)
    ensures
        final(out)@ == old(out)@ + spec_hex_lower(n as nat),
    decreases n,
{
    if n < 16 {
        out.push(hex_lower_digit_exec(n));
        proof {
            assert(final(out)@ =~= old(out)@ + spec_hex_lower(n as nat));
        }
    } else {
        push_hex_lower(n / 16, out);
        out.push(hex_lower_digit_exec(n % 16));
        proof {
            assert(final(out)@ =~= old(out)@ + spec_hex_lower(n as nat));
        }
    }
}

pub fn compressed_index(addr: &[u16]) -> (r: Option<usize>)
    requires
        addr@.len() == 8,
    ensures
        opt_nat(r) == spec_compressed_index(view_u16(addr@)),
{
    let ghost a = view_u16(addr@);
    let mut longest_index: Option<usize> = None;
    let mut longest_size: usize = 1;
    let mut found_index: Option<usize> = None;
    let mut found_size: usize = 0;
    let mut i: usize = 0;
    while i < 8
        invariant
            i <= 8,
            addr@.len() == 8,
            a == view_u16(addr@),
            longest_size <= 8,
            found_size <= i,
            spec_compressed_index(a) == spec_compress_loop(
                a,
                i as nat,
                opt_nat(longest_index),
                longest_size as nat,
                opt_nat(found_index),
                found_size as nat,
            ),
        decreases 8 - i,
    {
        if addr[i] != 0 {
            if found_size > longest_size {
                longest_index = found_index;
                longest_size = found_size;
            }
            found_index = None;
            found_size = 0;
        } else {
            if found_index.is_none() {
                found_index = Some(i);
            }
            found_size += 1;
        }
        i += 1;
    }
    if found_size > longest_size {
        found_index
    } else {
        longest_index
    }
}

/// The IPv6 serializer.
pub fn ipv6_serialize(addr: &[u16]) -> (out: Vec<u8>)
    requires
        addr@.len() == 8,
    ensures
        out@ == spec_ipv6_serialize(view_u16(addr@)),
{
    let ghost a = view_u16(addr@);
    let compress = compressed_index(addr);
    let mut out: Vec<u8> = Vec::new();
    let mut ignore0 = false;
    let mut i: usize = 0;
    proof {
        assert(out@ =~= Seq::<u8>::empty());
    }
    while i < 8
        invariant
            i <= 8,
            addr@.len() == 8,
            a == view_u16(addr@),
            spec_ipv6_serialize(a) == spec_serialize_loop(a, i as nat, opt_nat(compress), ignore0, out@),
        decreases 8 - i,
    {
        if ignore0 && addr[i] == 0 {
            i += 1;
            continue;
        }
        ignore0 = false;
        if compress == Some(i) {
            let ghost before = out@;
            if i == 0 {
                out.push(0x3A);
                out.push(0x3A);
                proof {
                    assert(out@ =~= before + seq![0x3Au8, 0x3Au8]);
                }
            } else {
                out.push(0x3A);
                proof {
                    assert(out@ =~= before + seq![0x3Au8]);
                }
            }
            ignore0 = true;
            i += 1;
            continue;
        }
        let ghost before = out@;
        push_hex_lower(addr[i], &mut out);
        let ghost mid = out@;
        if i != 7 {
            out.push(0x3A);
            proof {
                assert(out@ =~= before + spec_hex_lower(a[i as int]) + seq![0x3Au8]);
            }
        } else {
            proof {
                assert(out@ =~= before + spec_hex_lower(a[i as int]) + Seq::<u8>::empty());
            }
        }
        i += 1;
    }
    out
}

} // verus!
