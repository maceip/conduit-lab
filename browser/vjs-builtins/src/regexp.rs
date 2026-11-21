//! ECMA-262 §22.2 `RegExp` Regular Expression Objects (Warblre-style):
//! formally verified pattern parser + AST and defunctionalized continuation-backtracking
//! matcher (`exec_match` == `spec_match`, `exec_search` == `spec_search`) with machine-checked
//! termination (`decreases`), bounds validity invariants, and the §22.2.2.5.1 `RepeatMatcher`
//! empty-match progress guard preventing zero-width repetition loops.
use vstd::prelude::*;

verus! {

// =======================================================================================
// 1. RegExp Flags, AST (`RegexAst` & `SpecRegexAst`), and Match Result Types
// =======================================================================================

/// RegExp evaluation flags (`i`, `m`, `s`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegexFlags {
    pub ignore_case: bool,
    pub multiline: bool,
    pub dot_all: bool,
}

/// Spec-level regular expression AST (§22.2.1).
pub enum SpecRegexAst {
    Empty,
    Char(u16),
    Dot,
    CharClass { negated: bool, ranges: Seq<(u16, u16)> },
    Digit { negated: bool },
    Word { negated: bool },
    Space { negated: bool },
    AnchorStart,
    AnchorEnd,
    WordBoundary { negated: bool },
    Seq(Box<SpecRegexAst>, Box<SpecRegexAst>),
    Alt(Box<SpecRegexAst>, Box<SpecRegexAst>),
    Repeat { sub: Box<SpecRegexAst>, min: u32, max: Option<u32>, greedy: bool },
    Group { index: u32, sub: Box<SpecRegexAst> },
}

/// Exec-level regular expression AST (§22.2.1).
#[derive(PartialEq, Eq, Debug)]
pub enum RegexAst {
    Empty,
    Char(u16),
    Dot,
    CharClass { negated: bool, ranges: Vec<(u16, u16)> },
    Digit { negated: bool },
    Word { negated: bool },
    Space { negated: bool },
    AnchorStart,
    AnchorEnd,
    WordBoundary { negated: bool },
    Seq(Box<RegexAst>, Box<RegexAst>),
    Alt(Box<RegexAst>, Box<RegexAst>),
    Repeat { sub: Box<RegexAst>, min: u32, max: Option<u32>, greedy: bool },
    Group { index: u32, sub: Box<RegexAst> },
}

/// View mapping `RegexAst` to `SpecRegexAst`.
pub open spec fn spec_regex_view(ast: &RegexAst) -> SpecRegexAst
    decreases ast,
{
    match ast {
        RegexAst::Empty => SpecRegexAst::Empty,
        RegexAst::Char(c) => SpecRegexAst::Char(*c),
        RegexAst::Dot => SpecRegexAst::Dot,
        RegexAst::CharClass { negated, ranges } => SpecRegexAst::CharClass {
            negated: *negated,
            ranges: ranges@,
        },
        RegexAst::Digit { negated } => SpecRegexAst::Digit { negated: *negated },
        RegexAst::Word { negated } => SpecRegexAst::Word { negated: *negated },
        RegexAst::Space { negated } => SpecRegexAst::Space { negated: *negated },
        RegexAst::AnchorStart => SpecRegexAst::AnchorStart,
        RegexAst::AnchorEnd => SpecRegexAst::AnchorEnd,
        RegexAst::WordBoundary { negated } => SpecRegexAst::WordBoundary { negated: *negated },
        RegexAst::Seq(a, b) => SpecRegexAst::Seq(
            Box::new(spec_regex_view(&**a)),
            Box::new(spec_regex_view(&**b)),
        ),
        RegexAst::Alt(a, b) => SpecRegexAst::Alt(
            Box::new(spec_regex_view(&**a)),
            Box::new(spec_regex_view(&**b)),
        ),
        RegexAst::Repeat { sub, min, max, greedy } => SpecRegexAst::Repeat {
            sub: Box::new(spec_regex_view(&**sub)),
            min: *min,
            max: *max,
            greedy: *greedy,
        },
        RegexAst::Group { index, sub } => SpecRegexAst::Group {
            index: *index,
            sub: Box::new(spec_regex_view(&**sub)),
        },
    }
}

impl View for RegexAst {
    type V = SpecRegexAst;

    open spec fn view(&self) -> SpecRegexAst {
        spec_regex_view(self)
    }
}

/// Node count of `SpecRegexAst` for verified recursive helpers.
pub open spec fn spec_regex_size(ast: SpecRegexAst) -> nat
    decreases ast,
{
    match ast {
        SpecRegexAst::Seq(a, b) | SpecRegexAst::Alt(a, b) => {
            1 + spec_regex_size(*a) + spec_regex_size(*b)
        },
        SpecRegexAst::Repeat { sub, .. } | SpecRegexAst::Group { sub, .. } => {
            1 + spec_regex_size(*sub)
        },
        _ => 1,
    }
}

/// Verified clone of `(u16, u16)` range slice.
fn clone_ranges(ranges: &[(u16, u16)]) -> (out: Vec<(u16, u16)>)
    ensures
        out@ == ranges@,
{
    let n = ranges.len();
    let mut out: Vec<(u16, u16)> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == ranges@.len(),
            out@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> out@[k] == ranges@[k],
        decreases n - i,
    {
        out.push(ranges[i]);
        i += 1;
    }
    proof {
        assert(out@ =~= ranges@);
    }
    out
}

/// Verified clone of `RegexAst` preserving `View`.
pub fn clone_regex_ast(ast: &RegexAst) -> (out: RegexAst)
    ensures
        out@ == ast@,
    decreases spec_regex_size(ast@),
{
    match ast {
        RegexAst::Empty => RegexAst::Empty,
        RegexAst::Char(c) => RegexAst::Char(*c),
        RegexAst::Dot => RegexAst::Dot,
        RegexAst::CharClass { negated, ranges } => RegexAst::CharClass {
            negated: *negated,
            ranges: clone_ranges(ranges.as_slice()),
        },
        RegexAst::Digit { negated } => RegexAst::Digit { negated: *negated },
        RegexAst::Word { negated } => RegexAst::Word { negated: *negated },
        RegexAst::Space { negated } => RegexAst::Space { negated: *negated },
        RegexAst::AnchorStart => RegexAst::AnchorStart,
        RegexAst::AnchorEnd => RegexAst::AnchorEnd,
        RegexAst::WordBoundary { negated } => RegexAst::WordBoundary { negated: *negated },
        RegexAst::Seq(a, b) => RegexAst::Seq(
            Box::new(clone_regex_ast(&**a)),
            Box::new(clone_regex_ast(&**b)),
        ),
        RegexAst::Alt(a, b) => RegexAst::Alt(
            Box::new(clone_regex_ast(&**a)),
            Box::new(clone_regex_ast(&**b)),
        ),
        RegexAst::Repeat { sub, min, max, greedy } => RegexAst::Repeat {
            sub: Box::new(clone_regex_ast(&**sub)),
            min: *min,
            max: *max,
            greedy: *greedy,
        },
        RegexAst::Group { index, sub } => RegexAst::Group {
            index: *index,
            sub: Box::new(clone_regex_ast(&**sub)),
        },
    }
}

/// Spec match outcome.
pub enum SpecMatchOutcome {
    Matched {
        start_pos: nat,
        end_pos: nat,
        captures: Seq<Option<(nat, nat)>>,
    },
    NoMatch,
    StepLimitExceeded,
}

/// Exec match outcome.
#[derive(PartialEq, Eq, Debug)]
pub enum MatchOutcome {
    Matched {
        start_pos: usize,
        end_pos: usize,
        captures: Vec<Option<(usize, usize)>>,
    },
    NoMatch,
    StepLimitExceeded,
}

pub open spec fn spec_captures_view(caps: Seq<Option<(usize, usize)>>) -> Seq<Option<(nat, nat)>> {
    Seq::new(
        caps.len(),
        |i: int|
            match caps[i] {
                Some((s, e)) => Some((s as nat, e as nat)),
                None => None,
            },
    )
}

impl View for MatchOutcome {
    type V = SpecMatchOutcome;

    open spec fn view(&self) -> SpecMatchOutcome {
        match self {
            MatchOutcome::Matched { start_pos, end_pos, captures } => SpecMatchOutcome::Matched {
                start_pos: *start_pos as nat,
                end_pos: *end_pos as nat,
                captures: spec_captures_view(captures@),
            },
            MatchOutcome::NoMatch => SpecMatchOutcome::NoMatch,
            MatchOutcome::StepLimitExceeded => SpecMatchOutcome::StepLimitExceeded,
        }
    }
}

// =======================================================================================
// 2. Character Predicates (§22.2.2) & Capture Reset Semantics (§22.2.2.5.1)
// =======================================================================================

/// ECMA-262 §12.3 `LineTerminator` (`\n`, `\r`, `\u2028`, `\u2029`).
pub open spec fn spec_is_line_terminator(c: u16) -> bool {
    c == 0x000A || c == 0x000D || c == 0x2028 || c == 0x2029
}

/// ECMA-262 `\d` (`0-9`).
pub open spec fn spec_is_digit_char(c: u16) -> bool {
    0x0030 <= c && c <= 0x0039
}

/// ECMA-262 `\w` (`A-Z`, `a-z`, `0-9`, `_`).
pub open spec fn spec_is_word_char(c: u16) -> bool {
    (0x0041 <= c && c <= 0x005A)
        || (0x0061 <= c && c <= 0x007A)
        || (0x0030 <= c && c <= 0x0039)
        || c == 0x005F
}

/// ECMA-262 `\s` (`WhiteSpace` U `LineTerminator`).
pub open spec fn spec_is_space_char(c: u16) -> bool {
    c == 0x0009
        || c == 0x000B
        || c == 0x000C
        || c == 0x0020
        || c == 0x00A0
        || c == 0xFEFF
        || c == 0x1680
        || (0x2000 <= c && c <= 0x200A)
        || c == 0x202F
        || c == 0x205F
        || c == 0x3000
        || spec_is_line_terminator(c)
}

/// Canonicalize `c` for `Canonicalize ( ch )` under `ignoreCase` (§22.2.2.8.2).
pub open spec fn spec_canonicalize_char(c: u16, ignore_case: bool) -> u16 {
    if ignore_case && 0x0061 <= c && c <= 0x007A {
        (c - 32) as u16
    } else {
        c
    }
}

/// Check whether `c` matches `[lo, hi]` under ECMA-262 §22.2.2.8.1 `CharacterSetMatcher`.
pub open spec fn spec_in_single_range(c: u16, lo: u16, hi: u16, ignore_case: bool) -> bool {
    (lo <= c && c <= hi)
        || (ignore_case
            && 0x0041 <= c
            && c <= 0x005A
            && lo <= (c + 32) as u16
            && (c + 32) as u16 <= hi)
        || (ignore_case
            && 0x0061 <= c
            && c <= 0x007A
            && lo <= (c - 32) as u16
            && (c - 32) as u16 <= hi)
}

/// Exact ECMA-262 §22.2.2.8.1 preimage theorem: `spec_in_single_range(c, lo, hi, ignore_case)`
/// holds iff there exists some code unit `k` in `[lo, hi]` with `Canonicalize(k) == Canonicalize(c)`.
pub proof fn lemma_char_range_matches_canonicalize_preimage(
    c: u16,
    lo: u16,
    hi: u16,
    ignore_case: bool,
)
    ensures
        spec_in_single_range(c, lo, hi, ignore_case)
            <==> (exists|k: u16|
                lo <= k
                    && k <= hi
                    && #[trigger] spec_canonicalize_char(k, ignore_case)
                        == spec_canonicalize_char(c, ignore_case)),
{
    if spec_in_single_range(c, lo, hi, ignore_case) {
        if lo <= c && c <= hi {
            assert(spec_canonicalize_char(c, ignore_case) == spec_canonicalize_char(c, ignore_case));
        } else if ignore_case && 0x0041 <= c && c <= 0x005A {
            let k: u16 = (c + 32) as u16;
            assert(spec_canonicalize_char(k, ignore_case) == spec_canonicalize_char(c, ignore_case));
        } else {
            let k: u16 = (c - 32) as u16;
            assert(spec_canonicalize_char(k, ignore_case) == spec_canonicalize_char(c, ignore_case));
        }
    }
}

/// Check whether `c` falls in any range `(lo, hi)` of `ranges` under `ignore_case`.
pub open spec fn spec_in_char_ranges(
    c: u16,
    ranges: Seq<(u16, u16)>,
    ignore_case: bool,
) -> bool
    decreases ranges.len(),
{
    if ranges.len() == 0 {
        false
    } else {
        let (lo, hi) = ranges[0];
        if spec_in_single_range(c, lo, hi, ignore_case) {
            true
        } else {
            spec_in_char_ranges(c, ranges.subrange(1, ranges.len() as int), ignore_case)
        }
    }
}

/// Exact `u16` range list for `\d` inside `[...]` (§22.2.2.9.1).
pub open spec fn spec_class_ranges_d() -> Seq<(u16, u16)> {
    seq![(0x0030u16, 0x0039u16)]
}

/// Exact `u16` complement range list for `\D` inside `[...]` (§22.2.2.9.2).
pub open spec fn spec_class_ranges_not_d() -> Seq<(u16, u16)> {
    seq![(0x0000u16, 0x002Fu16), (0x003Au16, 0xFFFFu16)]
}

/// Exact `u16` range list for `\w` inside `[...]` (§22.2.2.9.3).
pub open spec fn spec_class_ranges_w() -> Seq<(u16, u16)> {
    seq![
        (0x0030u16, 0x0039u16),
        (0x0041u16, 0x005Au16),
        (0x005Fu16, 0x005Fu16),
        (0x0061u16, 0x007Au16),
    ]
}

/// Exact `u16` complement range list for `\W` inside `[...]` (§22.2.2.9.4).
pub open spec fn spec_class_ranges_not_w() -> Seq<(u16, u16)> {
    seq![
        (0x0000u16, 0x002Fu16),
        (0x003Au16, 0x0040u16),
        (0x005Bu16, 0x005Eu16),
        (0x0060u16, 0x0060u16),
        (0x007Bu16, 0xFFFFu16),
    ]
}

/// Exact `u16` range list for `\s` (`WhiteSpace` U `LineTerminator`, 10 ranges, §22.2.2.9.5).
pub open spec fn spec_class_ranges_s() -> Seq<(u16, u16)> {
    seq![
        (0x0009u16, 0x000Du16),
        (0x0020u16, 0x0020u16),
        (0x00A0u16, 0x00A0u16),
        (0x1680u16, 0x1680u16),
        (0x2000u16, 0x200Au16),
        (0x2028u16, 0x2029u16),
        (0x202Fu16, 0x202Fu16),
        (0x205Fu16, 0x205Fu16),
        (0x3000u16, 0x3000u16),
        (0xFEFFu16, 0xFEFFu16),
    ]
}

/// Exact `u16` complement range list for `\S` inside `[...]` (11 ranges, §22.2.2.9.6).
pub open spec fn spec_class_ranges_not_s() -> Seq<(u16, u16)> {
    seq![
        (0x0000u16, 0x0008u16),
        (0x000Eu16, 0x001Fu16),
        (0x0021u16, 0x009Fu16),
        (0x00A1u16, 0x167Fu16),
        (0x1681u16, 0x1FFFu16),
        (0x200Bu16, 0x2027u16),
        (0x202Au16, 0x202Eu16),
        (0x2030u16, 0x205Eu16),
        (0x2060u16, 0x2FFFu16),
        (0x3001u16, 0xFEFEu16),
        (0xFF00u16, 0xFFFFu16),
    ]
}

/// Witness predicate: `ranges[idx]` matches `c` under `ignore_case`.
pub open spec fn spec_range_at_matches(
    c: u16,
    ranges: Seq<(u16, u16)>,
    idx: int,
    ignore_case: bool,
) -> bool {
    0 <= idx < ranges.len()
        && spec_in_single_range(c, ranges[idx].0, ranges[idx].1, ignore_case)
}

/// Inductive characterization of `spec_in_char_ranges` via index witness.
pub proof fn lemma_in_char_ranges_iff_exists_index(
    c: u16,
    ranges: Seq<(u16, u16)>,
    ignore_case: bool,
)
    ensures
        spec_in_char_ranges(c, ranges, ignore_case)
            <==> (exists|idx: int| #[trigger] spec_range_at_matches(c, ranges, idx, ignore_case)),
    decreases ranges.len(),
{
    if ranges.len() == 0 {
        assert forall|idx: int|
            !#[trigger] spec_range_at_matches(c, ranges, idx, ignore_case) by {};
    } else {
        let (lo, hi) = ranges[0];
        if spec_in_single_range(c, lo, hi, ignore_case) {
            assert(spec_range_at_matches(c, ranges, 0, ignore_case));
        } else {
            let tail = ranges.subrange(1, ranges.len() as int);
            lemma_in_char_ranges_iff_exists_index(c, tail, ignore_case);
            if spec_in_char_ranges(c, tail, ignore_case) {
                let j = choose|j: int| #[trigger] spec_range_at_matches(c, tail, j, ignore_case);
                assert(tail[j] == ranges[j + 1]);
                assert(spec_range_at_matches(c, ranges, j + 1, ignore_case));
            } else {
                assert forall|idx: int|
                    !#[trigger] spec_range_at_matches(c, ranges, idx, ignore_case) by {
                    if idx == 0 {
                    } else if 1 <= idx < ranges.len() {
                        assert(tail[idx - 1] == ranges[idx]);
                        assert(!spec_range_at_matches(c, tail, idx - 1, ignore_case));
                    }
                };
            }
        }
    }
}

/// Pointwise equivalence theorem (§22.2.2.9.1–§22.2.2.9.6): inside `[...]`, the `u16` range
/// expansions of `\d`, `\D`, `\w`, `\W`, `\s`, `\S` agree pointwise with standalone
/// `spec_is_digit_char`, `!spec_is_digit_char`, `spec_is_word_char`, `!spec_is_word_char`,
/// `spec_is_space_char`, and `!spec_is_space_char` for every code unit `c: u16` and every
/// `ignore_case: bool` setting.
#[verifier::spinoff_prover]
pub proof fn lemma_class_escape_ranges_pointwise(c: u16, ignore_case: bool)
    ensures
        spec_in_char_ranges(c, spec_class_ranges_d(), ignore_case) <==> spec_is_digit_char(c),
        spec_in_char_ranges(c, spec_class_ranges_not_d(), ignore_case) <==> !spec_is_digit_char(c),
        spec_in_char_ranges(c, spec_class_ranges_w(), ignore_case) <==> spec_is_word_char(c),
        spec_in_char_ranges(c, spec_class_ranges_not_w(), ignore_case) <==> !spec_is_word_char(c),
        spec_in_char_ranges(c, spec_class_ranges_s(), ignore_case) <==> spec_is_space_char(c),
        spec_in_char_ranges(c, spec_class_ranges_not_s(), ignore_case) <==> !spec_is_space_char(c),
{
    let rd = spec_class_ranges_d();
    let rnd = spec_class_ranges_not_d();
    let rw = spec_class_ranges_w();
    let rnw = spec_class_ranges_not_w();
    let rs = spec_class_ranges_s();
    let rns = spec_class_ranges_not_s();

    lemma_in_char_ranges_iff_exists_index(c, rd, ignore_case);
    if spec_is_digit_char(c) {
        assert(spec_range_at_matches(c, rd, 0, ignore_case));
    }

    lemma_in_char_ranges_iff_exists_index(c, rnd, ignore_case);
    if !spec_is_digit_char(c) {
        if c <= 0x002Fu16 {
            assert(spec_range_at_matches(c, rnd, 0, ignore_case));
        } else {
            assert(spec_range_at_matches(c, rnd, 1, ignore_case));
        }
    }

    lemma_in_char_ranges_iff_exists_index(c, rw, ignore_case);
    if spec_is_word_char(c) {
        if 0x0030 <= c && c <= 0x0039 {
            assert(spec_range_at_matches(c, rw, 0, ignore_case));
        } else if 0x0041 <= c && c <= 0x005A {
            assert(spec_range_at_matches(c, rw, 1, ignore_case));
        } else if c == 0x005F {
            assert(spec_range_at_matches(c, rw, 2, ignore_case));
        } else {
            assert(spec_range_at_matches(c, rw, 3, ignore_case));
        }
    }

    lemma_in_char_ranges_iff_exists_index(c, rnw, ignore_case);
    if !spec_is_word_char(c) {
        if c <= 0x002Fu16 {
            assert(spec_range_at_matches(c, rnw, 0, ignore_case));
        } else if c <= 0x0040u16 {
            assert(spec_range_at_matches(c, rnw, 1, ignore_case));
        } else if c <= 0x005Eu16 {
            assert(spec_range_at_matches(c, rnw, 2, ignore_case));
        } else if c == 0x0060u16 {
            assert(spec_range_at_matches(c, rnw, 3, ignore_case));
        } else {
            assert(spec_range_at_matches(c, rnw, 4, ignore_case));
        }
    }

    lemma_in_char_ranges_iff_exists_index(c, rs, ignore_case);
    if spec_is_space_char(c) {
        if 0x0009 <= c && c <= 0x000D {
            assert(spec_range_at_matches(c, rs, 0, ignore_case));
        } else if c == 0x0020 {
            assert(spec_range_at_matches(c, rs, 1, ignore_case));
        } else if c == 0x00A0 {
            assert(spec_range_at_matches(c, rs, 2, ignore_case));
        } else if c == 0x1680 {
            assert(spec_range_at_matches(c, rs, 3, ignore_case));
        } else if 0x2000 <= c && c <= 0x200A {
            assert(spec_range_at_matches(c, rs, 4, ignore_case));
        } else if 0x2028 <= c && c <= 0x2029 {
            assert(spec_range_at_matches(c, rs, 5, ignore_case));
        } else if c == 0x202F {
            assert(spec_range_at_matches(c, rs, 6, ignore_case));
        } else if c == 0x205F {
            assert(spec_range_at_matches(c, rs, 7, ignore_case));
        } else if c == 0x3000 {
            assert(spec_range_at_matches(c, rs, 8, ignore_case));
        } else {
            assert(spec_range_at_matches(c, rs, 9, ignore_case));
        }
    }

    lemma_in_char_ranges_iff_exists_index(c, rns, ignore_case);
    if !spec_is_space_char(c) {
        if c <= 0x0008u16 {
            assert(spec_range_at_matches(c, rns, 0, ignore_case));
        } else if c <= 0x001Fu16 {
            assert(spec_range_at_matches(c, rns, 1, ignore_case));
        } else if c <= 0x009Fu16 {
            assert(spec_range_at_matches(c, rns, 2, ignore_case));
        } else if c <= 0x167Fu16 {
            assert(spec_range_at_matches(c, rns, 3, ignore_case));
        } else if c <= 0x1FFFu16 {
            assert(spec_range_at_matches(c, rns, 4, ignore_case));
        } else if c <= 0x2027u16 {
            assert(spec_range_at_matches(c, rns, 5, ignore_case));
        } else if c <= 0x202Eu16 {
            assert(spec_range_at_matches(c, rns, 6, ignore_case));
        } else if c <= 0x205Eu16 {
            assert(spec_range_at_matches(c, rns, 7, ignore_case));
        } else if c <= 0x2FFFu16 {
            assert(spec_range_at_matches(c, rns, 8, ignore_case));
        } else if c <= 0xFEFEu16 {
            assert(spec_range_at_matches(c, rns, 9, ignore_case));
        } else {
            assert(spec_range_at_matches(c, rns, 10, ignore_case));
        }
    }
}

/// Predicate: group `g` (1-based) appears anywhere inside `ast` (for §22.2.2.5.1 capture reset).
pub open spec fn spec_ast_contains_group(ast: SpecRegexAst, g: u32) -> bool
    decreases ast,
{
    match ast {
        SpecRegexAst::Group { index, sub } => index == g || spec_ast_contains_group(*sub, g),
        SpecRegexAst::Seq(a, b) | SpecRegexAst::Alt(a, b) => {
            spec_ast_contains_group(*a, g) || spec_ast_contains_group(*b, g)
        },
        SpecRegexAst::Repeat { sub, .. } => spec_ast_contains_group(*sub, g),
        _ => false,
    }
}

/// Reset captures belonging to `sub` to `None` before each iteration of `RepeatMatcher` (§22.2.2.5.1 step 4).
pub open spec fn spec_reset_sub_captures(
    caps: Seq<Option<(nat, nat)>>,
    sub: SpecRegexAst,
) -> Seq<Option<(nat, nat)>> {
    Seq::new(
        caps.len(),
        |i: int|
            if 0 <= i && i < 0xFFFF_FFFFint && spec_ast_contains_group(sub, (i + 1) as u32) {
                None
            } else {
                caps[i]
            },
    )
}

// =======================================================================================
// 3. Warblre-Style Defunctionalized Continuation & Choice-Stack Machine
// =======================================================================================

/// Spec matcher state `(pos, captures)`.
pub struct SpecMatchState {
    pub pos: nat,
    pub captures: Seq<Option<(nat, nat)>>,
}

/// Exec matcher state `(pos, captures)`.
pub struct MatchState {
    pub pos: usize,
    pub captures: Vec<Option<(usize, usize)>>,
}

impl View for MatchState {
    type V = SpecMatchState;

    open spec fn view(&self) -> SpecMatchState {
        SpecMatchState {
            pos: self.pos as nat,
            captures: spec_captures_view(self.captures@),
        }
    }
}

/// Spec continuation operation on the control stack.
pub enum SpecContOp {
    Eval(SpecRegexAst),
    CloseGroup { index: u32, start_pos: nat },
    /// §22.2.2.5.1 `RepeatMatcher` continuation `d(y)` with empty-match progress guard!
    RepeatGuard {
        sub: SpecRegexAst,
        prev_pos: nat,
        was_optional: bool,
        rem_min: u32,
        rem_max: Option<u32>,
        greedy: bool,
    },
}

/// Exec continuation operation on the control stack.
pub enum ContOp {
    Eval(RegexAst),
    CloseGroup { index: u32, start_pos: usize },
    RepeatGuard {
        sub: RegexAst,
        prev_pos: usize,
        was_optional: bool,
        rem_min: u32,
        rem_max: Option<u32>,
        greedy: bool,
    },
}

impl View for ContOp {
    type V = SpecContOp;

    open spec fn view(&self) -> SpecContOp {
        match self {
            ContOp::Eval(ast) => SpecContOp::Eval(ast@),
            ContOp::CloseGroup { index, start_pos } => SpecContOp::CloseGroup {
                index: *index,
                start_pos: *start_pos as nat,
            },
            ContOp::RepeatGuard { sub, prev_pos, was_optional, rem_min, rem_max, greedy } => {
                SpecContOp::RepeatGuard {
                    sub: sub@,
                    prev_pos: *prev_pos as nat,
                    was_optional: *was_optional,
                    rem_min: *rem_min,
                    rem_max: *rem_max,
                    greedy: *greedy,
                }
            },
        }
    }
}

pub open spec fn spec_cont_view(cont: Seq<ContOp>) -> Seq<SpecContOp> {
    Seq::new(cont.len(), |i: int| cont[i]@)
}

/// Exec backtrack choice point `(saved_state, saved_cont)`.
pub struct ChoicePoint {
    pub state: MatchState,
    pub cont: Vec<ContOp>,
}

impl View for ChoicePoint {
    type V = (SpecMatchState, Seq<SpecContOp>);

    open spec fn view(&self) -> (SpecMatchState, Seq<SpecContOp>) {
        (self.state@, spec_cont_view(self.cont@))
    }
}

pub open spec fn spec_choices_view(
    choices: Seq<ChoicePoint>,
) -> Seq<(SpecMatchState, Seq<SpecContOp>)> {
    Seq::new(choices.len(), |i: int| choices[i]@)
}

/// Validity invariant on `SpecMatchState` with respect to `input_len` and `start_pos`.
pub open spec fn spec_state_wf(st: SpecMatchState, start_pos: nat, input_len: nat) -> bool {
    start_pos <= st.pos
        && st.pos <= input_len
        && (forall|i: int|
            0 <= i < st.captures.len() ==> match #[trigger] st.captures[i] {
                Some((gs, ge)) => gs <= ge && ge <= input_len,
                None => true,
            })
}

/// Single transition of the top `SpecContOp` (returns `None` on mismatch / empty-match guard rejection,
/// or `Some((next_state, next_cont, pushed_choice))` on transition).
pub open spec fn spec_apply_op(
    input: Seq<u16>,
    flags: RegexFlags,
    state: SpecMatchState,
    op: SpecContOp,
    rest_cont: Seq<SpecContOp>,
) -> Option<(SpecMatchState, Seq<SpecContOp>, Option<(SpecMatchState, Seq<SpecContOp>)>)> {
    match op {
        SpecContOp::Eval(ast) => match ast {
            SpecRegexAst::Empty => Some((state, rest_cont, None)),
            SpecRegexAst::Char(ch) => {
                if state.pos < input.len()
                    && spec_canonicalize_char(input[state.pos as int], flags.ignore_case)
                        == spec_canonicalize_char(ch, flags.ignore_case)
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::Dot => {
                if state.pos < input.len()
                    && (flags.dot_all || !spec_is_line_terminator(input[state.pos as int]))
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::Digit { negated } => {
                if state.pos < input.len()
                    && (spec_is_digit_char(input[state.pos as int]) != negated)
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::Word { negated } => {
                if state.pos < input.len()
                    && (spec_is_word_char(input[state.pos as int]) != negated)
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::Space { negated } => {
                if state.pos < input.len()
                    && (spec_is_space_char(input[state.pos as int]) != negated)
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::CharClass { negated, ranges } => {
                if state.pos < input.len()
                    && (spec_in_char_ranges(input[state.pos as int], ranges, flags.ignore_case)
                        != negated)
                {
                    Some((
                        SpecMatchState { pos: state.pos + 1, captures: state.captures },
                        rest_cont,
                        None,
                    ))
                } else {
                    None
                }
            },
            SpecRegexAst::AnchorStart => {
                let ok = state.pos == 0
                    || (flags.multiline
                        && state.pos > 0
                        && state.pos <= input.len()
                        && spec_is_line_terminator(input[state.pos as int - 1]));
                if ok {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            SpecRegexAst::AnchorEnd => {
                let ok = state.pos == input.len()
                    || (flags.multiline
                        && state.pos < input.len()
                        && spec_is_line_terminator(input[state.pos as int]));
                if ok {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            SpecRegexAst::WordBoundary { negated } => {
                let left_w = state.pos > 0
                    && state.pos <= input.len()
                    && spec_is_word_char(input[state.pos as int - 1]);
                let right_w = state.pos < input.len()
                    && spec_is_word_char(input[state.pos as int]);
                let is_boundary = left_w != right_w;
                if is_boundary != negated {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            SpecRegexAst::Seq(a, b) => {
                let next_cont = rest_cont.push(SpecContOp::Eval(*b)).push(SpecContOp::Eval(*a));
                Some((state, next_cont, None))
            },
            SpecRegexAst::Alt(a, b) => {
                let alt_cont = rest_cont.push(SpecContOp::Eval(*b));
                let cur_cont = rest_cont.push(SpecContOp::Eval(*a));
                Some((state, cur_cont, Some((state, alt_cont))))
            },
            SpecRegexAst::Group { index, sub } => {
                let next_cont = rest_cont
                    .push(SpecContOp::CloseGroup { index, start_pos: state.pos })
                    .push(SpecContOp::Eval(*sub));
                Some((state, next_cont, None))
            },
            SpecRegexAst::Repeat { sub, min, max, greedy } => {
                if max == Some(0u32) {
                    Some((state, rest_cont, None))
                } else if max.is_some() && min > max.unwrap() {
                    None
                } else {
                    let rem_min = if min > 0 { (min - 1) as u32 } else { 0u32 };
                    let rem_max = match max {
                        Some(m) => Some((m - 1) as u32),
                        None => None,
                    };
                    let iter_state = SpecMatchState {
                        pos: state.pos,
                        captures: spec_reset_sub_captures(state.captures, *sub),
                    };
                    let iter_cont = rest_cont
                        .push(SpecContOp::RepeatGuard {
                            sub: *sub,
                            prev_pos: state.pos,
                            was_optional: min == 0,
                            rem_min,
                            rem_max,
                            greedy,
                        })
                        .push(SpecContOp::Eval(*sub));
                    if min > 0 {
                        Some((iter_state, iter_cont, None))
                    } else if greedy {
                        Some((iter_state, iter_cont, Some((state, rest_cont))))
                    } else {
                        Some((state, rest_cont, Some((iter_state, iter_cont))))
                    }
                }
            },
        },
        SpecContOp::CloseGroup { index, start_pos } => {
            if index >= 1
                && (index as int - 1) < state.captures.len()
                && start_pos <= state.pos
            {
                let next_caps = state
                    .captures
                    .update(index as int - 1, Some((start_pos, state.pos)));
                Some((
                    SpecMatchState { pos: state.pos, captures: next_caps },
                    rest_cont,
                    None,
                ))
            } else {
                Some((state, rest_cont, None))
            }
        },
        SpecContOp::RepeatGuard { sub, prev_pos, was_optional, rem_min, rem_max, greedy } => {
            // ECMA-262 §22.2.2.5.1 step 2.b: if min == 0 and y.endIndex == x.endIndex, return failure!
            if was_optional && state.pos <= prev_pos {
                None
            } else {
                let next_cont = rest_cont.push(SpecContOp::Eval(SpecRegexAst::Repeat {
                    sub: Box::new(sub),
                    min: rem_min,
                    max: rem_max,
                    greedy,
                }));
                Some((state, next_cont, None))
            }
        },
    }
}

/// Step-bounded backtracking loop (`decreases steps`).
pub open spec fn spec_run_machine(
    input: Seq<u16>,
    flags: RegexFlags,
    start_pos: nat,
    state: SpecMatchState,
    cont: Seq<SpecContOp>,
    choices: Seq<(SpecMatchState, Seq<SpecContOp>)>,
    steps: nat,
) -> SpecMatchOutcome
    decreases steps,
{
    if cont.len() == 0 {
        SpecMatchOutcome::Matched {
            start_pos,
            end_pos: state.pos,
            captures: state.captures,
        }
    } else if steps == 0 {
        SpecMatchOutcome::StepLimitExceeded
    } else {
        let top = cont[cont.len() - 1];
        let rest_cont = cont.subrange(0, cont.len() - 1);
        match spec_apply_op(input, flags, state, top, rest_cont) {
            Some((next_state, next_cont, maybe_choice)) => {
                let next_choices = match maybe_choice {
                    Some(cp) => choices.push(cp),
                    None => choices,
                };
                spec_run_machine(
                    input,
                    flags,
                    start_pos,
                    next_state,
                    next_cont,
                    next_choices,
                    (steps - 1) as nat,
                )
            },
            None => {
                if choices.len() == 0 {
                    SpecMatchOutcome::NoMatch
                } else {
                    let (bt_state, bt_cont) = choices[choices.len() - 1];
                    let rem_choices = choices.subrange(0, choices.len() - 1);
                    spec_run_machine(
                        input,
                        flags,
                        start_pos,
                        bt_state,
                        bt_cont,
                        rem_choices,
                        (steps - 1) as nat,
                    )
                }
            },
        }
    }
}

/// Anchored match starting at `start_pos` (`§22.2.2.2`).
pub open spec fn spec_match(
    ast: SpecRegexAst,
    flags: RegexFlags,
    input: Seq<u16>,
    start_pos: nat,
    num_groups: nat,
    steps: nat,
) -> SpecMatchOutcome {
    if start_pos > input.len() {
        SpecMatchOutcome::NoMatch
    } else {
        let init_state = SpecMatchState {
            pos: start_pos,
            captures: Seq::new(num_groups, |_i: int| None),
        };
        let init_cont = seq![SpecContOp::Eval(ast)];
        spec_run_machine(input, flags, start_pos, init_state, init_cont, Seq::empty(), steps)
    }
}

/// Unanchored search scanning `start_pos` from `from_pos` up to `input.len()` (`RegExpBuiltinExec` §22.2.5.2.2).
pub open spec fn spec_search_from(
    ast: SpecRegexAst,
    flags: RegexFlags,
    input: Seq<u16>,
    pos: nat,
    num_groups: nat,
    steps_per_pos: nat,
) -> SpecMatchOutcome
    decreases (if pos <= input.len() { (input.len() + 1) - pos } else { 0 }),
{
    if pos > input.len() {
        SpecMatchOutcome::NoMatch
    } else {
        match spec_match(ast, flags, input, pos, num_groups, steps_per_pos) {
            SpecMatchOutcome::Matched { start_pos, end_pos, captures } => {
                SpecMatchOutcome::Matched { start_pos, end_pos, captures }
            },
            SpecMatchOutcome::StepLimitExceeded => SpecMatchOutcome::StepLimitExceeded,
            SpecMatchOutcome::NoMatch => {
                spec_search_from(ast, flags, input, pos + 1, num_groups, steps_per_pos)
            },
        }
    }
}

// =======================================================================================
// 4. Proofs: Empty-Match Progress Guard, Zero-Width Loop Freedom, and Bounds Validity
// =======================================================================================

/// **§22.2.2.5.1 Empty-Match Progress Guard Theorem**:
/// For every optional repetition (`was_optional == true`):
/// 1. Zero-width matches (`state.pos == prev_pos`) are rejected (`None`), preventing zero-width loops.
/// 2. Any accepted transition strictly advances `state.pos > prev_pos` (`input.len() - state.pos` strictly decreases!).
pub proof fn lemma_empty_match_guard_strict_progress(
    input: Seq<u16>,
    flags: RegexFlags,
    state: SpecMatchState,
    sub: SpecRegexAst,
    prev_pos: nat,
    rem_min: u32,
    rem_max: Option<u32>,
    greedy: bool,
    rest_cont: Seq<SpecContOp>,
)
    ensures
        ({
            let op = SpecContOp::RepeatGuard {
                sub,
                prev_pos,
                was_optional: true,
                rem_min,
                rem_max,
                greedy,
            };
            let res = spec_apply_op(input, flags, state, op, rest_cont);
            &&& (state.pos <= prev_pos ==> res.is_none())
            &&& (res.is_some() ==> state.pos > prev_pos)
        }),
{
}

/// **End-to-End Zero-Width Star Termination Theorem**:
/// Matching `(?:)*` (`Repeat { sub: Empty, min: 0, max: None, greedy: true }`) at `start_pos == 0`
/// on ANY `input: Seq<u16>` terminates in 4 machine steps with `Matched { start_pos: 0, end_pos: 0 }`
/// (instead of diverging or exhausting arbitrary `steps >= 4`!).
pub proof fn lemma_zero_width_star_terminates_immediately(
    input: Seq<u16>,
    flags: RegexFlags,
    steps: nat,
)
    requires
        steps >= 4,
    ensures
        spec_match(
            SpecRegexAst::Repeat {
                sub: Box::new(SpecRegexAst::Empty),
                min: 0,
                max: None,
                greedy: true,
            },
            flags,
            input,
            0,
            0,
            steps,
        ) == (SpecMatchOutcome::Matched {
            start_pos: 0,
            end_pos: 0,
            captures: Seq::empty(),
        }),
{
    reveal_with_fuel(spec_run_machine, 5);
    let empty_caps = Seq::<Option<(nat, nat)>>::new(0, |_i: int| None);
    assert(empty_caps =~= Seq::<Option<(nat, nat)>>::empty());
    let sub = SpecRegexAst::Empty;
    assert(spec_reset_sub_captures(empty_caps, sub) =~= empty_caps);
    let init_st = SpecMatchState { pos: 0, captures: empty_caps };
    let r_ast = SpecRegexAst::Repeat {
        sub: Box::new(sub),
        min: 0,
        max: None,
        greedy: true,
    };
    let c0 = seq![SpecContOp::Eval(r_ast)];
    assert(c0.subrange(0, 0) =~= Seq::<SpecContOp>::empty());
    let guard_op = SpecContOp::RepeatGuard {
        sub,
        prev_pos: 0,
        was_optional: true,
        rem_min: 0,
        rem_max: None,
        greedy: true,
    };
    let c1 = Seq::<SpecContOp>::empty().push(guard_op).push(SpecContOp::Eval(sub));
    assert(c1[c1.len() - 1] == SpecContOp::Eval(sub));
    assert(c1.subrange(0, c1.len() - 1) =~= seq![guard_op]);
    let ch1 = Seq::<(SpecMatchState, Seq<SpecContOp>)>::empty().push((
        init_st,
        Seq::<SpecContOp>::empty(),
    ));
    assert(ch1[ch1.len() - 1] == (init_st, Seq::<SpecContOp>::empty()));
}

/// Preservation of `spec_state_wf` across `spec_apply_op`.
proof fn lemma_apply_op_preserves_wf(
    input: Seq<u16>,
    flags: RegexFlags,
    start_pos: nat,
    state: SpecMatchState,
    op: SpecContOp,
    rest_cont: Seq<SpecContOp>,
)
    requires
        spec_state_wf(state, start_pos, input.len()),
    ensures
        match spec_apply_op(input, flags, state, op, rest_cont) {
            Some((next_st, _, maybe_cp)) => {
                &&& spec_state_wf(next_st, start_pos, input.len())
                &&& match maybe_cp {
                    Some((cp_st, _)) => spec_state_wf(cp_st, start_pos, input.len()),
                    None => true,
                }
            },
            None => true,
        },
{
}

proof fn lemma_run_machine_bounds(
    input: Seq<u16>,
    flags: RegexFlags,
    start_pos: nat,
    state: SpecMatchState,
    cont: Seq<SpecContOp>,
    choices: Seq<(SpecMatchState, Seq<SpecContOp>)>,
    steps: nat,
)
    requires
        spec_state_wf(state, start_pos, input.len()),
        forall|k: int|
            0 <= k < choices.len() ==> spec_state_wf((#[trigger] choices[k]).0, start_pos, input.len()),
    ensures
        match spec_run_machine(input, flags, start_pos, state, cont, choices, steps) {
            SpecMatchOutcome::Matched { start_pos: sp, end_pos, captures } => {
                &&& sp == start_pos
                &&& sp <= end_pos && end_pos <= input.len()
                &&& forall|i: int|
                    0 <= i < captures.len() ==> match #[trigger] captures[i] {
                        Some((gs, ge)) => gs <= ge && ge <= input.len(),
                        None => true,
                    }
            },
            _ => true,
        },
    decreases steps,
{
    if cont.len() > 0 && steps > 0 {
        let top = cont[cont.len() - 1];
        let rest_cont = cont.subrange(0, cont.len() - 1);
        lemma_apply_op_preserves_wf(input, flags, start_pos, state, top, rest_cont);
        match spec_apply_op(input, flags, state, top, rest_cont) {
            Some((next_st, next_cont, maybe_cp)) => {
                let next_choices = match maybe_choice_helper(maybe_cp) {
                    Some(cp) => choices.push(cp),
                    None => choices,
                };
                assert forall|k: int|
                    0 <= k < next_choices.len() implies spec_state_wf(
                    (#[trigger] next_choices[k]).0,
                    start_pos,
                    input.len(),
                ) by {
                    if k < choices.len() {
                        assert(next_choices[k] == choices[k]);
                    }
                }
                lemma_run_machine_bounds(
                    input,
                    flags,
                    start_pos,
                    next_st,
                    next_cont,
                    next_choices,
                    (steps - 1) as nat,
                );
            },
            None => {
                if choices.len() > 0 {
                    let (bt_state, bt_cont) = choices[choices.len() - 1];
                    let rem_choices = choices.subrange(0, choices.len() - 1);
                    assert(spec_state_wf(choices[choices.len() - 1].0, start_pos, input.len()));
                    assert forall|k: int|
                        0 <= k < rem_choices.len() implies spec_state_wf(
                        (#[trigger] rem_choices[k]).0,
                        start_pos,
                        input.len(),
                    ) by {
                        assert(rem_choices[k] == choices[k]);
                    }
                    lemma_run_machine_bounds(
                        input,
                        flags,
                        start_pos,
                        bt_state,
                        bt_cont,
                        rem_choices,
                        (steps - 1) as nat,
                    );
                }
            },
        }
    }
}

pub open spec fn maybe_choice_helper(
    m: Option<(SpecMatchState, Seq<SpecContOp>)>,
) -> Option<(SpecMatchState, Seq<SpecContOp>)> {
    m
}

/// **Match Bounds Validity Theorem**:
/// Every match produced by `spec_match` satisfies `start_pos <= end_pos <= input.len()` and
/// valid capture spans `gs <= ge <= input.len()`.
pub proof fn lemma_match_bounds_valid(
    ast: SpecRegexAst,
    flags: RegexFlags,
    input: Seq<u16>,
    start_pos: nat,
    num_groups: nat,
    steps: nat,
)
    ensures
        match spec_match(ast, flags, input, start_pos, num_groups, steps) {
            SpecMatchOutcome::Matched { start_pos: sp, end_pos, captures } => {
                &&& sp == start_pos
                &&& sp <= end_pos && end_pos <= input.len()
                &&& captures.len() == num_groups
                &&& forall|i: int|
                    0 <= i < captures.len() ==> match #[trigger] captures[i] {
                        Some((gs, ge)) => gs <= ge && ge <= input.len(),
                        None => true,
                    }
            },
            _ => true,
        },
{
    if start_pos <= input.len() {
        let init_state = SpecMatchState {
            pos: start_pos,
            captures: Seq::new(num_groups, |_i: int| None),
        };
        let init_cont = seq![SpecContOp::Eval(ast)];
        lemma_run_machine_bounds_len(
            input,
            flags,
            start_pos,
            init_state,
            init_cont,
            Seq::empty(),
            num_groups,
            steps,
        );
    }
}

proof fn lemma_run_machine_bounds_len(
    input: Seq<u16>,
    flags: RegexFlags,
    start_pos: nat,
    state: SpecMatchState,
    cont: Seq<SpecContOp>,
    choices: Seq<(SpecMatchState, Seq<SpecContOp>)>,
    num_groups: nat,
    steps: nat,
)
    requires
        spec_state_wf(state, start_pos, input.len()),
        state.captures.len() == num_groups,
        forall|k: int|
            0 <= k < choices.len() ==> {
                &&& spec_state_wf((#[trigger] choices[k]).0, start_pos, input.len())
                &&& choices[k].0.captures.len() == num_groups
            },
    ensures
        match spec_run_machine(input, flags, start_pos, state, cont, choices, steps) {
            SpecMatchOutcome::Matched { start_pos: sp, end_pos, captures } => {
                &&& sp == start_pos
                &&& sp <= end_pos && end_pos <= input.len()
                &&& captures.len() == num_groups
                &&& forall|i: int|
                    0 <= i < captures.len() ==> match #[trigger] captures[i] {
                        Some((gs, ge)) => gs <= ge && ge <= input.len(),
                        None => true,
                    }
            },
            _ => true,
        },
    decreases steps,
{
    if cont.len() > 0 && steps > 0 {
        let top = cont[cont.len() - 1];
        let rest_cont = cont.subrange(0, cont.len() - 1);
        lemma_apply_op_preserves_wf(input, flags, start_pos, state, top, rest_cont);
        match spec_apply_op(input, flags, state, top, rest_cont) {
            Some((next_st, next_cont, maybe_cp)) => {
                let next_choices = match maybe_cp {
                    Some(cp) => choices.push(cp),
                    None => choices,
                };
                assert forall|k: int| 0 <= k < next_choices.len() implies {
                    &&& spec_state_wf((#[trigger] next_choices[k]).0, start_pos, input.len())
                    &&& next_choices[k].0.captures.len() == num_groups
                } by {
                    if k < choices.len() {
                        assert(next_choices[k] == choices[k]);
                    }
                }
                lemma_run_machine_bounds_len(
                    input,
                    flags,
                    start_pos,
                    next_st,
                    next_cont,
                    next_choices,
                    num_groups,
                    (steps - 1) as nat,
                );
            },
            None => {
                if choices.len() > 0 {
                    let (bt_state, bt_cont) = choices[choices.len() - 1];
                    let rem_choices = choices.subrange(0, choices.len() - 1);
                    assert(spec_state_wf(choices[choices.len() - 1].0, start_pos, input.len()));
                    assert forall|k: int| 0 <= k < rem_choices.len() implies {
                        &&& spec_state_wf((#[trigger] rem_choices[k]).0, start_pos, input.len())
                        &&& rem_choices[k].0.captures.len() == num_groups
                    } by {
                        assert(rem_choices[k] == choices[k]);
                    }
                    lemma_run_machine_bounds_len(
                        input,
                        flags,
                        start_pos,
                        bt_state,
                        bt_cont,
                        rem_choices,
                        num_groups,
                        (steps - 1) as nat,
                    );
                }
            },
        }
    }
}

// =======================================================================================
// 5. Exec Matcher (`exec_match` == `spec_match`, `exec_search` == `spec_search_from`)
// =======================================================================================

fn is_line_terminator_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_line_terminator(c),
{
    c == 0x000A || c == 0x000D || c == 0x2028 || c == 0x2029
}

fn is_digit_char_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_digit_char(c),
{
    c >= 0x0030 && c <= 0x0039
}

fn is_word_char_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_word_char(c),
{
    (c >= 0x0041 && c <= 0x005A)
        || (c >= 0x0061 && c <= 0x007A)
        || (c >= 0x0030 && c <= 0x0039)
        || c == 0x005F
}

fn is_space_char_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_space_char(c),
{
    c == 0x0009
        || c == 0x000B
        || c == 0x000C
        || c == 0x0020
        || c == 0x00A0
        || c == 0xFEFF
        || c == 0x1680
        || (c >= 0x2000 && c <= 0x200A)
        || c == 0x202F
        || c == 0x205F
        || c == 0x3000
        || is_line_terminator_exec(c)
}

fn canonicalize_char_exec(c: u16, ignore_case: bool) -> (res: u16)
    ensures
        res == spec_canonicalize_char(c, ignore_case),
{
    if ignore_case && c >= 0x0061 && c <= 0x007A {
        c - 32
    } else {
        c
    }
}

fn in_char_ranges_exec(c: u16, ranges: &[(u16, u16)], ignore_case: bool) -> (res: bool)
    ensures
        res == spec_in_char_ranges(c, ranges@, ignore_case),
{
    let n = ranges.len();
    let mut i: usize = 0;
    proof {
        assert(ranges@.subrange(0, n as int) =~= ranges@);
    }
    while i < n
        invariant
            i <= n,
            n == ranges@.len(),
            spec_in_char_ranges(c, ranges@, ignore_case)
                == spec_in_char_ranges(c, ranges@.subrange(i as int, n as int), ignore_case),
        decreases n - i,
    {
        let (lo, hi) = ranges[i];
        let ghost sub = ranges@.subrange(i as int, n as int);
        let match_head = (lo <= c && c <= hi)
            || (ignore_case
                && 0x0041 <= c
                && c <= 0x005A
                && lo <= c + 32
                && c + 32 <= hi)
            || (ignore_case
                && 0x0061 <= c
                && c <= 0x007A
                && lo <= c - 32
                && c - 32 <= hi);
        if match_head {
            return true;
        }
        i += 1;
        proof {
            assert(sub.subrange(1, sub.len() as int) =~= ranges@.subrange(i as int, n as int));
        }
    }
    proof {
        assert(ranges@.subrange(n as int, n as int) =~= Seq::<(u16, u16)>::empty());
    }
    false
}

fn ast_contains_group_exec(ast: &RegexAst, g: u32) -> (res: bool)
    ensures
        res == spec_ast_contains_group(ast@, g),
    decreases spec_regex_size(ast@),
{
    match ast {
        RegexAst::Group { index, sub } => *index == g || ast_contains_group_exec(&**sub, g),
        RegexAst::Seq(a, b) | RegexAst::Alt(a, b) => {
            ast_contains_group_exec(&**a, g) || ast_contains_group_exec(&**b, g)
        },
        RegexAst::Repeat { sub, .. } => ast_contains_group_exec(&**sub, g),
        _ => false,
    }
}

fn reset_sub_captures_exec(
    caps: &[Option<(usize, usize)>],
    sub: &RegexAst,
) -> (out: Vec<Option<(usize, usize)>>)
    ensures
        spec_captures_view(out@) == spec_reset_sub_captures(spec_captures_view(caps@), sub@),
        out@.len() == caps@.len(),
{
    let n = caps.len();
    let mut out: Vec<Option<(usize, usize)>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == caps@.len(),
            out@.len() == i as int,
            forall|k: int|
                0 <= k < i as int ==> spec_captures_view(out@)[k]
                    == spec_reset_sub_captures(spec_captures_view(caps@), sub@)[k],
        decreases n - i,
    {
        let should_reset = if i < 0xFFFF_FFFFusize {
            ast_contains_group_exec(sub, (i + 1) as u32)
        } else {
            false
        };
        let ghost prev_out = out@;
        if should_reset {
            out.push(None);
        } else {
            out.push(caps[i]);
        }
        i += 1;
        proof {
            assert forall|k: int| 0 <= k < i as int implies spec_captures_view(out@)[k]
                == spec_reset_sub_captures(spec_captures_view(caps@), sub@)[k] by {
                if k < i as int - 1 {
                    assert(out@[k] == prev_out[k]);
                    assert(spec_captures_view(out@)[k] == spec_captures_view(prev_out)[k]);
                }
            }
        }
    }
    proof {
        assert(spec_captures_view(out@)
            =~= spec_reset_sub_captures(spec_captures_view(caps@), sub@));
    }
    out
}

fn clone_state_exec(st: &MatchState) -> (out: MatchState)
    ensures
        out@ == st@,
{
    let n = st.captures.len();
    let mut caps: Vec<Option<(usize, usize)>> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == st.captures@.len(),
            caps@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> caps@[k] == st.captures@[k],
        decreases n - i,
    {
        caps.push(st.captures[i]);
        i += 1;
    }
    proof {
        assert(caps@ =~= st.captures@);
    }
    MatchState { pos: st.pos, captures: caps }
}

fn clone_cont_op_exec(op: &ContOp) -> (out: ContOp)
    ensures
        out@ == op@,
{
    match op {
        ContOp::Eval(ast) => ContOp::Eval(clone_regex_ast(ast)),
        ContOp::CloseGroup { index, start_pos } => ContOp::CloseGroup {
            index: *index,
            start_pos: *start_pos,
        },
        ContOp::RepeatGuard { sub, prev_pos, was_optional, rem_min, rem_max, greedy } => {
            ContOp::RepeatGuard {
                sub: clone_regex_ast(sub),
                prev_pos: *prev_pos,
                was_optional: *was_optional,
                rem_min: *rem_min,
                rem_max: *rem_max,
                greedy: *greedy,
            }
        },
    }
}

fn clone_cont_vec_exec(cont: &[ContOp]) -> (out: Vec<ContOp>)
    ensures
        spec_cont_view(out@) == spec_cont_view(cont@),
{
    let n = cont.len();
    let mut out: Vec<ContOp> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == cont@.len(),
            out@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> out@[k]@ == cont@[k]@,
        decreases n - i,
    {
        out.push(clone_cont_op_exec(&cont[i]));
        i += 1;
    }
    proof {
        assert(spec_cont_view(out@) =~= spec_cont_view(cont@));
    }
    out
}

#[verifier::spinoff_prover]
fn apply_op_exec(
    input: &[u16],
    flags: RegexFlags,
    state: MatchState,
    op: ContOp,
    mut rest_cont: Vec<ContOp>,
) -> (res: Option<(MatchState, Vec<ContOp>, Option<ChoicePoint>)>)
    requires
        state.pos <= input@.len(),
    ensures
        match res {
            Some((nst, ncont, mcp)) => {
                &&& nst.pos <= input@.len()
                &&& match mcp {
                    Some(cp) => {
                        &&& cp.state.pos <= input@.len()
                        &&& spec_apply_op(
                            input@,
                            flags,
                            state@,
                            op@,
                            spec_cont_view(rest_cont@),
                        ) == Some((nst@, spec_cont_view(ncont@), Some(cp@)))
                    },
                    None => {
                        spec_apply_op(
                            input@,
                            flags,
                            state@,
                            op@,
                            spec_cont_view(rest_cont@),
                        ) == Some((nst@, spec_cont_view(ncont@), None))
                    },
                }
            },
            None => spec_apply_op(input@, flags, state@, op@, spec_cont_view(rest_cont@)).is_none(),
        },
{
    let n = input.len();
    match op {
        ContOp::Eval(ast) => match ast {
            RegexAst::Empty => Some((state, rest_cont, None)),
            RegexAst::Char(ch) => {
                if state.pos < n
                    && canonicalize_char_exec(input[state.pos], flags.ignore_case)
                        == canonicalize_char_exec(ch, flags.ignore_case)
                {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::Dot => {
                if state.pos < n && (flags.dot_all || !is_line_terminator_exec(input[state.pos])) {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::Digit { negated } => {
                if state.pos < n && (is_digit_char_exec(input[state.pos]) != negated) {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::Word { negated } => {
                if state.pos < n && (is_word_char_exec(input[state.pos]) != negated) {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::Space { negated } => {
                if state.pos < n && (is_space_char_exec(input[state.pos]) != negated) {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::CharClass { negated, ranges } => {
                if state.pos < n
                    && (in_char_ranges_exec(input[state.pos], ranges.as_slice(), flags.ignore_case)
                        != negated)
                {
                    let nst = MatchState { pos: state.pos + 1, captures: state.captures };
                    Some((nst, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::AnchorStart => {
                let ok = state.pos == 0
                    || (flags.multiline
                        && state.pos > 0
                        && is_line_terminator_exec(input[state.pos - 1]));
                if ok {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::AnchorEnd => {
                let ok = state.pos == n
                    || (flags.multiline
                        && state.pos < n
                        && is_line_terminator_exec(input[state.pos]));
                if ok {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::WordBoundary { negated } => {
                let left_w = state.pos > 0 && is_word_char_exec(input[state.pos - 1]);
                let right_w = state.pos < n && is_word_char_exec(input[state.pos]);
                let is_boundary = left_w != right_w;
                if is_boundary != negated {
                    Some((state, rest_cont, None))
                } else {
                    None
                }
            },
            RegexAst::Seq(a, b) => {
                let ghost rc_v = spec_cont_view(rest_cont@);
                let ghost a_v = (*a)@;
                let ghost b_v = (*b)@;
                rest_cont.push(ContOp::Eval(*b));
                rest_cont.push(ContOp::Eval(*a));
                proof {
                    assert(spec_cont_view(rest_cont@)
                        =~= rc_v.push(SpecContOp::Eval(b_v)).push(SpecContOp::Eval(a_v)));
                }
                Some((state, rest_cont, None))
            },
            RegexAst::Alt(a, b) => {
                let ghost rc_v = spec_cont_view(rest_cont@);
                let ghost a_v = (*a)@;
                let ghost b_v = (*b)@;
                let mut alt_cont = clone_cont_vec_exec(rest_cont.as_slice());
                alt_cont.push(ContOp::Eval(*b));
                let alt_st = clone_state_exec(&state);
                rest_cont.push(ContOp::Eval(*a));
                proof {
                    assert(spec_cont_view(alt_cont@) =~= rc_v.push(SpecContOp::Eval(b_v)));
                    assert(spec_cont_view(rest_cont@) =~= rc_v.push(SpecContOp::Eval(a_v)));
                }
                Some((state, rest_cont, Some(ChoicePoint { state: alt_st, cont: alt_cont })))
            },
            RegexAst::Group { index, sub } => {
                let ghost rc_v = spec_cont_view(rest_cont@);
                let ghost sub_v = (*sub)@;
                let sp = state.pos;
                rest_cont.push(ContOp::CloseGroup { index, start_pos: sp });
                rest_cont.push(ContOp::Eval(*sub));
                proof {
                    assert(spec_cont_view(rest_cont@)
                        =~= rc_v
                            .push(SpecContOp::CloseGroup { index, start_pos: sp as nat })
                            .push(SpecContOp::Eval(sub_v)));
                }
                Some((state, rest_cont, None))
            },
            RegexAst::Repeat { sub, min, max, greedy } => {
                let ghost rc_v = spec_cont_view(rest_cont@);
                let ghost sub_v = (*sub)@;
                if max == Some(0u32) {
                    Some((state, rest_cont, None))
                } else if max.is_some() && min > max.unwrap() {
                    None
                } else {
                    let rem_min = if min > 0 { min - 1 } else { 0u32 };
                    let rem_max = match max {
                        Some(m) => Some(m - 1),
                        None => None,
                    };
                    let iter_caps = reset_sub_captures_exec(state.captures.as_slice(), &*sub);
                    let iter_state = MatchState { pos: state.pos, captures: iter_caps };
                    let sub_clone = clone_regex_ast(&*sub);
                    let guard = ContOp::RepeatGuard {
                        sub: sub_clone,
                        prev_pos: state.pos,
                        was_optional: min == 0,
                        rem_min,
                        rem_max,
                        greedy,
                    };
                    let ghost guard_v = guard@;
                    if min > 0 {
                        rest_cont.push(guard);
                        rest_cont.push(ContOp::Eval(*sub));
                        proof {
                            assert(spec_cont_view(rest_cont@)
                                =~= rc_v.push(guard_v).push(SpecContOp::Eval(sub_v)));
                        }
                        Some((iter_state, rest_cont, None))
                    } else if greedy {
                        let exit_cont = clone_cont_vec_exec(rest_cont.as_slice());
                        rest_cont.push(guard);
                        rest_cont.push(ContOp::Eval(*sub));
                        proof {
                            assert(spec_cont_view(rest_cont@)
                                =~= rc_v.push(guard_v).push(SpecContOp::Eval(sub_v)));
                        }
                        Some((
                            iter_state,
                            rest_cont,
                            Some(ChoicePoint { state, cont: exit_cont }),
                        ))
                    } else {
                        let mut iter_cont = clone_cont_vec_exec(rest_cont.as_slice());
                        iter_cont.push(guard);
                        iter_cont.push(ContOp::Eval(*sub));
                        proof {
                            assert(spec_cont_view(iter_cont@)
                                =~= rc_v.push(guard_v).push(SpecContOp::Eval(sub_v)));
                        }
                        Some((
                            state,
                            rest_cont,
                            Some(ChoicePoint { state: iter_state, cont: iter_cont }),
                        ))
                    }
                }
            },
        },
        ContOp::CloseGroup { index, start_pos } => {
            if index >= 1
                && ((index - 1) as usize) < state.captures.len()
                && start_pos <= state.pos
            {
                let mut ncaps = state.captures;
                let ghost old_caps_v = spec_captures_view(ncaps@);
                ncaps.set((index - 1) as usize, Some((start_pos, state.pos)));
                proof {
                    assert(spec_captures_view(ncaps@)
                        =~= old_caps_v.update(
                            index as int - 1,
                            Some((start_pos as nat, state.pos as nat)),
                        ));
                }
                Some((MatchState { pos: state.pos, captures: ncaps }, rest_cont, None))
            } else {
                Some((state, rest_cont, None))
            }
        },
        ContOp::RepeatGuard { sub, prev_pos, was_optional, rem_min, rem_max, greedy } => {
            if was_optional && state.pos <= prev_pos {
                None
            } else {
                let ghost rc_v = spec_cont_view(rest_cont@);
                let ghost sub_v = sub@;
                let rep = RegexAst::Repeat {
                    sub: Box::new(sub),
                    min: rem_min,
                    max: rem_max,
                    greedy,
                };
                rest_cont.push(ContOp::Eval(rep));
                proof {
                    assert(spec_cont_view(rest_cont@)
                        =~= rc_v.push(SpecContOp::Eval(SpecRegexAst::Repeat {
                            sub: Box::new(sub_v),
                            min: rem_min,
                            max: rem_max,
                            greedy,
                        })));
                }
                Some((state, rest_cont, None))
            }
        },
    }
}

/// Exec step-bounded backtracking loop proved equal to `spec_run_machine`.
fn run_machine_exec(
    input: &[u16],
    flags: RegexFlags,
    start_pos: usize,
    state_in: MatchState,
    cont_in: Vec<ContOp>,
    choices_in: Vec<ChoicePoint>,
    steps_in: usize,
) -> (out: MatchOutcome)
    requires
        state_in.pos <= input@.len(),
        forall|k: int|
            0 <= k < choices_in@.len() ==> (#[trigger] choices_in@[k]).state.pos <= input@.len(),
    ensures
        out@
            == spec_run_machine(
                input@,
                flags,
                start_pos as nat,
                state_in@,
                spec_cont_view(cont_in@),
                spec_choices_view(choices_in@),
                steps_in as nat,
            ),
{
    let ghost init_st = state_in@;
    let ghost init_cont = spec_cont_view(cont_in@);
    let ghost init_choices = spec_choices_view(choices_in@);
    let ghost init_steps = steps_in as nat;
    let mut state = state_in;
    let mut cont = cont_in;
    let mut choices = choices_in;
    let mut steps = steps_in;
    loop
        invariant
            state.pos <= input@.len(),
            forall|k: int|
                0 <= k < choices@.len() ==> (#[trigger] choices@[k]).state.pos <= input@.len(),
            init_st == state_in@,
            init_cont == spec_cont_view(cont_in@),
            init_choices == spec_choices_view(choices_in@),
            init_steps == steps_in as nat,
            spec_run_machine(
                input@,
                flags,
                start_pos as nat,
                init_st,
                init_cont,
                init_choices,
                init_steps,
            )
                == spec_run_machine(
                    input@,
                    flags,
                    start_pos as nat,
                    state@,
                    spec_cont_view(cont@),
                    spec_choices_view(choices@),
                    steps as nat,
                ),
        decreases steps,
    {
        if cont.len() == 0 {
            return MatchOutcome::Matched {
                start_pos,
                end_pos: state.pos,
                captures: state.captures,
            };
        }
        if steps == 0 {
            return MatchOutcome::StepLimitExceeded;
        }
        let ghost pre_cont_v = spec_cont_view(cont@);
        let ghost pre_choices_v = spec_choices_view(choices@);
        let top = cont.pop().unwrap();
        proof {
            assert(top@ == pre_cont_v[pre_cont_v.len() - 1]);
            assert(spec_cont_view(cont@) =~= pre_cont_v.subrange(0, pre_cont_v.len() - 1));
        }
        match apply_op_exec(input, flags, state, top, cont) {
            Some((nst, ncont, mcp)) => {
                if let Some(cp) = mcp {
                    choices.push(cp);
                    proof {
                        assert(spec_choices_view(choices@) =~= pre_choices_v.push(cp@));
                    }
                }
                state = nst;
                cont = ncont;
                steps -= 1;
            },
            None => {
                if choices.len() == 0 {
                    return MatchOutcome::NoMatch;
                }
                let cp = choices.pop().unwrap();
                proof {
                    assert(cp@ == pre_choices_v[pre_choices_v.len() - 1]);
                    assert(spec_choices_view(choices@)
                        =~= pre_choices_v.subrange(0, pre_choices_v.len() - 1));
                }
                state = cp.state;
                cont = cp.cont;
                steps -= 1;
            },
        }
    }
}

/// Exec anchored matcher (`§22.2.2.2`) proved equal to `spec_match` and proved bounds-safe.
pub fn exec_match(
    ast: &RegexAst,
    flags: RegexFlags,
    input: &[u16],
    start_pos: usize,
    num_groups: usize,
    steps: usize,
) -> (out: MatchOutcome)
    ensures
        out@
            == spec_match(
                ast@,
                flags,
                input@,
                start_pos as nat,
                num_groups as nat,
                steps as nat,
            ),
        match out@ {
            SpecMatchOutcome::Matched { start_pos: sp, end_pos, captures } => {
                &&& sp == start_pos as nat
                &&& sp <= end_pos && end_pos <= input@.len()
                &&& captures.len() == num_groups as nat
                &&& forall|i: int|
                    0 <= i < captures.len() ==> match #[trigger] captures[i] {
                        Some((gs, ge)) => gs <= ge && ge <= input@.len(),
                        None => true,
                    }
            },
            _ => true,
        },
{
    proof {
        lemma_match_bounds_valid(
            ast@,
            flags,
            input@,
            start_pos as nat,
            num_groups as nat,
            steps as nat,
        );
    }
    if start_pos > input.len() {
        return MatchOutcome::NoMatch;
    }
    let mut caps: Vec<Option<(usize, usize)>> = Vec::new();
    let mut i: usize = 0;
    while i < num_groups
        invariant
            i <= num_groups,
            caps@.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> caps@[k].is_none(),
        decreases num_groups - i,
    {
        caps.push(None);
        i += 1;
    }
    let init_state = MatchState { pos: start_pos, captures: caps };
    let mut init_cont: Vec<ContOp> = Vec::new();
    init_cont.push(ContOp::Eval(clone_regex_ast(ast)));
    let init_choices: Vec<ChoicePoint> = Vec::new();
    proof {
        assert(spec_captures_view(init_state.captures@)
            =~= Seq::new(num_groups as nat, |_i: int| None));
        assert(spec_cont_view(init_cont@) =~= seq![SpecContOp::Eval(ast@)]);
        assert(spec_choices_view(init_choices@)
            =~= Seq::<(SpecMatchState, Seq<SpecContOp>)>::empty());
    }
    run_machine_exec(input, flags, start_pos, init_state, init_cont, init_choices, steps)
}

/// Exec unanchored search (`RegExpBuiltinExec` §22.2.5.2.2) proved equal to `spec_search_from`.
pub fn exec_search(
    ast: &RegexAst,
    flags: RegexFlags,
    input: &[u16],
    from_pos: usize,
    num_groups: usize,
    steps_per_pos: usize,
) -> (out: MatchOutcome)
    ensures
        out@
            == spec_search_from(
                ast@,
                flags,
                input@,
                from_pos as nat,
                num_groups as nat,
                steps_per_pos as nat,
            ),
{
    let n = input.len();
    if from_pos > n {
        return MatchOutcome::NoMatch;
    }
    let mut pos: usize = from_pos;
    loop
        invariant
            from_pos <= pos <= n,
            n == input@.len(),
            spec_search_from(
                ast@,
                flags,
                input@,
                from_pos as nat,
                num_groups as nat,
                steps_per_pos as nat,
            )
                == spec_search_from(
                    ast@,
                    flags,
                    input@,
                    pos as nat,
                    num_groups as nat,
                    steps_per_pos as nat,
                ),
        decreases (n + 1) - pos,
    {
        let res = exec_match(ast, flags, input, pos, num_groups, steps_per_pos);
        match res {
            MatchOutcome::Matched { .. } => return res,
            MatchOutcome::StepLimitExceeded => return MatchOutcome::StepLimitExceeded,
            MatchOutcome::NoMatch => {
                if pos == n {
                    proof {
                        assert(spec_search_from(
                            ast@,
                            flags,
                            input@,
                            (n + 1) as nat,
                            num_groups as nat,
                            steps_per_pos as nat,
                        ) == SpecMatchOutcome::NoMatch);
                    }
                    return MatchOutcome::NoMatch;
                }
                pos += 1;
            },
        }
    }
}

// =======================================================================================
// 6. Verified RegExp Pattern Parser (`parse_pattern` & `spec_parse_pattern`, §22.2.1)
// =======================================================================================

/// Parse hex escape `\xXX` or `\uXXXX` helper.
pub open spec fn spec_re_is_hex(c: u16) -> bool {
    (0x0030 <= c && c <= 0x0039) || (0x0041 <= c && c <= 0x0046) || (0x0061 <= c && c <= 0x0066)
}

pub open spec fn spec_re_hex_val(c: u16) -> u16 {
    if 0x0030 <= c && c <= 0x0039 {
        (c - 0x0030) as u16
    } else if 0x0041 <= c && c <= 0x0046 {
        (c - 0x0041 + 10) as u16
    } else {
        (c - 0x0061 + 10) as u16
    }
}

/// Parse decimal quantifier bound (`{n}` / `{n,m}`) over the full `u32` range.
pub open spec fn spec_parse_quant_uint(
    pat: Seq<u16>,
    pos: nat,
    acc: u32,
    has_digit: bool,
) -> Option<(u32, nat)>
    decreases (if pos <= pat.len() { pat.len() - pos } else { 0 }),
{
    if pos < pat.len() && 0x0030 <= pat[pos as int] && pat[pos as int] <= 0x0039 {
        let d = (pat[pos as int] - 0x0030) as u32;
        if acc as nat * 10 + d as nat > 0xFFFF_FFFFnat {
            None
        } else {
            spec_parse_quant_uint(pat, pos + 1, (acc * 10 + d) as u32, true)
        }
    } else if has_digit {
        Some((acc, pos))
    } else {
        None
    }
}

/// Parse single escaped character inside `[...]` or atom escape.
pub open spec fn spec_parse_class_escape_char(pat: Seq<u16>, pos: nat) -> Option<(u16, nat)> {
    if pos >= pat.len() {
        None
    } else {
        let e = pat[pos as int];
        if e == 0x006E {
            Some((0x000A, pos + 1))
        } else if e == 0x0072 {
            Some((0x000D, pos + 1))
        } else if e == 0x0074 {
            Some((0x0009, pos + 1))
        } else if e == 0x0066 {
            Some((0x000C, pos + 1))
        } else if e == 0x0076 {
            Some((0x000B, pos + 1))
        } else if e == 0x0030 {
            Some((0x0000, pos + 1))
        } else if e == 0x0078 {
            if pos + 3 <= pat.len()
                && spec_re_is_hex(pat[pos as int + 1])
                && spec_re_is_hex(pat[pos as int + 2])
            {
                let v = (spec_re_hex_val(pat[pos as int + 1]) * 16
                    + spec_re_hex_val(pat[pos as int + 2])) as u16;
                Some((v, pos + 3))
            } else {
                None
            }
        } else if e == 0x0075 {
            if pos + 5 <= pat.len()
                && spec_re_is_hex(pat[pos as int + 1])
                && spec_re_is_hex(pat[pos as int + 2])
                && spec_re_is_hex(pat[pos as int + 3])
                && spec_re_is_hex(pat[pos as int + 4])
            {
                let v = (spec_re_hex_val(pat[pos as int + 1]) * 4096
                    + spec_re_hex_val(pat[pos as int + 2]) * 256
                    + spec_re_hex_val(pat[pos as int + 3]) * 16
                    + spec_re_hex_val(pat[pos as int + 4])) as u16;
                Some((v, pos + 5))
            } else {
                None
            }
        } else {
            Some((e, pos + 1))
        }
    }
}

/// Parse one atom inside `[...]` returning `(single_char_opt, extra_ranges, next_pos)`.
pub open spec fn spec_parse_class_item(
    pat: Seq<u16>,
    pos: nat,
) -> Option<(Option<u16>, Seq<(u16, u16)>, nat)> {
    if pos >= pat.len() {
        None
    } else if pat[pos as int] == 0x005C {
        if pos + 1 >= pat.len() {
            None
        } else {
            let e = pat[pos as int + 1];
            if e == 0x0064 {
                Some((None, spec_class_ranges_d(), pos + 2))
            } else if e == 0x0044 {
                Some((None, spec_class_ranges_not_d(), pos + 2))
            } else if e == 0x0077 {
                Some((None, spec_class_ranges_w(), pos + 2))
            } else if e == 0x0057 {
                Some((None, spec_class_ranges_not_w(), pos + 2))
            } else if e == 0x0073 {
                Some((None, spec_class_ranges_s(), pos + 2))
            } else if e == 0x0053 {
                Some((None, spec_class_ranges_not_s(), pos + 2))
            } else if e == 0x0062 {
                Some((Some(0x0008u16), Seq::empty(), pos + 2))
            } else {
                match spec_parse_class_escape_char(pat, pos + 1) {
                    Some((ch, np)) => Some((Some(ch), Seq::empty(), np)),
                    None => None,
                }
            }
        }
    } else {
        Some((Some(pat[pos as int]), Seq::empty(), pos + 1))
    }
}

/// Parse character class body up to closing `]` (`0x005D`).
/// Per non-Annex-B ECMA-262 §22.2.1.1, a character-class escape (`\d`, `\D`, `\w`, `\W`, `\s`, `\S`)
/// on either side of `-` (when followed by non-`]`) is rejected as `None` (`SyntaxError`).
pub open spec fn spec_parse_char_class_body(
    pat: Seq<u16>,
    pos: nat,
) -> Option<(Seq<(u16, u16)>, nat)>
    decreases (if pos <= pat.len() { pat.len() - pos } else { 0 }),
{
    if pos >= pat.len() {
        None
    } else if pat[pos as int] == 0x005D {
        Some((Seq::empty(), pos + 1))
    } else {
        match spec_parse_class_item(pat, pos) {
            None => None,
            Some((maybe_lo, r_head, p1)) => {
                if p1 <= pos {
                    None
                } else if p1 + 1 < pat.len()
                    && pat[p1 as int] == 0x002D
                    && pat[p1 as int + 1] != 0x005D
                {
                    match maybe_lo {
                        None => None,
                        Some(lo) => match spec_parse_class_item(pat, p1 + 1) {
                            Some((Some(hi), _, p2)) => {
                                if lo > hi || p2 <= pos {
                                    None
                                } else {
                                    match spec_parse_char_class_body(pat, p2) {
                                        Some((rest, end_pos)) => {
                                            Some((seq![(lo, hi)] + rest, end_pos))
                                        },
                                        None => None,
                                    }
                                }
                            },
                            _ => None,
                        },
                    }
                } else {
                    let cur = match maybe_lo {
                        Some(ch) => seq![(ch, ch)],
                        None => r_head,
                    };
                    match spec_parse_char_class_body(pat, p1) {
                        Some((rest, end_pos)) => Some((cur + rest, end_pos)),
                        None => None,
                    }
                }
            },
        }
    }
}

/// Parse optional quantifier suffix (`*`, `+`, `?`, `{n}`, `{n,}`, `{n,m}` + lazy `?`).
pub open spec fn spec_parse_quantifier_suffix(
    pat: Seq<u16>,
    pos: nat,
    atom: SpecRegexAst,
) -> Option<(SpecRegexAst, nat)> {
    if pos >= pat.len() {
        Some((atom, pos))
    } else {
        let c = pat[pos as int];
        if c == 0x002A || c == 0x002B || c == 0x003F {
            let (min, max) = if c == 0x002A {
                (0u32, None)
            } else if c == 0x002B {
                (1u32, None)
            } else {
                (0u32, Some(1u32))
            };
            if pos + 1 < pat.len() && pat[pos as int + 1] == 0x003F {
                Some((
                    SpecRegexAst::Repeat {
                        sub: Box::new(atom),
                        min,
                        max,
                        greedy: false,
                    },
                    pos + 2,
                ))
            } else {
                Some((
                    SpecRegexAst::Repeat {
                        sub: Box::new(atom),
                        min,
                        max,
                        greedy: true,
                    },
                    pos + 1,
                ))
            }
        } else if c == 0x007B {
            match spec_parse_quant_uint(pat, pos + 1, 0, false) {
                None => None,
                Some((min_v, p1)) => {
                    if p1 >= pat.len() {
                        None
                    } else if pat[p1 as int] == 0x007D {
                        let p_end = p1 + 1;
                        let greedy = !(p_end < pat.len() && pat[p_end as int] == 0x003F);
                        let p_fin = if greedy { p_end } else { p_end + 1 };
                        Some((
                            SpecRegexAst::Repeat {
                                sub: Box::new(atom),
                                min: min_v,
                                max: Some(min_v),
                                greedy,
                            },
                            p_fin,
                        ))
                    } else if pat[p1 as int] == 0x002C {
                        if p1 + 1 < pat.len() && pat[p1 as int + 1] == 0x007D {
                            let p_end = p1 + 2;
                            let greedy = !(p_end < pat.len() && pat[p_end as int] == 0x003F);
                            let p_fin = if greedy { p_end } else { p_end + 1 };
                            Some((
                                SpecRegexAst::Repeat {
                                    sub: Box::new(atom),
                                    min: min_v,
                                    max: None,
                                    greedy,
                                },
                                p_fin,
                            ))
                        } else {
                            match spec_parse_quant_uint(pat, p1 + 1, 0, false) {
                                None => None,
                                Some((max_v, p2)) => {
                                    if p2 >= pat.len()
                                        || pat[p2 as int] != 0x007D
                                        || min_v > max_v
                                    {
                                        None
                                    } else {
                                        let p_end = p2 + 1;
                                        let greedy = !(p_end < pat.len()
                                            && pat[p_end as int] == 0x003F);
                                        let p_fin = if greedy { p_end } else { p_end + 1 };
                                        Some((
                                            SpecRegexAst::Repeat {
                                                sub: Box::new(atom),
                                                min: min_v,
                                                max: Some(max_v),
                                                greedy,
                                            },
                                            p_fin,
                                        ))
                                    }
                                },
                            }
                        }
                    } else {
                        None
                    }
                },
            }
        } else {
            Some((atom, pos))
        }
    }
}

pub open spec fn spec_is_quantifier_start(c: u16) -> bool {
    c == 0x002A || c == 0x002B || c == 0x003F || c == 0x007B
}

/// Fuel-bounded recursive-descent `Disjunction` parser (`a|b|c`).
pub open spec fn spec_parse_disjunction(
    pat: Seq<u16>,
    pos: nat,
    next_group: u32,
    fuel: nat,
) -> Option<(SpecRegexAst, nat, u32)>
    decreases fuel, 2nat,
{
    if fuel == 0 {
        None
    } else {
        match spec_parse_alternative(pat, pos, next_group, fuel) {
            None => None,
            Some((lhs, p1, g1)) => {
                if p1 < pat.len() && pat[p1 as int] == 0x007C {
                    match spec_parse_disjunction(pat, p1 + 1, g1, (fuel - 1) as nat) {
                        Some((rhs, p2, g2)) => {
                            Some((SpecRegexAst::Alt(Box::new(lhs), Box::new(rhs)), p2, g2))
                        },
                        None => None,
                    }
                } else {
                    Some((lhs, p1, g1))
                }
            },
        }
    }
}

/// Fuel-bounded `Alternative` parser (concatenation of terms up to `|`, `)`, or EOF).
pub open spec fn spec_parse_alternative(
    pat: Seq<u16>,
    pos: nat,
    next_group: u32,
    fuel: nat,
) -> Option<(SpecRegexAst, nat, u32)>
    decreases fuel, 1nat, (if pos <= pat.len() { pat.len() - pos } else { 0 }),
{
    if fuel == 0 {
        None
    } else if pos >= pat.len() || pat[pos as int] == 0x007C || pat[pos as int] == 0x0029 {
        Some((SpecRegexAst::Empty, pos, next_group))
    } else {
        match spec_parse_term(pat, pos, next_group, fuel) {
            None => None,
            Some((term, p1, g1)) => {
                if p1 <= pos {
                    None
                } else if p1 >= pat.len()
                    || pat[p1 as int] == 0x007C
                    || pat[p1 as int] == 0x0029
                {
                    Some((term, p1, g1))
                } else {
                    match spec_parse_alternative(pat, p1, g1, fuel) {
                        Some((rest, p2, g2)) => {
                            Some((SpecRegexAst::Seq(Box::new(term), Box::new(rest)), p2, g2))
                        },
                        None => None,
                    }
                }
            },
        }
    }
}

/// Parse one `Term` (assertion or quantified atom).
pub open spec fn spec_parse_term(
    pat: Seq<u16>,
    pos: nat,
    next_group: u32,
    fuel: nat,
) -> Option<(SpecRegexAst, nat, u32)>
    decreases fuel, 0nat,
{
    if fuel == 0 || pos >= pat.len() {
        None
    } else {
        let c = pat[pos as int];
        if c == 0x005E {
            if pos + 1 < pat.len() && spec_is_quantifier_start(pat[pos as int + 1]) {
                None
            } else {
                Some((SpecRegexAst::AnchorStart, pos + 1, next_group))
            }
        } else if c == 0x0024 {
            if pos + 1 < pat.len() && spec_is_quantifier_start(pat[pos as int + 1]) {
                None
            } else {
                Some((SpecRegexAst::AnchorEnd, pos + 1, next_group))
            }
        } else if c == 0x005C && pos + 1 < pat.len()
            && (pat[pos as int + 1] == 0x0062 || pat[pos as int + 1] == 0x0042)
        {
            let neg = pat[pos as int + 1] == 0x0042;
            if pos + 2 < pat.len() && spec_is_quantifier_start(pat[pos as int + 2]) {
                None
            } else {
                Some((SpecRegexAst::WordBoundary { negated: neg }, pos + 2, next_group))
            }
        } else if spec_is_quantifier_start(c) || c == 0x0029 || c == 0x007C {
            None
        } else {
            let atom_opt: Option<(SpecRegexAst, nat, u32)> = if c == 0x002E {
                Some((SpecRegexAst::Dot, pos + 1, next_group))
            } else if c == 0x0028 {
                if pos + 2 < pat.len()
                    && pat[pos as int + 1] == 0x003F
                    && pat[pos as int + 2] == 0x003A
                {
                    match spec_parse_disjunction(pat, pos + 3, next_group, (fuel - 1) as nat) {
                        Some((sub, p_end, g_after)) => {
                            if p_end < pat.len() && pat[p_end as int] == 0x0029 {
                                Some((sub, p_end + 1, g_after))
                            } else {
                                None
                            }
                        },
                        None => None,
                    }
                } else if next_group == u32::MAX {
                    None
                } else {
                    let g_idx: u32 = (next_group + 1) as u32;
                    match spec_parse_disjunction(pat, pos + 1, g_idx, (fuel - 1) as nat) {
                        Some((sub, p_end, g_after)) => {
                            if p_end < pat.len() && pat[p_end as int] == 0x0029 {
                                Some((
                                    SpecRegexAst::Group { index: g_idx, sub: Box::new(sub) },
                                    p_end + 1,
                                    g_after,
                                ))
                            } else {
                                None
                            }
                        },
                        None => None,
                    }
                }
            } else if c == 0x005B {
                let negated = pos + 1 < pat.len() && pat[pos as int + 1] == 0x005E;
                let body_start = if negated { pos + 2 } else { pos + 1 };
                match spec_parse_char_class_body(pat, body_start) {
                    Some((ranges, p_end)) => Some((
                        SpecRegexAst::CharClass { negated, ranges },
                        p_end,
                        next_group,
                    )),
                    None => None,
                }
            } else if c == 0x005C {
                if pos + 1 >= pat.len() {
                    None
                } else {
                    let e = pat[pos as int + 1];
                    if e == 0x0064 || e == 0x0044 {
                        Some((
                            SpecRegexAst::Digit { negated: e == 0x0044 },
                            pos + 2,
                            next_group,
                        ))
                    } else if e == 0x0077 || e == 0x0057 {
                        Some((
                            SpecRegexAst::Word { negated: e == 0x0057 },
                            pos + 2,
                            next_group,
                        ))
                    } else if e == 0x0073 || e == 0x0053 {
                        Some((
                            SpecRegexAst::Space { negated: e == 0x0053 },
                            pos + 2,
                            next_group,
                        ))
                    } else {
                        match spec_parse_class_escape_char(pat, pos + 1) {
                            Some((ch, p_end)) => {
                                Some((SpecRegexAst::Char(ch), p_end, next_group))
                            },
                            None => None,
                        }
                    }
                }
            } else {
                Some((SpecRegexAst::Char(c), pos + 1, next_group))
            };
            match atom_opt {
                None => None,
                Some((atom, p_atom, g_after)) => {
                    match spec_parse_quantifier_suffix(pat, p_atom, atom) {
                        Some((q_ast, p_fin)) => Some((q_ast, p_fin, g_after)),
                        None => None,
                    }
                },
            }
        }
    }
}

/// Top-level ECMA-262 §22.2.1 `ParsePattern` returning `(ast, num_groups)`.
pub open spec fn spec_parse_pattern(
    pat: Seq<u16>,
    fuel: nat,
) -> Option<(SpecRegexAst, u32)> {
    match spec_parse_disjunction(pat, 0, 0, fuel) {
        Some((ast, end_pos, groups)) => {
            if end_pos == pat.len() {
                Some((ast, groups))
            } else {
                None
            }
        },
        None => None,
    }
}

// ---------------------------------------------------------------------------------------
// Exec RegExp Pattern Parser (`parse_pattern` == `spec_parse_pattern`)
// ---------------------------------------------------------------------------------------

fn re_is_hex_exec(c: u16) -> (res: bool)
    ensures
        res == spec_re_is_hex(c),
{
    (c >= 0x0030 && c <= 0x0039) || (c >= 0x0041 && c <= 0x0046) || (c >= 0x0061 && c <= 0x0066)
}

fn re_hex_val_exec(c: u16) -> (v: u16)
    requires
        spec_re_is_hex(c),
    ensures
        v == spec_re_hex_val(c),
        v < 16,
{
    if c <= 0x0039 {
        c - 0x0030
    } else if c <= 0x0046 {
        c - 0x0041 + 10
    } else {
        c - 0x0061 + 10
    }
}

fn parse_quant_uint_exec(pat: &[u16], pos: usize) -> (res: Option<(u32, usize)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((v, end_pos)) => {
                &&& spec_parse_quant_uint(pat@, pos as nat, 0, false) == Some((v, end_pos as nat))
                &&& pos < end_pos <= pat@.len()
            },
            None => spec_parse_quant_uint(pat@, pos as nat, 0, false).is_none(),
        },
{
    let n = pat.len();
    let mut i: usize = pos;
    let mut acc: u32 = 0;
    let mut has_digit: bool = false;
    while i < n && pat[i] >= 0x0030 && pat[i] <= 0x0039
        invariant
            pos <= i <= n,
            n == pat@.len(),
            has_digit <==> (i > pos),
            spec_parse_quant_uint(pat@, pos as nat, 0, false)
                == spec_parse_quant_uint(pat@, i as nat, acc, has_digit),
        decreases n - i,
    {
        let d: u32 = (pat[i] - 0x0030) as u32;
        if acc > (0xFFFF_FFFFu32 - d) / 10 {
            proof {
                assert(acc as nat * 10 + d as nat > 0xFFFF_FFFFnat) by (nonlinear_arith)
                    requires
                        d < 10,
                        acc > (0xFFFF_FFFFu32 - d) / 10,
                ;
                assert(spec_parse_quant_uint(pat@, i as nat, acc, has_digit).is_none());
            }
            return None;
        }
        proof {
            assert(acc as nat * 10 + d as nat <= 0xFFFF_FFFFnat) by (nonlinear_arith)
                requires
                    d < 10,
                    acc <= (0xFFFF_FFFFu32 - d) / 10,
            ;
        }
        acc = acc * 10 + d;
        has_digit = true;
        i += 1;
    }
    if has_digit {
        Some((acc, i))
    } else {
        None
    }
}

fn parse_class_escape_char_exec(pat: &[u16], pos: usize) -> (res: Option<(u16, usize)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((ch, np)) => {
                &&& spec_parse_class_escape_char(pat@, pos as nat) == Some((ch, np as nat))
                &&& pos < np <= pat@.len()
            },
            None => spec_parse_class_escape_char(pat@, pos as nat).is_none(),
        },
{
    let n = pat.len();
    if pos >= n {
        return None;
    }
    let e = pat[pos];
    if e == 0x006E {
        Some((0x000A, pos + 1))
    } else if e == 0x0072 {
        Some((0x000D, pos + 1))
    } else if e == 0x0074 {
        Some((0x0009, pos + 1))
    } else if e == 0x0066 {
        Some((0x000C, pos + 1))
    } else if e == 0x0076 {
        Some((0x000B, pos + 1))
    } else if e == 0x0030 {
        Some((0x0000, pos + 1))
    } else if e == 0x0078 {
        if n - pos >= 3 && re_is_hex_exec(pat[pos + 1]) && re_is_hex_exec(pat[pos + 2]) {
            let v = re_hex_val_exec(pat[pos + 1]) * 16 + re_hex_val_exec(pat[pos + 2]);
            Some((v, pos + 3))
        } else {
            None
        }
    } else if e == 0x0075 {
        if n - pos >= 5
            && re_is_hex_exec(pat[pos + 1])
            && re_is_hex_exec(pat[pos + 2])
            && re_is_hex_exec(pat[pos + 3])
            && re_is_hex_exec(pat[pos + 4])
        {
            let v = re_hex_val_exec(pat[pos + 1]) * 4096
                + re_hex_val_exec(pat[pos + 2]) * 256
                + re_hex_val_exec(pat[pos + 3]) * 16
                + re_hex_val_exec(pat[pos + 4]);
            Some((v, pos + 5))
        } else {
            None
        }
    } else {
        Some((e, pos + 1))
    }
}

fn parse_class_item_exec(
    pat: &[u16],
    pos: usize,
) -> (res: Option<(Option<u16>, Vec<(u16, u16)>, usize)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((mc, rvec, np)) => {
                &&& spec_parse_class_item(pat@, pos as nat) == Some((mc, rvec@, np as nat))
                &&& pos < np <= pat@.len()
            },
            None => spec_parse_class_item(pat@, pos as nat).is_none(),
        },
{
    let n = pat.len();
    if pos >= n {
        return None;
    }
    if pat[pos] == 0x005C {
        if n - pos < 2 {
            return None;
        }
        let e = pat[pos + 1];
        if e == 0x0064 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0030, 0x0039));
            proof {
                assert(r@ =~= spec_class_ranges_d());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0044 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0000, 0x002F));
            r.push((0x003A, 0xFFFF));
            proof {
                assert(r@ =~= spec_class_ranges_not_d());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0077 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0030, 0x0039));
            r.push((0x0041, 0x005A));
            r.push((0x005F, 0x005F));
            r.push((0x0061, 0x007A));
            proof {
                assert(r@ =~= spec_class_ranges_w());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0057 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0000, 0x002F));
            r.push((0x003A, 0x0040));
            r.push((0x005B, 0x005E));
            r.push((0x0060, 0x0060));
            r.push((0x007B, 0xFFFF));
            proof {
                assert(r@ =~= spec_class_ranges_not_w());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0073 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0009, 0x000D));
            r.push((0x0020, 0x0020));
            r.push((0x00A0, 0x00A0));
            r.push((0x1680, 0x1680));
            r.push((0x2000, 0x200A));
            r.push((0x2028, 0x2029));
            r.push((0x202F, 0x202F));
            r.push((0x205F, 0x205F));
            r.push((0x3000, 0x3000));
            r.push((0xFEFF, 0xFEFF));
            proof {
                assert(r@ =~= spec_class_ranges_s());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0053 {
            let mut r: Vec<(u16, u16)> = Vec::new();
            r.push((0x0000, 0x0008));
            r.push((0x000E, 0x001F));
            r.push((0x0021, 0x009F));
            r.push((0x00A1, 0x167F));
            r.push((0x1681, 0x1FFF));
            r.push((0x200B, 0x2027));
            r.push((0x202A, 0x202E));
            r.push((0x2030, 0x205E));
            r.push((0x2060, 0x2FFF));
            r.push((0x3001, 0xFEFE));
            r.push((0xFF00, 0xFFFF));
            proof {
                assert(r@ =~= spec_class_ranges_not_s());
            }
            Some((None, r, pos + 2))
        } else if e == 0x0062 {
            let r: Vec<(u16, u16)> = Vec::new();
            proof {
                assert(r@ =~= Seq::<(u16, u16)>::empty());
            }
            Some((Some(0x0008), r, pos + 2))
        } else {
            match parse_class_escape_char_exec(pat, pos + 1) {
                Some((ch, np)) => {
                    let r: Vec<(u16, u16)> = Vec::new();
                    proof {
                        assert(r@ =~= Seq::<(u16, u16)>::empty());
                    }
                    Some((Some(ch), r, np))
                },
                None => None,
            }
        }
    } else {
        let r: Vec<(u16, u16)> = Vec::new();
        proof {
            assert(r@ =~= Seq::<(u16, u16)>::empty());
        }
        Some((Some(pat[pos]), r, pos + 1))
    }
}

fn parse_char_class_body_exec(pat: &[u16], pos: usize) -> (res: Option<(Vec<(u16, u16)>, usize)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((ranges, end_pos)) => {
                &&& spec_parse_char_class_body(pat@, pos as nat) == Some((ranges@, end_pos as nat))
                &&& pos < end_pos <= pat@.len()
            },
            None => spec_parse_char_class_body(pat@, pos as nat).is_none(),
        },
{
    let n = pat.len();
    let mut out: Vec<(u16, u16)> = Vec::new();
    let mut i: usize = pos;
    while i < n
        invariant
            pos <= i <= n,
            n == pat@.len(),
            match spec_parse_char_class_body(pat@, i as nat) {
                Some((rest, end_pos)) => {
                    spec_parse_char_class_body(pat@, pos as nat) == Some((out@ + rest, end_pos))
                },
                None => spec_parse_char_class_body(pat@, pos as nat).is_none(),
            },
        decreases n - i,
    {
        if pat[i] == 0x005D {
            proof {
                assert(spec_parse_char_class_body(pat@, i as nat)
                    == Some((Seq::<(u16, u16)>::empty(), (i + 1) as nat)));
                assert(out@ + Seq::<(u16, u16)>::empty() =~= out@);
            }
            return Some((out, i + 1));
        }
        let ghost prev_out = out@;
        match parse_class_item_exec(pat, i) {
            None => return None,
            Some((maybe_lo, r_head, p1)) => {
                if n - p1 >= 2
                    && pat[p1] == 0x002D
                    && pat[p1 + 1] != 0x005D
                {
                    match maybe_lo {
                        None => return None,
                        Some(lo) => match parse_class_item_exec(pat, p1 + 1) {
                            Some((Some(hi), _, p2)) => {
                                if lo > hi {
                                    return None;
                                }
                                out.push((lo, hi));
                                i = p2;
                                proof {
                                    if let Some((rest, _)) =
                                        spec_parse_char_class_body(pat@, i as nat)
                                    {
                                        assert(prev_out + (seq![(lo, hi)] + rest) =~= out@ + rest);
                                    }
                                }
                            },
                            _ => return None,
                        },
                    }
                } else {
                    match maybe_lo {
                        Some(ch) => {
                            out.push((ch, ch));
                            i = p1;
                            proof {
                                if let Some((rest, _)) = spec_parse_char_class_body(pat@, i as nat) {
                                    assert(prev_out + (seq![(ch, ch)] + rest) =~= out@ + rest);
                                }
                            }
                        },
                        None => {
                            let ghost rh_v = r_head@;
                            let rlen = r_head.len();
                            let mut k: usize = 0;
                            while k < rlen
                                invariant
                                    k <= rlen,
                                    rlen == r_head@.len(),
                                    rh_v == r_head@,
                                    out@ == prev_out + rh_v.subrange(0, k as int),
                                decreases rlen - k,
                            {
                                out.push(r_head[k]);
                                k += 1;
                                proof {
                                    assert(out@ =~= prev_out + rh_v.subrange(0, k as int));
                                }
                            }
                            i = p1;
                            proof {
                                assert(rh_v.subrange(0, rlen as int) =~= rh_v);
                                if let Some((rest, _)) = spec_parse_char_class_body(pat@, i as nat) {
                                    assert(prev_out + (rh_v + rest) =~= out@ + rest);
                                }
                            }
                        },
                    }
                }
            },
        }
    }
    None
}

fn parse_quantifier_suffix_exec(
    pat: &[u16],
    pos: usize,
    atom: RegexAst,
) -> (res: Option<(RegexAst, usize)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((q_ast, p_fin)) => {
                &&& spec_parse_quantifier_suffix(pat@, pos as nat, atom@)
                    == Some((q_ast@, p_fin as nat))
                &&& pos <= p_fin <= pat@.len()
            },
            None => spec_parse_quantifier_suffix(pat@, pos as nat, atom@).is_none(),
        },
{
    let n = pat.len();
    if pos >= n {
        return Some((atom, pos));
    }
    let c = pat[pos];
    if c == 0x002A || c == 0x002B || c == 0x003F {
        let (min, max) = if c == 0x002A {
            (0u32, None)
        } else if c == 0x002B {
            (1u32, None)
        } else {
            (0u32, Some(1u32))
        };
        if n - pos >= 2 && pat[pos + 1] == 0x003F {
            Some((
                RegexAst::Repeat { sub: Box::new(atom), min, max, greedy: false },
                pos + 2,
            ))
        } else {
            Some((
                RegexAst::Repeat { sub: Box::new(atom), min, max, greedy: true },
                pos + 1,
            ))
        }
    } else if c == 0x007B {
        match parse_quant_uint_exec(pat, pos + 1) {
            None => None,
            Some((min_v, p1)) => {
                if p1 >= n {
                    None
                } else if pat[p1] == 0x007D {
                    let p_end = p1 + 1;
                    let greedy = !(p_end < n && pat[p_end] == 0x003F);
                    let p_fin = if greedy { p_end } else { p_end + 1 };
                    Some((
                        RegexAst::Repeat {
                            sub: Box::new(atom),
                            min: min_v,
                            max: Some(min_v),
                            greedy,
                        },
                        p_fin,
                    ))
                } else if pat[p1] == 0x002C {
                    if n - p1 >= 2 && pat[p1 + 1] == 0x007D {
                        let p_end = p1 + 2;
                        let greedy = !(p_end < n && pat[p_end] == 0x003F);
                        let p_fin = if greedy { p_end } else { p_end + 1 };
                        Some((
                            RegexAst::Repeat {
                                sub: Box::new(atom),
                                min: min_v,
                                max: None,
                                greedy,
                            },
                            p_fin,
                        ))
                    } else {
                        match parse_quant_uint_exec(pat, p1 + 1) {
                            None => None,
                            Some((max_v, p2)) => {
                                if p2 >= n || pat[p2] != 0x007D || min_v > max_v {
                                    None
                                } else {
                                    let p_end = p2 + 1;
                                    let greedy = !(p_end < n && pat[p_end] == 0x003F);
                                    let p_fin = if greedy { p_end } else { p_end + 1 };
                                    Some((
                                        RegexAst::Repeat {
                                            sub: Box::new(atom),
                                            min: min_v,
                                            max: Some(max_v),
                                            greedy,
                                        },
                                        p_fin,
                                    ))
                                }
                            },
                        }
                    }
                } else {
                    None
                }
            },
        }
    } else {
        Some((atom, pos))
    }
}

fn is_quantifier_start_exec(c: u16) -> (res: bool)
    ensures
        res == spec_is_quantifier_start(c),
{
    c == 0x002A || c == 0x002B || c == 0x003F || c == 0x007B
}

fn parse_disjunction_exec(
    pat: &[u16],
    pos: usize,
    next_group: u32,
    fuel: usize,
) -> (res: Option<(RegexAst, usize, u32)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((ast, p_end, g_end)) => {
                &&& spec_parse_disjunction(pat@, pos as nat, next_group, fuel as nat)
                    == Some((ast@, p_end as nat, g_end))
                &&& pos <= p_end <= pat@.len()
            },
            None => spec_parse_disjunction(pat@, pos as nat, next_group, fuel as nat).is_none(),
        },
    decreases fuel, 2usize,
{
    if fuel == 0 {
        return None;
    }
    match parse_alternative_exec(pat, pos, next_group, fuel) {
        None => None,
        Some((lhs, p1, g1)) => {
            if p1 < pat.len() && pat[p1] == 0x007C {
                match parse_disjunction_exec(pat, p1 + 1, g1, fuel - 1) {
                    Some((rhs, p2, g2)) => {
                        Some((RegexAst::Alt(Box::new(lhs), Box::new(rhs)), p2, g2))
                    },
                    None => None,
                }
            } else {
                Some((lhs, p1, g1))
            }
        },
    }
}

fn parse_alternative_exec(
    pat: &[u16],
    pos: usize,
    next_group: u32,
    fuel: usize,
) -> (res: Option<(RegexAst, usize, u32)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((ast, p_end, g_end)) => {
                &&& spec_parse_alternative(pat@, pos as nat, next_group, fuel as nat)
                    == Some((ast@, p_end as nat, g_end))
                &&& pos <= p_end <= pat@.len()
            },
            None => spec_parse_alternative(pat@, pos as nat, next_group, fuel as nat).is_none(),
        },
    decreases fuel, 1usize, pat@.len() - pos,
{
    if fuel == 0 {
        return None;
    }
    let n = pat.len();
    if pos >= n || pat[pos] == 0x007C || pat[pos] == 0x0029 {
        return Some((RegexAst::Empty, pos, next_group));
    }
    match parse_term_exec(pat, pos, next_group, fuel) {
        None => None,
        Some((term, p1, g1)) => {
            if p1 >= n || pat[p1] == 0x007C || pat[p1] == 0x0029 {
                Some((term, p1, g1))
            } else {
                match parse_alternative_exec(pat, p1, g1, fuel) {
                    Some((rest, p2, g2)) => {
                        Some((RegexAst::Seq(Box::new(term), Box::new(rest)), p2, g2))
                    },
                    None => None,
                }
            }
        },
    }
}

fn parse_term_exec(
    pat: &[u16],
    pos: usize,
    next_group: u32,
    fuel: usize,
) -> (res: Option<(RegexAst, usize, u32)>)
    requires
        pos <= pat@.len(),
    ensures
        match res {
            Some((ast, p_end, g_end)) => {
                &&& spec_parse_term(pat@, pos as nat, next_group, fuel as nat)
                    == Some((ast@, p_end as nat, g_end))
                &&& pos < p_end <= pat@.len()
            },
            None => spec_parse_term(pat@, pos as nat, next_group, fuel as nat).is_none(),
        },
    decreases fuel, 0usize,
{
    let n = pat.len();
    if fuel == 0 || pos >= n {
        return None;
    }
    let c = pat[pos];
    if c == 0x005E {
        if n - pos >= 2 && is_quantifier_start_exec(pat[pos + 1]) {
            None
        } else {
            Some((RegexAst::AnchorStart, pos + 1, next_group))
        }
    } else if c == 0x0024 {
        if n - pos >= 2 && is_quantifier_start_exec(pat[pos + 1]) {
            None
        } else {
            Some((RegexAst::AnchorEnd, pos + 1, next_group))
        }
    } else if c == 0x005C && n - pos >= 2 && (pat[pos + 1] == 0x0062 || pat[pos + 1] == 0x0042) {
        let neg = pat[pos + 1] == 0x0042;
        if n - pos >= 3 && is_quantifier_start_exec(pat[pos + 2]) {
            None
        } else {
            Some((RegexAst::WordBoundary { negated: neg }, pos + 2, next_group))
        }
    } else if is_quantifier_start_exec(c) || c == 0x0029 || c == 0x007C {
        None
    } else {
        let atom_opt: Option<(RegexAst, usize, u32)> = if c == 0x002E {
            Some((RegexAst::Dot, pos + 1, next_group))
        } else if c == 0x0028 {
            if n - pos >= 3 && pat[pos + 1] == 0x003F && pat[pos + 2] == 0x003A {
                match parse_disjunction_exec(pat, pos + 3, next_group, fuel - 1) {
                    Some((sub, p_end, g_after)) => {
                        if p_end < n && pat[p_end] == 0x0029 {
                            Some((sub, p_end + 1, g_after))
                        } else {
                            None
                        }
                    },
                    None => None,
                }
            } else if next_group == u32::MAX {
                None
            } else {
                let g_idx = next_group + 1;
                match parse_disjunction_exec(pat, pos + 1, g_idx, fuel - 1) {
                    Some((sub, p_end, g_after)) => {
                        if p_end < n && pat[p_end] == 0x0029 {
                            Some((
                                RegexAst::Group { index: g_idx, sub: Box::new(sub) },
                                p_end + 1,
                                g_after,
                            ))
                        } else {
                            None
                        }
                    },
                    None => None,
                }
            }
        } else if c == 0x005B {
            let negated = n - pos >= 2 && pat[pos + 1] == 0x005E;
            let body_start = if negated { pos + 2 } else { pos + 1 };
            match parse_char_class_body_exec(pat, body_start) {
                Some((ranges, p_end)) => {
                    Some((RegexAst::CharClass { negated, ranges }, p_end, next_group))
                },
                None => None,
            }
        } else if c == 0x005C {
            if n - pos < 2 {
                None
            } else {
                let e = pat[pos + 1];
                if e == 0x0064 || e == 0x0044 {
                    Some((RegexAst::Digit { negated: e == 0x0044 }, pos + 2, next_group))
                } else if e == 0x0077 || e == 0x0057 {
                    Some((RegexAst::Word { negated: e == 0x0057 }, pos + 2, next_group))
                } else if e == 0x0073 || e == 0x0053 {
                    Some((RegexAst::Space { negated: e == 0x0053 }, pos + 2, next_group))
                } else {
                    match parse_class_escape_char_exec(pat, pos + 1) {
                        Some((ch, p_end)) => Some((RegexAst::Char(ch), p_end, next_group)),
                        None => None,
                    }
                }
            }
        } else {
            Some((RegexAst::Char(c), pos + 1, next_group))
        };
        match atom_opt {
            None => None,
            Some((atom, p_atom, g_after)) => {
                match parse_quantifier_suffix_exec(pat, p_atom, atom) {
                    Some((q_ast, p_fin)) => Some((q_ast, p_fin, g_after)),
                    None => None,
                }
            },
        }
    }
}

/// Exec ECMA-262 §22.2.1 `ParsePattern` proved equal to `spec_parse_pattern`.
pub fn parse_pattern(pat: &[u16], fuel: usize) -> (res: Option<(RegexAst, u32)>)
    ensures
        match res {
            Some((ast, groups)) => spec_parse_pattern(pat@, fuel as nat) == Some((ast@, groups)),
            None => spec_parse_pattern(pat@, fuel as nat).is_none(),
        },
{
    match parse_disjunction_exec(pat, 0, 0, fuel) {
        Some((ast, end_pos, groups)) => {
            if end_pos == pat.len() {
                Some((ast, groups))
            } else {
                None
            }
        },
        None => None,
    }
}

/// Helper: a 3-unit class body `[\<esc>]` parses to `expected` at depth 2.
proof fn lemma_single_escape_class_body(esc: u16, expected: Seq<(u16, u16)>)
    requires
        spec_parse_class_item(seq![0x005Cu16, esc, 0x005Du16], 0) == Some((None, expected, 2nat)),
    ensures
        spec_parse_char_class_body(seq![0x005Cu16, esc, 0x005Du16], 0)
            == Some((expected, 3nat)),
{
    let p = seq![0x005Cu16, esc, 0x005Du16];
    assert(spec_parse_char_class_body(p, 2) == Some((Seq::<(u16, u16)>::empty(), 3nat)));
    assert(expected + Seq::<(u16, u16)>::empty() =~= expected);
}

/// Parser-level verification of `[\d]`, `[\D]`, `[\w]`, `[\W]`, `[\s]`, `[\S]` and symmetric
/// rejection of class-set escapes on either side of `-` (`[\d-a]` and `[a-\d]`, §22.2.1.1).
#[verifier::spinoff_prover]
pub proof fn lemma_parsed_class_escapes_and_dash_errors()
    ensures
        spec_parse_char_class_body(seq![0x005Cu16, 0x0064u16, 0x005Du16], 0)
            == Some((spec_class_ranges_d(), 3nat)),
        spec_parse_char_class_body(seq![0x005Cu16, 0x0044u16, 0x005Du16], 0)
            == Some((spec_class_ranges_not_d(), 3nat)),
        spec_parse_char_class_body(seq![0x005Cu16, 0x0077u16, 0x005Du16], 0)
            == Some((spec_class_ranges_w(), 3nat)),
        spec_parse_char_class_body(seq![0x005Cu16, 0x0057u16, 0x005Du16], 0)
            == Some((spec_class_ranges_not_w(), 3nat)),
        spec_parse_char_class_body(seq![0x005Cu16, 0x0073u16, 0x005Du16], 0)
            == Some((spec_class_ranges_s(), 3nat)),
        spec_parse_char_class_body(seq![0x005Cu16, 0x0053u16, 0x005Du16], 0)
            == Some((spec_class_ranges_not_s(), 3nat)),
        spec_parse_char_class_body(
            seq![0x005Cu16, 0x0064u16, 0x002Du16, 0x0061u16, 0x005Du16],
            0,
        ).is_none(),
        spec_parse_char_class_body(
            seq![0x0061u16, 0x002Du16, 0x005Cu16, 0x0064u16, 0x005Du16],
            0,
        ).is_none(),
{
    lemma_single_escape_class_body(0x0064u16, spec_class_ranges_d());
    lemma_single_escape_class_body(0x0044u16, spec_class_ranges_not_d());
    lemma_single_escape_class_body(0x0077u16, spec_class_ranges_w());
    lemma_single_escape_class_body(0x0057u16, spec_class_ranges_not_w());
    lemma_single_escape_class_body(0x0073u16, spec_class_ranges_s());
    lemma_single_escape_class_body(0x0053u16, spec_class_ranges_not_s());
}

} // verus!
