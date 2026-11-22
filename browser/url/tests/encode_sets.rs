//! Pins every byte of every percent-encode set. The proofs show `in_set` == `spec_in_set`, so they
//! cannot notice a member missing from *both*; these tests compare against oracles that share no
//! code with either.
//!
//! 1. `tables`: the ASCII members of all 8 sets, written out from whatwg/url@4f461b81 §1.3 as literal
//!    characters (not as nested set formulas).
//! 2. The `url`, `form_urlencoded` and `percent-encoding` crates, through their public APIs. Only
//!    CONTROLS is exported as a set constant, so the others are observed through URL behaviour.
use percent_encoding::{percent_encode as their_encode, CONTROLS};
use vurl::percent::{in_set, percent_encode, EncodeSet};

const ALL: [EncodeSet; 8] = [
    EncodeSet::C0Control,
    EncodeSet::Fragment,
    EncodeSet::Query,
    EncodeSet::SpecialQuery,
    EncodeSet::Path,
    EncodeSet::Userinfo,
    EncodeSet::Component,
    EncodeSet::FormUrlencoded,
];

/// Members among U+0020..=U+007E. C0 controls, U+007F and everything above are in every set.
fn printable_members(set: EncodeSet) -> &'static [u8] {
    match set {
        EncodeSet::C0Control => b"",
        EncodeSet::Fragment => b" \"<>`",
        EncodeSet::Query => b" \"#<>",
        EncodeSet::SpecialQuery => b" \"#<>'",
        EncodeSet::Path => b" \"#<>?^`{}",
        EncodeSet::Userinfo => b" \"#<>?^`{}/:;=@[\\]|",
        EncodeSet::Component => b" \"#<>?^`{}/:;=@[\\]|$%&+,",
        EncodeSet::FormUrlencoded => b" \"#<>?^`{}/:;=@[\\]|$%&+,!'()~",
    }
}

#[test]
fn tables_pin_all_8_sets_for_all_256_bytes() {
    for set in ALL {
        for b in 0u8..=255 {
            let want = b <= 0x1F || b >= 0x7F || printable_members(set).contains(&b);
            assert_eq!(in_set(set, b), want, "{set:?} byte {b:#04x}");
            let enc = if want { format!("%{b:02X}").into_bytes() } else { vec![b] };
            assert_eq!(percent_encode(&[b], set), enc, "{set:?} byte {b:#04x}");
        }
    }
}

#[test]
fn c0_control_matches_percent_encoding_crate() {
    for b in 0u8..=255 {
        let theirs = their_encode(&[b], CONTROLS).to_string().into_bytes();
        assert_eq!(percent_encode(&[b], EncodeSet::C0Control), theirs, "byte {b:#04x}");
    }
}

#[test]
fn form_urlencoded_matches_form_urlencoded_crate() {
    for b in (0u8..=255).filter(|&b| b != b' ') {
        // byte_serialize uses spaceAsPlus = true; vurl models spaceAsPlus = false, so skip U+0020.
        let theirs: String = url::form_urlencoded::byte_serialize(&[b]).collect();
        assert_eq!(percent_encode(&[b], EncodeSet::FormUrlencoded), theirs.into_bytes(), "byte {b:#04x}");
    }
}

/// Bytes in U+0021..=U+007E where `url` and `vurl` disagree about encoding. `parse` returns the
/// serialized component for the one-character input, or None if the character ends the component.
fn disagreements(set: EncodeSet, skip: &str, parse: impl Fn(char) -> Option<String>) -> (usize, String) {
    let (mut checked, mut diff) = (0, String::new());
    for b in 0x21u8..=0x7E {
        let c = b as char;
        if skip.contains(c) {
            continue;
        }
        let theirs = parse(c).unwrap_or_else(|| panic!("{set:?}: url crate gave no component for {c:?}"));
        checked += 1;
        if theirs.into_bytes() != percent_encode(&[b], set) {
            diff.push(c);
        }
    }
    (checked, diff)
}

fn parse(s: String) -> url::Url {
    url::Url::parse(&s).unwrap_or_else(|e| panic!("{s:?}: {e}"))
}

#[test]
fn url_crate_agrees_on_fragment_and_query_sets() {
    // '#' starts the fragment, so it can never reach the query encoder.
    let frag = disagreements(EncodeSet::Fragment, "", |c| parse(format!("http://h/#{c}")).fragment().map(Into::into));
    assert_eq!(frag, (94, String::new()));
    let special =
        disagreements(EncodeSet::SpecialQuery, "#", |c| parse(format!("http://h/?{c}")).query().map(Into::into));
    assert_eq!(special, (93, String::new()));
    let query = disagreements(EncodeSet::Query, "#", |c| parse(format!("x://h/?{c}")).query().map(Into::into));
    assert_eq!(query, (93, String::new()));
}

#[test]
fn url_crate_agrees_on_path_set_except_caret() {
    // '#' and '?' end the path, '/' and '\' separate segments, so none reaches the path encoder.
    // url 2.5.8 predates U+005E (^) joining the path set; if an upgrade fixes it, update this.
    let path = disagreements(EncodeSet::Path, "#?/\\", |c| {
        parse(format!("http://h/a{c}")).path().strip_prefix("/a").map(Into::into)
    });
    assert_eq!(path, (90, "^".to_string()));
}

#[test]
fn url_crate_agrees_on_userinfo_set() {
    let userinfo = disagreements(EncodeSet::Userinfo, "", |c| {
        let mut u = parse("http://h/".into());
        u.set_username(&c.to_string()).ok()?;
        Some(u.username().into())
    });
    assert_eq!(userinfo, (94, String::new()));
}
