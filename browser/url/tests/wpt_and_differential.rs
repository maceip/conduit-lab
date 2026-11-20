//! Tests the verified code against (1) the WPT URL test suite, pinned in tests/data, and
//! (2) the `url` / `percent-encoding` crates as independent implementations of the same spec.
use std::net::Ipv4Addr;
use vurl::ipv4::{ends_in_a_number, ipv4_parse};
use vurl::percent::{percent_decode, percent_encode, EncodeSet};

/// The host parser's IPv4 branch: Some(Some(addr)) = IPv4, Some(None) = failure, None = not IPv4.
fn host_ipv4(host: &str) -> Option<Option<Ipv4Addr>> {
    let h = host.to_ascii_lowercase(); // domain-to-ASCII on ASCII input lowercases
    if h.is_empty() || !ends_in_a_number(h.as_bytes()) {
        return None;
    }
    Some(ipv4_parse(h.as_bytes()).map(Ipv4Addr::from))
}

#[test]
fn wpt_urltestdata_ipv4_hosts() {
    let data: serde_json::Value =
        serde_json::from_str(include_str!("data/urltestdata.json")).unwrap();
    let mut checked = 0;
    for t in data.as_array().unwrap().iter().filter(|t| t.is_object()) {
        let input = t["input"].as_str().unwrap();
        // Only inputs that are exactly "<special scheme>://<ASCII host>[/]", so the host parser's
        // result alone decides the outcome.
        let Some((scheme, rest)) = input.split_once("://") else { continue };
        if !["http", "https", "ws", "wss", "ftp"].contains(&scheme) {
            continue;
        }
        let host = rest.strip_suffix('/').unwrap_or(rest);
        if host.is_empty() || !host.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'.') {
            continue;
        }
        let Some(ours) = host_ipv4(host) else { continue };
        let failure = t.get("failure").and_then(|f| f.as_bool()).unwrap_or(false);
        match ours {
            None => assert!(failure, "{input}: we reject, WPT expects {:?}", t["hostname"]),
            Some(a) => {
                assert!(!failure, "{input}: we parse {a}, WPT expects failure");
                assert_eq!(t["hostname"].as_str().unwrap(), a.to_string(), "{input}");
            }
        }
        checked += 1;
    }
    println!("WPT IPv4 host cases checked: {checked}");
    assert!(checked >= 20, "only {checked} WPT cases matched the filter");
}

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
}

#[test]
fn differential_ipv4_vs_url_crate() {
    let alphabet = b"0123456789abcdefxX.";
    let mut rng = Lcg(0x5eed);
    let (mut ipv4, mut fail, mut domain) = (0, 0, 0);
    for _ in 0..300_000 {
        let len = 1 + (rng.next() % 14) as usize;
        let s: String =
            (0..len).map(|_| alphabet[(rng.next() % alphabet.len() as u64) as usize] as char).collect();
        let theirs = url::Host::parse(&s);
        match host_ipv4(&s) {
            Some(Some(a)) => {
                ipv4 += 1;
                assert!(matches!(theirs, Ok(url::Host::Ipv4(b)) if b == a), "{s:?}: ours {a}, url {theirs:?}")
            }
            Some(None) => {
                fail += 1;
                assert!(theirs.is_err(), "{s:?}: ours failure, url {theirs:?}")
            }
            None => {
                domain += 1;
                assert!(!matches!(theirs, Ok(url::Host::Ipv4(_))), "{s:?}: ours not-IPv4, url {theirs:?}")
            }
        }
    }
    println!("differential: {ipv4} ipv4, {fail} failures, {domain} non-ipv4");
}

#[test]
fn differential_percent_decode_vs_crate() {
    let alphabet = b"%%%0123456789abcdefABCDEFgG\x00\xff";
    let mut rng = Lcg(0xdec0de);
    for _ in 0..200_000 {
        let len = (rng.next() % 10) as usize;
        let s: Vec<u8> = (0..len).map(|_| alphabet[(rng.next() % alphabet.len() as u64) as usize]).collect();
        let theirs: Vec<u8> = percent_encoding::percent_decode(&s).collect();
        assert_eq!(percent_decode(&s), theirs, "{s:?}");
    }
}

#[test]
fn component_set_matches_encode_uri_component() {
    // encodeURIComponent leaves exactly A-Z a-z 0-9 - _ . ! ~ * ' ( ) unescaped.
    for b in 0u8..=255 {
        let out = percent_encode(&[b], EncodeSet::Component);
        let unescaped = b.is_ascii_alphanumeric() || b"-_.!~*'()".contains(&b);
        assert_eq!(out == vec![b], unescaped, "byte {b:#04x} -> {out:?}");
    }
}

#[test]
fn spec_examples() {
    assert_eq!(ipv4_parse(b"0x7f.1"), Some(0x7f00_0001));
    assert_eq!(ipv4_parse(b"192.168.0.1."), Some(0xc0a8_0001));
    assert_eq!(ipv4_parse(b"1.2.3.4.5"), None);
    assert_eq!(ipv4_parse(b"256.0.0.1"), None);
    assert_eq!(ipv4_parse(b"4294967295"), Some(u32::MAX));
    assert_eq!(ipv4_parse(b"4294967296"), None);
    assert_eq!(percent_decode(b"%41%zz%4"), b"A%zz%4");
    assert_eq!(percent_encode(b"a b%", EncodeSet::Component), b"a%20b%25");
}
