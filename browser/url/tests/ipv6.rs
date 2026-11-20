//! IPv6: WPT urltestdata bracketed hosts, differential vs the `url` crate, and
//! serialize→parse round trips on random addresses.
use std::net::Ipv6Addr;
use vurl::ipv6::{ipv6_parse, ipv6_serialize};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
}

fn ser(pieces: &[u16]) -> String {
    String::from_utf8(ipv6_serialize(pieces)).unwrap()
}

#[test]
fn wpt_urltestdata_ipv6_hosts() {
    let data: serde_json::Value =
        serde_json::from_str(include_str!("data/urltestdata.json")).unwrap();
    let mut checked = 0;
    for t in data.as_array().unwrap().iter().filter(|t| t.is_object()) {
        let input = t["input"].as_str().unwrap();
        let Some((scheme, rest)) = input.split_once("://") else { continue };
        if !["http", "https", "ws", "wss", "ftp"].contains(&scheme) {
            continue;
        }
        let host = rest.strip_suffix('/').unwrap_or(rest);
        let Some(inner) = host.strip_prefix('[').and_then(|h| h.strip_suffix(']')) else { continue };
        if !inner.bytes().all(|b| b.is_ascii_hexdigit() || b == b':' || b == b'.') {
            continue;
        }
        let failure = t.get("failure").and_then(|f| f.as_bool()).unwrap_or(false);
        match ipv6_parse(inner.as_bytes()) {
            None => assert!(failure, "{input}: we reject, WPT expects {:?}", t["hostname"]),
            Some(p) => {
                assert!(!failure, "{input}: we parse {p:?}, WPT expects failure");
                assert_eq!(t["hostname"].as_str().unwrap(), format!("[{}]", ser(&p)), "{input}");
            }
        }
        checked += 1;
    }
    println!("WPT IPv6 host cases checked: {checked}");
    assert!(checked >= 15, "only {checked} WPT cases matched the filter");
}

#[test]
fn differential_ipv6_vs_url_crate() {
    let alphabet = b"0123456789abcdefABCDEF::::...";
    let mut rng = Lcg(0x1b6);
    let (mut ok, mut fail) = (0, 0);
    for _ in 0..300_000 {
        let len = 1 + (rng.next() % 24) as usize;
        let s: String =
            (0..len).map(|_| alphabet[(rng.next() % alphabet.len() as u64) as usize] as char).collect();
        let theirs = url::Host::parse(&format!("[{s}]"));
        match ipv6_parse(s.as_bytes()) {
            Some(p) => {
                ok += 1;
                let a = Ipv6Addr::from(<[u16; 8]>::try_from(p.as_slice()).unwrap());
                assert!(matches!(theirs, Ok(url::Host::Ipv6(b)) if b == a), "{s:?}: ours {a}, url {theirs:?}");
                // url's Display brackets the same serializer output
                assert_eq!(theirs.unwrap().to_string(), format!("[{}]", ser(&p)), "{s:?}");
            }
            None => {
                fail += 1;
                assert!(theirs.is_err(), "{s:?}: ours failure, url {theirs:?}")
            }
        }
    }
    println!("differential: {ok} parsed, {fail} failures");
    assert!(ok > 1000, "generator produced too few valid addresses ({ok})");
}

#[test]
fn serialize_parse_roundtrip_random() {
    let mut rng = Lcg(0xabc);
    for _ in 0..200_000 {
        // bias toward zeros so compression paths are exercised
        let p: Vec<u16> = (0..8)
            .map(|_| if rng.next() % 3 == 0 { 0 } else { (rng.next() & 0xffff) as u16 })
            .collect();
        let s = ser(&p);
        assert_eq!(ipv6_parse(s.as_bytes()), Some(p.clone()), "{s}");
    }
}

#[test]
fn spec_examples() {
    assert_eq!(ser(&[0x2001, 0xdb8, 0, 0, 0, 0, 0, 1]), "2001:db8::1");
    assert_eq!(ser(&[0, 0, 0, 0, 0, 0, 0, 0]), "::");
    assert_eq!(ser(&[1, 0, 0, 2, 0, 0, 0, 3]), "1:0:0:2::3");
    assert_eq!(ser(&[1, 0, 2, 3, 4, 5, 6, 7]), "1:0:2:3:4:5:6:7"); // a single 0 is not compressed
    assert_eq!(ipv6_parse(b"::ffff:192.168.0.1"), Some(vec![0, 0, 0, 0, 0, 0xffff, 0xc0a8, 0x0001]));
    assert_eq!(ipv6_parse(b"1:2:3:4:5:6:7:8:9"), None);
    assert_eq!(ipv6_parse(b"::1.2.3.04"), None); // leading zero in IPv4 part
    assert_eq!(ipv6_parse(b":1"), None);
}
