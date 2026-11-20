// CONDUIT irrigation controller, macOS host binary.
//
// `ctl.rs` holds the formally verified decision logic (inside `verus!`).
// `protocol.rs` and this file are ordinary, unverified I/O.
//
// Verify:  verus controller/irrigation.rs
// Build:   verus controller/irrigation.rs --compile -o <out>

extern crate alloc;

mod ctl;
mod protocol;

use std::io::{BufRead, Write};

fn main() {
    let mut c = ctl::Ctl::new(ctl::TANK_CAP);
    let mut out = std::io::stdout();
    let _ = writeln!(out, "{}", protocol::state_json(&c, true, "ready", "macos"));
    let _ = out.flush();
    for line in std::io::stdin().lock().lines() {
        let Ok(line) = line else { break };
        match protocol::handle(&mut c, &line, "macos") {
            Some(reply) => {
                let _ = writeln!(out, "{}", reply);
                let _ = out.flush();
            }
            None => break,
        }
    }
}
