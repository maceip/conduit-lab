// CONDUIT irrigation controller.
//
// The decision logic (which valves may open, how water leaves the tank, when a
// zone is forced closed) lives inside `verus!` and is formally verified against
// `Ctl::inv()`. The text protocol in `main` is ordinary, unverified Rust I/O.
//
// Verify:  verus controller/irrigation.rs
// Build:   verus controller/irrigation.rs --compile -o <out>
//
// Protocol (one command per line on stdin, one reply line on stdout):
//   open <z> | close <z> | tick | refill <liters> | state
// Every reply is the full state as a single JSON object.

use vstd::prelude::*;

verus! {

pub const NZONES: usize = 4;
/// The pump can feed at most this many zones at once.
pub const MAX_OPEN: u64 = 2;
/// A zone is forced closed after this many consecutive ticks.
pub const MAX_RUN: u64 = 30;
/// Liters drawn from the tank per open zone per tick.
pub const FLOW: u64 = 5;
/// Tank capacity in liters.
pub const TANK_CAP: u64 = 1000;

pub struct Ctl {
    pub open: [bool; 4],
    pub run: [u64; 4],
    pub delivered: [u64; 4],
    pub tank: u64,
    pub ticks: u64,
}

pub open spec fn b2i(b: bool) -> int {
    if b { 1 } else { 0 }
}

pub open spec fn count_open(open: [bool; 4]) -> int {
    b2i(open@[0]) + b2i(open@[1]) + b2i(open@[2]) + b2i(open@[3])
}

impl Ctl {
    /// Safety invariant, preserved by every operation:
    ///  - never more zones open than the pump can feed
    ///  - the tank holds enough water for the next tick of every open zone
    ///  - no zone runs longer than MAX_RUN; closed zones have no run time
    pub open spec fn inv(&self) -> bool {
        &&& count_open(self.open) <= MAX_OPEN
        &&& self.tank <= TANK_CAP
        &&& self.tank >= count_open(self.open) * FLOW
        &&& forall|i: int| 0 <= i < 4 ==> self.run@[i] < MAX_RUN
        &&& forall|i: int| 0 <= i < 4 ==> (!self.open@[i] ==> self.run@[i] == 0)
        &&& forall|i: int| 0 <= i < 4 ==> self.delivered@[i] <= self.ticks * FLOW
    }

    pub fn new(tank: u64) -> (c: Ctl)
        requires tank <= TANK_CAP,
        ensures c.inv(), count_open(c.open) == 0, c.tank == tank,
    {
        Ctl { open: [false; 4], run: [0; 4], delivered: [0; 4], tank, ticks: 0 }
    }

    pub fn n_open(&self) -> (n: u64)
        ensures n == count_open(self.open),
    {
        (if self.open[0] { 1u64 } else { 0 }) + (if self.open[1] { 1u64 } else { 0 })
            + (if self.open[2] { 1u64 } else { 0 }) + (if self.open[3] { 1u64 } else { 0 })
    }

    /// Request to open zone `z`. Granted only if it keeps the invariant.
    pub fn open_zone(&mut self, z: usize) -> (granted: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).ticks == old(self).ticks,
            granted ==> z < 4 && final(self).open@[z as int],
            !granted ==> final(self).open == old(self).open && final(self).tank == old(self).tank,
    {
        if z >= NZONES || self.open[z] {
            return false;
        }
        let n = self.n_open();
        if n + 1 > MAX_OPEN || self.tank < (n + 1) * FLOW {
            return false;
        }
        self.open[z] = true;
        self.run[z] = 0;
        proof {
            assert(count_open(self.open) == count_open(old(self).open) + 1);
        }
        true
    }

    pub fn close_zone(&mut self, z: usize) -> (closed: bool)
        requires old(self).inv(),
        ensures
            final(self).inv(),
            final(self).ticks == old(self).ticks,
            closed ==> z < 4 && !final(self).open@[z as int],
            count_open(final(self).open) <= count_open(old(self).open),
    {
        if z >= NZONES || !self.open[z] {
            return false;
        }
        self.open[z] = false;
        self.run[z] = 0;
        proof {
            assert(count_open(self.open) == count_open(old(self).open) - 1);
        }
        true
    }

    /// Add water to the tank, saturating at capacity.
    pub fn refill(&mut self, liters: u64)
        requires old(self).inv(),
        ensures final(self).inv(), final(self).tank >= old(self).tank, final(self).open == old(self).open,
    {
        let room = TANK_CAP - self.tank;
        let add = if liters < room { liters } else { room };
        self.tank = self.tank + add;
    }

    /// Advance one tick: every open zone draws FLOW liters, then zones that hit
    /// MAX_RUN, or that the remaining water cannot feed next tick, are closed.
    /// Returns the liters drawn this tick.
    pub fn tick(&mut self) -> (drawn: u64)
        requires old(self).inv(), old(self).ticks < u64::MAX / FLOW - 1,
        ensures
            final(self).inv(),
            final(self).ticks == old(self).ticks + 1,
            drawn == count_open(old(self).open) * FLOW,
            final(self).tank == old(self).tank - drawn,
    {
        let drawn = self.n_open() * FLOW;
        self.tank = self.tank - drawn;
        self.ticks = self.ticks + 1;
        let mut i: usize = 0;
        while i < NZONES
            invariant
                0 <= i <= 4,
                self.ticks == old(self).ticks + 1,
                self.tank == old(self).tank - drawn,
                drawn == count_open(old(self).open) * FLOW,
                self.open == old(self).open,
                old(self).ticks < u64::MAX / FLOW - 1,
                forall|j: int| 0 <= j < 4 ==> old(self).delivered@[j] <= old(self).ticks * FLOW,
                forall|j: int| 0 <= j < 4 ==> old(self).run@[j] < MAX_RUN,
                forall|j: int| 0 <= j < 4 ==> (!old(self).open@[j] ==> old(self).run@[j] == 0),
                forall|j: int| 0 <= j < i ==> self.run@[j] <= MAX_RUN,
                forall|j: int| 0 <= j < i ==> (!self.open@[j] ==> self.run@[j] == 0),
                forall|j: int| 0 <= j < i ==> self.delivered@[j] <= self.ticks * FLOW,
                forall|j: int| i <= j < 4 ==> self.run@[j] == old(self).run@[j],
                forall|j: int| i <= j < 4 ==> self.delivered@[j] == old(self).delivered@[j],
            decreases 4 - i,
        {
            if self.open[i] {
                let r = self.run[i] + 1;
                self.run[i] = r;
                let d = self.delivered[i] + FLOW;
                self.delivered[i] = d;
            }
            i = i + 1;
        }
        // Force-close zones at MAX_RUN.
        let mut k: usize = 0;
        while k < NZONES
            invariant
                0 <= k <= 4,
                self.ticks == old(self).ticks + 1,
                self.tank == old(self).tank - drawn,
                drawn == count_open(old(self).open) * FLOW,
                count_open(self.open) <= count_open(old(self).open),
                count_open(old(self).open) <= MAX_OPEN,
                old(self).tank <= TANK_CAP,
                forall|j: int| 0 <= j < 4 ==> self.run@[j] <= MAX_RUN,
                forall|j: int| 0 <= j < 4 ==> (!self.open@[j] ==> self.run@[j] == 0),
                forall|j: int| 0 <= j < k ==> self.run@[j] < MAX_RUN,
                forall|j: int| 0 <= j < 4 ==> self.delivered@[j] <= self.ticks * FLOW,
            decreases 4 - k,
        {
            if self.run[k] >= MAX_RUN {
                self.open[k] = false;
                self.run[k] = 0;
            }
            k = k + 1;
        }
        // Close zones (highest index first) until the tank can feed the rest next tick.
        let mut z: usize = NZONES;
        while self.tank < self.n_open() * FLOW && z > 0
            invariant
                0 <= z <= 4,
                self.ticks == old(self).ticks + 1,
                self.tank == old(self).tank - drawn,
                drawn == count_open(old(self).open) * FLOW,
                count_open(self.open) <= MAX_OPEN,
                old(self).tank <= TANK_CAP,
                forall|j: int| z <= j < 4 ==> !self.open@[j],
                forall|j: int| 0 <= j < 4 ==> self.run@[j] < MAX_RUN,
                forall|j: int| 0 <= j < 4 ==> (!self.open@[j] ==> self.run@[j] == 0),
                forall|j: int| 0 <= j < 4 ==> self.delivered@[j] <= self.ticks * FLOW,
            decreases z,
        {
            z = z - 1;
            if self.open[z] {
                self.open[z] = false;
                self.run[z] = 0;
            }
        }
        proof {
            if self.tank < count_open(self.open) * FLOW {
                assert(z == 0);
                assert(count_open(self.open) == 0);
            }
        }
        drawn
    }
}

} // verus!

fn state_json(c: &Ctl, ok: bool, msg: &str) -> String {
    let b = |v: &[bool; 4]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    let n = |v: &[u64; 4]| v.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
    format!(
        "{{\"ok\":{},\"msg\":\"{}\",\"open\":[{}],\"run\":[{}],\"delivered\":[{}],\"tank\":{},\"ticks\":{},\"limits\":{{\"zones\":{},\"max_open\":{},\"max_run\":{},\"flow\":{},\"tank_cap\":{}}}}}",
        ok, msg, b(&c.open), n(&c.run), n(&c.delivered), c.tank, c.ticks,
        NZONES, MAX_OPEN, MAX_RUN, FLOW, TANK_CAP
    )
}

fn main() {
    use std::io::{BufRead, Write};
    let mut c = Ctl::new(TANK_CAP);
    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    let _ = writeln!(out, "{}", state_json(&c, true, "ready"));
    let _ = out.flush();
    for line in stdin.lock().lines() {
        let Ok(line) = line else { break };
        let mut parts = line.split_whitespace();
        let cmd = parts.next().unwrap_or("");
        let arg = parts.next().and_then(|s| s.parse::<u64>().ok());
        let (ok, msg) = match (cmd, arg) {
            ("open", Some(z)) => {
                let g = c.open_zone(z as usize);
                (g, if g { "opened" } else { "denied" })
            }
            ("close", Some(z)) => {
                let g = c.close_zone(z as usize);
                (g, if g { "closed" } else { "not open" })
            }
            ("tick", _) if c.ticks < u64::MAX / FLOW - 1 => {
                c.tick();
                (true, "tick")
            }
            ("refill", Some(l)) => {
                c.refill(l);
                (true, "refilled")
            }
            ("state", _) => (true, "state"),
            ("quit", _) => break,
            _ => (false, "bad command"),
        };
        let _ = writeln!(out, "{}", state_json(&c, ok, msg));
        let _ = out.flush();
    }
}
