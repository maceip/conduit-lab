import { writeCadFigure } from "./iso-cad.mjs";

export function buildShowcases() {
  // ==========================================================================
  // SHOWCASE A: High-Bypass Aircraft Turbofan Jet Engine (Aerospace CAD)
  // ==========================================================================
  writeCadFigure({
    slug: "showcase-01-jet-engine",
    fig: "Aero 1",
    title: "High-Bypass Turbofan Jet Engine · 9.6:1 BPR",
    hint: "click cutaway cowl · spool fan · reverse thrust · drag to orbit",
    initialReadout: "cutaway open · n1 88% · 18-blade fan · 340 kN thrust",
    ariaLabel:
      "Interactive 3D isometric high-bypass aircraft turbofan jet engine with cutaway bypass nacelle, 18 pitched wide-chord fan blades, multi-stage axial compressor, annular combustor cans, turbine stages, chevron core nozzle, and translating thrust reverser.",
    footHelp:
      "Click parts or keys: <kbd>C</kbd> toggle cutaway cowling · <kbd>S</kbd> / <kbd>Space</kbd> spool fan &amp; core · <kbd>R</kbd> deploy thrust reverser sleeve · <kbd>I</kbd> toggle combustor ignition · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit in 3D.",
    azDeg: 38,
    elDeg: 27,
    sceneJs: `
const st = { cutaway: true, spinDeg: 14, rpmPct: 88, rev: false, ignited: true };
const KM = { c: 'cowl', ' ': 'spool', s: 'spool', r: 'rev', i: 'ign' };

function act(k) {
  if (k === 'cowl') st.cutaway = !st.cutaway;
  else if (k === 'spool') { st.spinDeg = (st.spinDeg + 19) % 360; st.rpmPct = st.rpmPct >= 102 ? 62 : st.rpmPct + 14; }
  else if (k === 'rev') st.rev = !st.rev;
  else if (k === 'ign') st.ignited = !st.ignited;
  redraw(false);
}

function buildScene(cad) {
  const spinRad = (st.spinDeg * Math.PI) / 180;

  // 1. Overhead Wing Pylon Strut (swept aerodynamic pylon profile)
  cad.extrudePoly(
    [[-55, 62], [75, 62], [115, 96], [-18, 96]],
    { origin: [0, -7, 0], uAxis: [1, 0, 0], vAxis: [0, 0, 1], wAxis: [0, 1, 0], depth: 14, tone: 'dark' }
  );

  // 2. Central Core Shaft + Conical Nose Spinner
  cad.cyl([-128, 0, 0], [148, 0, 0], 11, 9, { segs: 20, tone: 'dark' });
  cad.revolve(
    [[-158, 0.4], [-148, 8], [-134, 17], [-120, 22, true], [-120, 0.5]],
    { axis: 'x', segs: 26, tone: 'hi', key: 'spool' }
  );

  // 3. 18 Pitched Titanium Wide-Chord Turbofan Blades (arrayed around X-axis!)
  const bladeCount = 18;
  for (let i = 0; i < bladeCount; i++) {
    const a = spinRad + (i * Math.PI * 2) / bladeCount;
    cad.push(cad.mRotX(a));
    cad.push(cad.mTrans(-112, 0, 21));
    cad.push(cad.mRotZ(0.46)); // aerodynamic blade twist
    cad.extrudePoly(
      [[-8, 0], [7, -1.5], [9, 39], [-5, 41]],
      { origin: [0, -1.3, 0], uAxis: [1, 0, 0], vAxis: [0, 0, 1], wAxis: [0, 1, 0], depth: 2.6, tone: i % 3 === 0 ? 'hi' : 'body', key: 'spool' }
    );
    cad.pop(); cad.pop(); cad.pop();
  }

  // 4. Multi-Stage Axial LP/HP Compressor Drum & Bladed Stages (x = -86 .. -8)
  cad.revolve(
    [[-92, 24], [-70, 27, true], [-46, 30, true], [-22, 31, true], [-4, 28]],
    { axis: 'x', segs: 24, ribRings: [0, 1, 2, 3], tone: 'body' }
  );
  for (let stg = 0; stg < 5; stg++) {
    const sx = -84 + stg * 16;
    const rOut = 43 - stg * 1.8;
    const nBlades = 14;
    for (let b = 0; b < nBlades; b++) {
      const ba = -spinRad * 0.7 + stg * 0.3 + (b * Math.PI * 2) / nBlades;
      cad.push(cad.mRotX(ba));
      cad.box3(sx, -1.1, 27, 6.5, 2.2, rOut - 27, { tone: stg % 2 === 0 ? 'hi' : 'body' });
      cad.pop();
    }
  }

  // 5. Annular Combustor Chamber + 10 Cylindrical Fuel-Burner Cans (x = -2 .. +44)
  cad.cyl([-4, 0, 0], [44, 0, 0], 27, 26, { segs: 22, tone: 'dark' });
  for (let c = 0; c < 10; c++) {
    const ca = (c * Math.PI * 2) / 10;
    const cy = Math.cos(ca) * 33, cz = Math.sin(ca) * 33;
    cad.cyl([-1, cy, cz], [39, cy * 0.94, cz * 0.94], 5.6, 4.8, {
      segs: 12,
      tone: st.ignited ? 'hi' : 'body',
      liveStroke: st.ignited,
      key: 'ign',
    });
  }

  // 6. HP & LP Turbine Stages (x = 48 .. 94) + Core Cowl & Exhaust Tailcone
  for (let t = 0; t < 3; t++) {
    const tx = 50 + t * 15;
    for (let b = 0; b < 14; b++) {
      const ba = spinRad * 1.2 + t * 0.25 + (b * Math.PI * 2) / 14;
      cad.push(cad.mRotX(ba));
      cad.box3(tx, -1, 24, 6, 2, 15 + t * 2.5, { tone: 'hi' });
      cad.pop();
    }
  }
  // Core inner cowling aft section + Exhaust Mixer Cone
  cad.revolve(
    [[86, 41, true], [116, 37], [142, 31, true], [142, 29], [86, 38]],
    { axis: 'x', segs: 24, a0: st.cutaway ? 0.55 : 0, a1: st.cutaway ? Math.PI * 1.62 : Math.PI * 2, cutCaps: true, tone: 'body' }
  );
  cad.revolve(
    [[112, 24], [148, 15], [182, 2.2], [185, 0.2]],
    { axis: 'x', segs: 22, tone: 'hi' }
  );

  // 7. External Swept Fuel & Bleed-Air Manifold Pipes hugging the Core!
  cad.sweepTube([[-68, -36, 22], [-30, -40, 26], [16, -39, 24], [58, -36, 18]], 2.3, { cornerR: 10, tone: 'hi' });
  cad.sweepTube([[-52, -26, 36], [0, -30, 39], [44, -28, 35]], 1.8, { cornerR: 8, tone: 'body' });

  // 8. Outer Aerodynamic High-Bypass Nacelle Cowling (with Cutaway Window & Translating Thrust Reverser!)
  const cowlA0 = st.cutaway ? 0.62 : 0;
  const cowlA1 = st.cutaway ? Math.PI * 1.56 : Math.PI * 2;

  // Forward Acoustic Intake Lip (always 360° ring at the very nose lip so the intake mouth reads unmistakably!)
  cad.revolve(
    [[-144, 63], [-150, 66], [-146, 70], [-130, 73, true], [-116, 73], [-116, 63], [-134, 61], [-144, 63]],
    { axis: 'x', segs: 32, tone: 'hi', key: 'cowl' }
  );

  // Mid Fan Cowl Barrel (cutaway opens near side to expose fan, compressor & combustor!)
  cad.revolve(
    [[-116, 73, true], [-68, 74], [-22, 72, true], [-22, 65], [-68, 66], [-116, 63]],
    { axis: 'x', segs: 30, a0: cowlA0, a1: cowlA1, cutCaps: true, ribRings: [1], tone: 'body', key: 'cowl' }
  );

  // Aft Translating Sleeve Cowl (slides +26 units aft when Reverse Thrust is deployed, exposing cascade vanes!)
  const revShift = st.rev ? 26 : 0;
  if (st.rev) {
    // Exposed blocker/cascade reverser rings
    cad.cyl([-22, 0, 0], [4, 0, 0], 66, 65, { segs: 24, holeR: 60, ribEvery: 2, tone: 'hi', liveStroke: true, key: 'rev' });
  }
  cad.revolve(
    [[-22 + revShift, 72, true], [34 + revShift, 68], [88 + revShift, 57, true], [88 + revShift, 51], [34 + revShift, 61], [-22 + revShift, 65]],
    { axis: 'x', segs: 30, a0: cowlA0, a1: cowlA1, cutCaps: true, ribRings: [1], tone: st.rev ? 'hi' : 'body', key: 'rev' }
  );

  // Callout Actuator Tags anchored directly to the real 3D engine assemblies
  cad.callout([-136, -48, 52], -36, -34, st.cutaway ? 'CLOSE COWL' : 'OPEN CUTAWAY', { key: 'cowl', op: true, sel: st.cutaway });
  cad.callout([-144, 10, -14], -44, 48, 'SPOOL FAN (' + st.rpmPct + '%)', { key: 'spool', op: false });
  cad.callout([16, -32, -16], 10, 62, st.ignited ? 'BURNER: LIT' : 'BURNER: CUT', { key: 'ign', sel: st.ignited });
  cad.callout([54 + revShift, 22, 54], 38, -28, st.rev ? 'REVERSER: DEPLOYED' : 'DEPLOY REVERSER', { key: 'rev', sel: st.rev });

  const thrust = !st.ignited ? 0 : st.rev ? -Math.round(st.rpmPct * 1.9) : Math.round(st.rpmPct * 3.85);
  return (st.cutaway ? 'cutaway · ' : 'cowled · ') + 'n1 ' + st.rpmPct + '% · ' + (st.rev ? 'reverse ' : 'fwd ') + thrust + ' kN';
}
`,
  });

  // ==========================================================================
  // SHOWCASE B: Sculpted Aerodynamic Grand-Tourer Sports Car (Automotive CAD)
  // ==========================================================================
  writeCadFigure({
    slug: "showcase-02-sports-car",
    fig: "Auto 2",
    title: "Sculpted Grand-Tourer Coupe · Multi-Station Loft",
    hint: "steer front axle · deploy active aero · toggle lamps · drag to orbit",
    initialReadout: "aero wing stowed · steer +18° · quad-diffuser gt",
    ariaLabel:
      "Interactive 3D isometric grand-tourer sports coupe built from multi-station lofted bodywork, flared fenders, fastback glasshouse canopy, steerable 5-spoke alloy wheels, and active swan-neck rear wing.",
    footHelp:
      "Click parts or keys: <kbd>S</kbd> cycle front steering · <kbd>W</kbd> / <kbd>Space</kbd> deploy active DRS/airbrake rear wing · <kbd>L</kbd> toggle headlamps · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit in 3D.",
    azDeg: -144,
    elDeg: 24,
    sceneJs: `
const st = { steerDeg: 18, wingUp: false, lamps: true };
const KM = { s: 'steer', w: 'wing', ' ': 'wing', l: 'lamps' };

function act(k) {
  if (k === 'steer') st.steerDeg = st.steerDeg === 18 ? -18 : st.steerDeg === -18 ? 0 : 18;
  else if (k === 'wing') st.wingUp = !st.wingUp;
  else if (k === 'lamps') st.lamps = !st.lamps;
  redraw(false);
}

function buildScene(cad) {
  // Helper: symmetric transverse car body cross-section at station x
  // Returns closed 10-point loop: bottom-center -> R-sill -> R-fender-mid -> R-shoulder -> R-hood-in -> center-top -> L-...
  function bodyRing(x, zBot, ySill, yMid, zMid, yTop, zShoulder, zCenter) {
    return [
      [x, 0, zBot],
      [x, -ySill, zBot + 2],
      [x, -yMid, zMid],
      [x, -yTop, zShoulder],
      [x, -yTop * 0.48, zCenter],
      [x, yTop * 0.48, zCenter],
      [x, yTop, zShoulder],
      [x, yMid, zMid],
      [x, ySill, zBot + 2],
    ];
  }

  // 1. Front Carbon Splitter Lip + Rear Quad-Fin Diffuser Tray
  cad.extrudePoly(
    [[-168, -54], [-156, -60], [-132, -60], [-132, 60], [-156, 60], [-168, 54]],
    { origin: [0, 0, 10], uAxis: [1, 0, 0], vAxis: [0, 1, 0], wAxis: [0, 0, 1], depth: 3.5, tone: 'dark' }
  );
  cad.box3(132, -54, 12, 26, 108, 6, { tone: 'dark' });
  for (const fy of [-38, -14, 14, 38]) {
    cad.box3(138, fy - 1.2, 9, 22, 2.4, 9, { tone: 'hi' });
  }
  // Quad Cylindrical Exhaust Tailpipes
  for (const ey of [-44, -34, 34, 44]) {
    cad.cyl([152, ey, 16], [163, ey, 16], 3.8, 3.8, { segs: 14, holeR: 2.7, tone: 'hi' });
  }

  // 2. Sculpted Multi-Station Lofted Coachwork (10 stations with raised wheel-arch cutouts!)
  const bodyStations = [
    bodyRing(-164, 13, 38, 44, 19, 40, 24, 23),  // low sharp nose
    bodyRing(-140, 13, 52, 60, 26, 56, 36, 33),  // headlamp / front intake flare
    bodyRing(-102, 27, 46, 67, 36, 63, 45, 41),  // front wheel-arch crown (raised arch!)
    bodyRing(-64,  13, 56, 64, 31, 60, 46, 45),  // cowl base of windshield
    bodyRing(-12,  12, 53, 59, 29, 56, 47, 46),  // pinched coke-bottle door waist!
    bodyRing(44,   12, 56, 65, 32, 61, 49, 47),  // rear haunch intake swell
    bodyRing(96,   29, 46, 68, 38, 63, 51, 48),  // muscular rear wheel-arch crown (raised arch!)
    bodyRing(136,  16, 54, 61, 33, 56, 48, 46),  // rear decklid taper
    bodyRing(156,  18, 48, 53, 32, 49, 45, 44),  // Kammback transom tail
  ];
  cad.loft(bodyStations, { closed: true, capStart: true, capEnd: true, ribStations: [2, 4, 6], creaseDeg: 28, tone: 'body' });

  // 3. Sculpted Fastback Glasshouse Canopy (lofted from cowl -> roof peak -> fastback hatch!)
  const cabinRing = (x, yBase, zBase, yRoof, zRoof) => [
    [x, -yBase, zBase],
    [x, -yRoof, zRoof],
    [x, 0, zRoof + 2.2],
    [x, yRoof, zRoof],
    [x, yBase, zBase],
  ];
  cad.loft([
    cabinRing(-58, 52, 45, 48, 46),
    cabinRing(-18, 50, 47, 41, 68), // top of raked windshield
    cabinRing(32,  50, 48, 39, 69), // roof crown
    cabinRing(88,  48, 49, 35, 60), // fastback slope
    cabinRing(132, 42, 47, 34, 48), // rear deck merge
  ], { closed: true, capStart: true, capEnd: true, glass: true, creaseDeg: 24 });

  // A-pillar -> Roofline -> Fastback Cantrail Structural Chrome/Carbon Bows
  for (const sgn of [-1, 1]) {
    cad.sweepTube([
      [-56, sgn * 51, 45.5],
      [-18, sgn * 41.5, 68.5],
      [32, sgn * 39.5, 69.5],
      [88, sgn * 35.5, 60.5],
      [130, sgn * 34.5, 48],
    ], 1.5, { cornerR: 12, tone: 'hi' });
    // Sculpted Wing Mirrors on stalks
    cad.sweepTube([[-34, sgn * 54, 47], [-38, sgn * 66, 52]], 1.4, { tone: 'dark' });
    cad.cyl([-43, sgn * 67, 52], [-33, sgn * 67, 52.5], 2.5, 4.2, { segs: 12, tone: 'hi' });
  }

  // 4. Recessed Headlamp Pods + Full-Width Taillight Blade
  for (const sgn of [-1, 1]) {
    cad.extrudePoly(
      [[-152, sgn * 38], [-132, sgn * 53], [-124, sgn * 49], [-145, sgn * 34]],
      {
        origin: [0, 0, 31],
        uAxis: [1, 0, 0],
        vAxis: [0, 1, 0],
        wAxis: [0, 0, 1],
        depth: 4,
        tone: st.lamps ? 'hi' : 'dark',
        liveStroke: st.lamps,
        key: 'lamps',
      }
    );
  }
  cad.box3(154, -46, 37, 4, 92, 4.5, { tone: 'hi', liveStroke: st.lamps, key: 'lamps' });

  // 5. Four 3D Cylindrical Tires + Deep-Dish 5-Spoke Alloy Rims + Brake Rotors!
  function drawWheel(wx, wy, rTire, width, steerRad) {
    cad.push(cad.mTrans(wx, wy, rTire));
    if (steerRad) cad.push(cad.mRotZ(steerRad));
    const yIn = wy < 0 ? width / 2 : -width / 2;
    const yOut = wy < 0 ? -width / 2 : width / 2;
    // Recessed dark wheelhouse drum behind wheel
    cad.cyl([0, yIn * 1.15, 0], [0, yOut * 0.7, 0], rTire + 3, rTire + 3, { segs: 20, tone: 'dark' });
    // Thick rubber tire with sidewall shoulder
    cad.cyl([0, yIn, 0], [0, yOut, 0], rTire, rTire, { segs: 26, holeR: rTire * 0.66, tone: 'dark', key: 'steer' });
    // Alloy rim barrel + brake disc + center lock nut + 5 spokes!
    cad.cyl([0, yIn * 0.4, 0], [0, yOut * 0.92, 0], rTire * 0.66, rTire * 0.66, { segs: 22, holeR: rTire * 0.56, tone: 'hi', key: 'steer' });
    cad.cyl([0, yOut * 0.3, 0], [0, yOut * 0.55, 0], rTire * 0.48, rTire * 0.48, { segs: 18, tone: 'body' }); // brake rotor
    cad.cyl([0, yOut * 0.4, 0], [0, yOut * 0.98, 0], 5.2, 4.2, { segs: 14, tone: 'hi', key: 'steer' });
    for (let sp = 0; sp < 5; sp++) {
      const a = (sp * Math.PI * 2) / 5 + 0.2;
      const p1 = [Math.cos(a) * 4.5, yOut * 0.86, Math.sin(a) * 4.5];
      const p2 = [Math.cos(a) * (rTire * 0.60), yOut * 0.88, Math.sin(a) * (rTire * 0.60)];
      cad.sweepTube([p1, p2], 1.7, { segs: 8, tone: 'hi', key: 'steer' });
    }
    if (steerRad) cad.pop();
    cad.pop();
  }
  const steerRad = (st.steerDeg * Math.PI) / 180;
  drawWheel(-102, -57, 25, 18, steerRad);
  drawWheel(-102,  57, 25, 18, steerRad);
  drawWheel( 96,  -59, 27, 21, 0);
  drawWheel( 96,   59, 27, 21, 0);

  // 6. Active Swan-Neck Rear Aero Wing (stowed flush vs elevated high-downforce pitch!)
  const wz = st.wingUp ? 66 : 51;
  const wpitch = st.wingUp ? 0.24 : 0.04;
  for (const py of [-26, 26]) {
    cad.sweepTube([[130, py, 46], [138, py, wz + 2]], 1.8, { tone: 'dark', key: 'wing' });
  }
  cad.push(cad.mTrans(142, 0, wz));
  cad.push(cad.mRotY(wpitch));
  cad.extrudePoly(
    [[-14, 0], [12, -2], [16, 1.5], [-10, 3.2]],
    { origin: [0, -56, 0], uAxis: [1, 0, 0], vAxis: [0, 0, 1], wAxis: [0, 1, 0], depth: 112, tone: 'hi', liveStroke: st.wingUp, key: 'wing' }
  );
  // Wing endplates
  for (const ey of [-57, 55]) {
    cad.box3(-15, ey, -5, 33, 2, 11, { tone: 'body', key: 'wing' });
  }
  cad.pop(); cad.pop();

  // Callout Actuator Tags
  cad.callout([-102, -62, 20], -38, 48, 'STEER (' + (st.steerDeg > 0 ? '+' : '') + st.steerDeg + '°)', { key: 'steer', op: true, sel: st.steerDeg !== 0 });
  cad.callout([-142, 46, 34], 42, 34, st.lamps ? 'LAMPS: ON' : 'LAMPS: OFF', { key: 'lamps', sel: st.lamps });
  cad.callout([142, 34, wz + 3], -34, -34, st.wingUp ? 'AERO WING: ACTIVE' : 'DEPLOY AERO WING', { key: 'wing', op: true, sel: st.wingUp });

  return (st.wingUp ? 'active aero (+2.4 kN) · ' : 'aero stowed · ') + 'steer ' + (st.steerDeg > 0 ? '+' : '') + st.steerDeg + '° · lamps ' + (st.lamps ? 'on' : 'off');
}
`,
  });

  // ==========================================================================
  // SHOWCASE C: Ocean Cruise Liner (Naval Architecture Hull Loft & Promenade)
  // ==========================================================================
  writeCadFigure({
    slug: "showcase-03-cruise-ship",
    fig: "Marine 3",
    title: "Ocean Cruise Liner · Bulbous Bow & Terraced Decks",
    hint: "vector azimuth pods · sweep radar · swing davit · drag to orbit",
    initialReadout: "22.5 kn · pods +20° · 6 promenade decks · radar active",
    ariaLabel:
      "Interactive 3D isometric ocean cruise ship with naval-lofted bulbous bow, flared clipper stem, cruiser stern, twin steerable azimuth thruster pods, six stepped balcony promenade decks, cantilevered navigation bridge wings, raked winged funnel, radar mast, and lifeboats.",
    footHelp:
      "Click parts or keys: <kbd>P</kbd> vector twin stern azimuth pods · <kbd>R</kbd> / <kbd>Space</kbd> sweep radar scanners · <kbd>B</kbd> swing starboard lifeboat davit outboard · <kbd>K</kbd> step cruise speed · Drag or <kbd>[</kbd> <kbd>]</kbd> to orbit in 3D.",
    azDeg: -142,
    elDeg: 25,
    sceneJs: `
const st = { podDeg: 20, radarDeg: 28, davitOut: false, knots: 22.5 };
const KM = { p: 'pods', r: 'radar', ' ': 'radar', b: 'davit', k: 'speed' };

function act(k) {
  if (k === 'pods') st.podDeg = st.podDeg === 20 ? -20 : st.podDeg === -20 ? 0 : 20;
  else if (k === 'radar') st.radarDeg = (st.radarDeg + 42) % 360;
  else if (k === 'davit') st.davitOut = !st.davitOut;
  else if (k === 'speed') st.knots = st.knots >= 24 ? 14.0 : +(st.knots + 4.25).toFixed(1);
  redraw(false);
}

function buildScene(cad) {
  // 1. Forward Underwater Bulbous Bow Torpedo Nose (x = -196 .. -146)
  cad.revolve(
    [[-196, 0.4], [-190, 7.5], [-176, 11], [-156, 9.5], [-142, 6]],
    { axis: 'x', origin: [0, 0, 7], segs: 20, tone: 'hi' }
  );

  // 2. Naval-Lofted Main Ship Hull (keel -> bilge -> waterline chine -> flared sheer deck!)
  function hullRing(x, yKeel, zKeel, yWL, zWL, yDeck, zDeck) {
    return [
      [x, 0, zKeel],
      [x, -yKeel, zKeel + 1.5],
      [x, -yWL, zWL],
      [x, -yDeck, zDeck],
      [x, 0, zDeck + 1],
      [x, yDeck, zDeck],
      [x, yWL, zWL],
      [x, yKeel, zKeel + 1.5],
    ];
  }
  cad.loft([
    hullRing(-192, 0.5, 11, 1.5, 22, 2.5, 48),  // razor clipper bow stem!
    hullRing(-162, 7,   4,  15,  18, 26,  45),  // dramatic bow flare
    hullRing(-116, 22,  2,  32,  17, 40,  42),  // forebody entry
    hullRing(-48,  32,  0,  40,  17, 43,  40),  // forward midship
    hullRing(36,   33,  0,  41,  17, 43,  40),  // aft midship parallel body
    hullRing(112,  29,  2,  39,  18, 42,  40),  // aft run rising above pods
    hullRing(166,  20,  11, 34,  22, 39,  41),  // cruiser stern overhang
    hullRing(186,  12,  16, 26,  25, 33,  41),  // curved transom stern
  ], { closed: true, capStart: true, capEnd: true, ribStations: [2, 4, 6], creaseDeg: 26, tone: 'dark' });

  // Foredeck Breakwater & Twin Anchor Chains/Capstans
  cad.cyl([-156, -8, 45], [-156, -8, 49], 3.2, 2.6, { segs: 12, tone: 'hi' });
  cad.cyl([-156,  8, 45], [-156,  8, 49], 3.2, 2.6, { segs: 12, tone: 'hi' });

  // 3. Five Stepped Terraced Balcony Superstructure Decks (extruded rounded-prow tiers!)
  function deckTier(xBow, xStern, halfW, zBase, h, tone = 'hi') {
    const pts = [
      [xStern, -halfW],
      [xBow + 28, -halfW],
      [xBow + 8, -halfW * 0.58],
      [xBow, 0],
      [xBow + 8, halfW * 0.58],
      [xBow + 28, halfW],
      [xStern, halfW],
    ];
    cad.extrudePoly(pts, {
      origin: [0, 0, zBase],
      uAxis: [1, 0, 0],
      vAxis: [0, 1, 0],
      wAxis: [0, 0, 1],
      depth: h,
      tone,
    });
  }
  deckTier(-126, 178, 39, 40, 10, 'body'); // Promenade Deck 6
  deckTier(-112, 172, 37, 50, 9,  'hi');   // Balcony Deck 7
  deckTier(-98,  165, 36, 59, 9,  'body'); // Balcony Deck 8
  deckTier(-84,  156, 35, 68, 9,  'hi');   // Suite Deck 9
  deckTier(-68,  146, 34, 77, 8,  'hi');   // Lido Pool & Panorama Deck 10

  // Recessed Lido Swimming Pool Deck Basin amidships!
  cad.box3(-8, -14, 83, 44, 28, 3.5, { glass: true });

  // 4. Cantilevered Panoramic Navigation Bridge & Port/Starboard Bridge Wings!
  cad.extrudePoly(
    [[-64, -50], [-82, -50], [-86, -34], [-96, 0], [-86, 34], [-82, 50], [-64, 50]],
    { origin: [0, 0, 81], uAxis: [1, 0, 0], vAxis: [0, 1, 0], wAxis: [0, 0, 1], depth: 7.5, glass: true }
  );
  cad.extrudePoly(
    [[-62, -48], [-80, -48], [-84, -32], [-93, 0], [-84, 32], [-80, 48], [-62, 48]],
    { origin: [0, 0, 88.5], uAxis: [1, 0, 0], vAxis: [0, 1, 0], wAxis: [0, 0, 1], depth: 2.5, tone: 'hi' }
  );

  // 5. Forward Observation Lounge + Tall Radar/Satcom Mast + Spinning Scanners + Radome Domes
  cad.cyl([-54, 0, 85], [-46, 0, 124], 3.2, 1.4, { segs: 12, tone: 'hi', key: 'radar' });
  cad.sweepTube([[-49, -18, 106], [-49, 18, 106]], 1.2, { tone: 'hi', key: 'radar' });
  // Twin white satcom radome spheres on bridge roof
  cad.revolve([[-6,0.2],[-4,4.8],[0,6.5],[4,4.8],[6,0.2]], { axis: 'z', origin: [-64, -18, 97], segs: 16, tone: 'hi' });
  cad.revolve([[-6,0.2],[-4,4.8],[0,6.5],[4,4.8],[6,0.2]], { axis: 'z', origin: [-64,  18, 97], segs: 16, tone: 'hi' });
  // Rotating X-Band Radar Bar
  cad.push(cad.mTrans(-47, 0, 125));
  cad.push(cad.mRotZ((st.radarDeg * Math.PI) / 180));
  cad.box3(-2.5, -15, 0, 5, 30, 2.6, { tone: 'hi', liveStroke: true, key: 'radar' });
  cad.pop(); cad.pop();

  // 6. Iconic Raked Winged Cruise-Ship Funnel Aft!
  cad.push(cad.mTrans(68, 0, 85));
  cad.push(cad.mRotY(0.24)); // raked aft 14°
  cad.extrudePoly(
    [[-18, 0], [-12, -13], [14, -10], [22, 0], [14, 10], [-12, 13]],
    { origin: [0, 0, 0], uAxis: [1, 0, 0], vAxis: [0, 1, 0], wAxis: [0, 0, 1], depth: 34, taper: 0.78, tone: 'hi' }
  );
  // Characteristic winged whale-tail smoke deflector fins!
  cad.extrudePoly(
    [[-12, -26], [10, -22], [18, 0], [10, 22], [-12, 26], [-4, 0]],
    { origin: [2, 0, 31], uAxis: [1, 0, 0], vAxis: [0, 1, 0], wAxis: [0, 0, 1], depth: 3.5, tone: 'hi' }
  );
  // Twin exhaust uptakes
  cad.cyl([-2, -4, 33], [1, -4, 39], 3.2, 3.0, { segs: 12, holeR: 2.2, tone: 'dark' });
  cad.cyl([ 6,  4, 33], [9,  4, 39], 3.2, 3.0, { segs: 12, holeR: 2.2, tone: 'dark' });
  cad.pop(); cad.pop();

  // 7. Lifeboats on Gravity Davits along Both Flanks (middle starboard boat swings outboard!)
  for (const sgn of [-1, 1]) {
    for (let bi = 0; bi < 3; bi++) {
      const bx = -38 + bi * 38;
      const swing = (sgn === -1 && bi === 1 && st.davitOut) ? -12 : 0;
      const bz = (sgn === -1 && bi === 1 && st.davitOut) ? 44 : 51;
      const by = sgn * 41 + swing;
      cad.sweepTube([[bx - 7, sgn * 37, 58], [bx - 7, by, bz + 4]], 0.9, { tone: 'body', key: 'davit' });
      cad.sweepTube([[bx + 7, sgn * 37, 58], [bx + 7, by, bz + 4]], 0.9, { tone: 'body', key: 'davit' });
      // Double-ended enclosed lifeboat hull
      cad.revolve(
        [[-12, 0.3], [-8, 3.8], [0, 4.4], [8, 3.8], [12, 0.3]],
        { axis: 'x', origin: [bx, by, bz], segs: 14, tone: 'hi', liveStroke: swing !== 0, key: 'davit' }
      );
    }
  }

  // 8. Twin Steerable 360° Azimuth Pod Thrusters under Cruiser Stern!
  const podRad = (st.podDeg * Math.PI) / 180;
  for (const py of [-18, 18]) {
    cad.push(cad.mTrans(152, py, 10));
    cad.push(cad.mRotZ(podRad));
    cad.cyl([0, 0, 8], [0, 0, 0], 3.2, 2.4, { segs: 12, tone: 'body', key: 'pods' });
    cad.revolve(
      [[-11, 0.5], [-7, 4.6], [5, 4.6], [11, 1.8]],
      { axis: 'x', segs: 16, tone: 'hi', key: 'pods' }
    );
    // 4-blade propeller hub
    for (let b = 0; b < 4; b++) {
      const a = (b * Math.PI) / 2 + 0.4;
      cad.box3(-12.5, Math.cos(a) * 3.5 - 0.8, Math.sin(a) * 3.5 - 0.8, 1.5, 3.8, 3.8, { tone: 'hi', key: 'pods' });
    }
    cad.pop(); cad.pop();
  }

  // Callouts
  cad.callout([-47, 0, 126], 46, -24, 'RADAR (' + st.radarDeg + '°)', { key: 'radar', op: true });
  cad.callout([0, -44, 48], -48, 34, st.davitOut ? 'DAVIT: OUTBOARD' : 'SWING LIFEBOAT', { key: 'davit', sel: st.davitOut });
  cad.callout([154, -18, 8], -52, -44, 'AZIMUTH PODS (' + (st.podDeg > 0 ? '+' : '') + st.podDeg + '°)', { key: 'pods', op: true, sel: st.podDeg !== 0 });
  cad.callout([-180, 0, 10], 42, 30, 'SPEED: ' + st.knots + ' KN', { key: 'speed' });

  return st.knots + ' kn · pods ' + (st.podDeg > 0 ? '+' : '') + st.podDeg + '° · davit ' + (st.davitOut ? 'outboard' : 'stowed');
}
`,
  });
}
