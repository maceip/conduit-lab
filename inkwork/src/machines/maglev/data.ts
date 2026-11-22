import type { BoltSetDef, CameraDef, GuideDef, PartAnnotation, PartDef, StepDef, Vec3 } from '../types';
import { MAGLEV_BOM_CALLOUTS } from './bom';

/**
 * Shanghai SMT Maglev (Transrapid TR08 architecture)
 *
 * What it is: an electromagnetic-suspension high-speed maglev — the train wraps
 *   a concrete box beam, levitates on attracted C-core magnets (nominal 10 mm
 *   gap), is centred by guidance magnets, and is pulled by a long-stator linear
 *   synchronous motor whose windings live in the beam, not on the train. The
 *   causal chain the animation shows: the levitation control energises → the
 *   10 mm gap opens → the car floats; the guideway's travelling field (phase
 *   locked to position) drags the car's excitation magnets forward.
 *
 * Dimensions: public Transrapid TR08 / Shanghai SMT figures (3.7 m body width,
 *   ≈4.2 m height, ≈27 m nose car, 10 mm levitation/guidance gaps, ≈2.8 m box
 *   beam). No manufacturer drawings, no logos or lettering on the model.
 *
 * Units & frame: millimetres. +x is forward (nose), −x aft, +y up; the beam
 *   centreline plane is z = 0; the bottom of the pier is y = 0. The section cut
 *   removes the z > 0 half — side shells, skirts, the box beam and the magnet
 *   housings are hollow and symmetric about z = 0, so the half-section opens
 *   the carbody, the wrap-around bogie arms and the beam cavity.
 *
 * Breakdown: 31 parts at the top level and six sub-assemblies with 35 parts
 *   (carbody / bogie / propulsion / guideway / power / braking).
 *
 * Motion (kinematics.ts pure functions + tests): the car levitates to a 10 mm
 *   gap with guidance centring, and the long-stator phase is locked to position
 *   (phase = 2π·x / pole pitch) — synchronous by construction.
 */

/** Key dimensions (mm) and the explosion unit U. */
export const MG = {
  /** Car body. */
  carLength: 27000,
  carWidth: 3700,
  carHeight: 4200,
  carX0: 0,
  carX1: 27000,
  noseX: 27000,
  floorY: 3400,        // underbelly / beam top
  roofY: 7600,         // floorY + carHeight
  /** Beam & pier. */
  beamX0: -6000,
  beamX1: 30000,
  beamW: 2800,
  beamH: 2200,
  beamTopY: 3400,
  beamBotY: 1200,
  pierY: 1200,
  /** Suspension. */
  levGap: 10,          // nominal levitation gap
  guidGap: 10,
  polePitch: 258,      // long-stator pole pitch (mm)
  /** Bogie stations (x of the wrap frames). */
  bogieFX: 21500,
  bogieRX: 4500,
  doorFX: 21000,
  doorRX: 6000,
  /** Explosion unit: 1U = 6,000 mm (sized for the 36 m scene). */
  U: 6000,
};

export const AY = MG.roofY - MG.carHeight / 2; // carbody centreline (visual)
const U = MG.U;
const ux = (n: number): number => n * U;

/**
 * 31 parts (indices 1–31). Three-wave teardown:
 * W1 exterior skins & leaves 0→0.35, W2 major groups 0.30→0.68,
 * W3 magnet arrays / track gear 0.60→1.00. The beam and pier stay put.
 */
export const PARTS: PartDef[] = [
  /* ── Wave 1 · exterior skins & leaves ───────────────────────────── */
  {
    id: 'nose-cone', index: 1, name: 'Aerodynamic Nose Shell', en: 'Aerodynamic Nose Shell', role: 'Aero · crush zone',
    material: 'Glass-fibre sandwich',
    description: 'Streamlined double-curvature nose (≈5.2 m long), bonded GFRP sandwich over an aluminium crush frame; drag coefficient 0.26 at 430 km/h.',
    explode: [ux(1.2), 0, 0], stage: [0, 0.3],
  },
  {
    id: 'windshield', index: 2, name: 'Windshield Panel', en: 'Windshield Panel', role: 'Vision',
    material: 'Laminated glass',
    description: 'Twin-pane dark glazing set in the navy nose panel; bird-strike rated to 430 km/h, electrically de-iced.',
    explode: [ux(1.5), 0, 0], stage: [0.03, 0.32],
  },
  {
    id: 'door-left', index: 3, name: 'Plug Door (left)', en: 'Plug Door (Left)', role: 'Passenger access',
    material: 'Aluminium honeycomb',
    description: 'Single leaf plug door (1,300 × 2,050 mm) that lifts and slides forward into the shell pocket; seals to 4 kPa at speed.',
    explode: [0, 0, ux(1.2)], stage: [0.05, 0.35],
  },
  {
    id: 'door-right', index: 4, name: 'Plug Door (right)', en: 'Plug Door (Right)', role: 'Passenger access',
    material: 'Aluminium honeycomb',
    description: 'Mirror of the left leaf, driven by a common electric screw jack; interlocked with the levitation gap — no levitating with a door open.',
    explode: [0, 0, -ux(1.2)], stage: [0.05, 0.35],
  },
  {
    id: 'skirt-left', index: 5, name: 'Undercar Skirt (left)', en: 'Undercar Skirt (Left)', role: 'Aero · fairing',
    material: 'GFRP',
    description: 'Fairing over the bogie arms, 8 mm wall, hinged at the top for bogie access; splits ±z at the centre line.',
    explode: [0, -ux(0.6), ux(1.4)], stage: [0, 0.35],
  },
  {
    id: 'skirt-right', index: 6, name: 'Undercar Skirt (right)', en: 'Undercar Skirt (Right)', role: 'Aero · fairing',
    material: 'GFRP',
    description: 'Right-hand skirt; together with the left half it keeps the wrap-around bogie out of the 430 km/h slipstream.',
    explode: [0, -ux(0.6), -ux(1.4)], stage: [0, 0.35],
  },
  {
    id: 'roof-fairing', index: 7, name: 'Roof Fairing & HVAC Cover', en: 'Roof Fairing', role: 'Aero · covers',
    material: 'Aluminium sheet',
    description: 'Shallow roof fairing (2.8 m long) with louvred HVAC intake; drains and antenna blanks moulded in.',
    explode: [0, ux(1.0), 0], stage: [0, 0.35],
  },

  /* ── Wave 2 · major groups ──────────────────────────────────────── */
  {
    id: 'side-shell-left', index: 8, name: 'Side Shell (left)', en: 'Side Shell (Left)', role: 'Primary structure',
    material: 'Aluminium alloy 6082',
    description: 'Left side shell with the window band cut-out, 1,800 mm extruded panels, self-piercing riveted to the floor ring; hollow and symmetric for the half-section.',
    explode: [0, 0, ux(2.0)], stage: [0.3, 0.62],
  },
  {
    id: 'side-shell-right', index: 9, name: 'Side Shell (right)', en: 'Side Shell (Right)', role: 'Primary structure',
    material: 'Aluminium alloy 6082',
    description: 'Right side shell; the two shells plus floor and roof form a torsion box taking 0.5 g lateral service loads.',
    explode: [0, 0, -ux(2.0)], stage: [0.3, 0.62],
  },
  {
    id: 'bogie-front', index: 10, name: 'Front Levitation Bogie', en: 'Front Levitation Bogie', role: 'Suspension frame',
    material: 'Welded S355 steel',
    description: 'Wrap-around frame under the cab: two arms reaching down beside the beam to y ≈ 2,200, carrying levitation, guidance and brake magnets plus the gap sensors.',
    explode: [0, -ux(1.6), 0], stage: [0.32, 0.66],
  },
  {
    id: 'bogie-rear', index: 11, name: 'Rear Levitation Bogie', en: 'Rear Levitation Bogie', role: 'Suspension frame',
    material: 'Welded S355 steel',
    description: 'Rear frame, identical arms; each bogie levitates independently so a faulted module drops to skid rails rather than the car.',
    explode: [0, -ux(1.6), 0], stage: [0.32, 0.66],
  },
  {
    id: 'battery-box', index: 12, name: 'Onboard Battery Box', en: 'Onboard Battery Box', role: 'Emergency power',
    material: 'NiCd battery set',
    description: 'Battery box under the floor (110 V, 200 Ah): holds levitation and gap control alive if ground power drops, for a controlled touchdown.',
    explode: [0, -ux(1.2), 0], stage: [0.36, 0.68],
  },
  {
    id: 'hvac-unit', index: 13, name: 'HVAC Unit', en: 'HVAC Unit', role: 'Climate',
    material: 'Aluminium casing',
    description: 'Roof-pack air conditioning (2 × 25 kW), ducted through the ceiling plenum; air renewal at 30 m³/h per passenger.',
    explode: [0, ux(1.4), 0], stage: [0.36, 0.68],
  },
  {
    id: 'converter-cabinet', index: 14, name: 'Converter & Control Cabinet', en: 'Converter & Control Cabinet', role: 'Power electronics',
    material: 'Sheet steel',
    description: 'Cabinet with the levitation choppers, guidance converters and gap-controller DSPs — one per bogie, redundant pairs.',
    explode: [0, -ux(1.4), 0], stage: [0.38, 0.68],
  },

  /* ── Wave 3 · magnet arrays & track gear ────────────────────────── */
  {
    id: 'lev-magnet-fl', index: 15, name: 'Levitation Magnet (FL)', en: 'Levitation Magnet (FL)', role: 'Lift · front left',
    material: 'Low-carbon steel + copper',
    description: 'C-core electromagnet on the front-left arm: 12 poles facing the beam-mounted stator pack, nominal 10 mm gap, ≈76 kN lift per magnet.',
    explode: [0, -ux(0.8), ux(1.3)], stage: [0.6, 0.85],
  },
  {
    id: 'lev-magnet-fr', index: 16, name: 'Levitation Magnet (FR)', en: 'Levitation Magnet (FR)', role: 'Lift · front right',
    material: 'Low-carbon steel + copper',
    description: 'Front-right magnet; the paired left/right magnets are chopper-fed in opposite polarity so guidance forces can be added to lift.',
    explode: [0, -ux(0.8), -ux(1.3)], stage: [0.6, 0.85],
  },
  {
    id: 'lev-magnet-rl', index: 17, name: 'Levitation Magnet (RL)', en: 'Levitation Magnet (RL)', role: 'Lift · rear left',
    material: 'Low-carbon steel + copper',
    description: 'Rear-left magnet with its own gap sensors and chopper; control bandwidth 20 Hz keeps the gap inside 10 ± 1 mm.',
    explode: [0, -ux(0.8), ux(1.3)], stage: [0.62, 0.87],
  },
  {
    id: 'lev-magnet-rr', index: 18, name: 'Levitation Magnet (RR)', en: 'Levitation Magnet (RR)', role: 'Lift · rear right',
    material: 'Low-carbon steel + copper',
    description: 'Rear-right magnet; four lift points per bogie give an eight-point levitation plane under each car.',
    explode: [0, -ux(0.8), -ux(1.3)], stage: [0.62, 0.87],
  },
  {
    id: 'guid-magnet-fl', index: 19, name: 'Guidance Magnet (FL)', en: 'Guidance Magnet (FL)', role: 'Centring · front left',
    material: 'Low-carbon steel + copper',
    description: 'Side-facing C-core holding the 10 mm guidance gap to the beam rail; each car takes 20 kN lateral without contact.',
    explode: [0, -ux(0.4), ux(1.8)], stage: [0.64, 0.9],
  },
  {
    id: 'guid-magnet-fr', index: 20, name: 'Guidance Magnet (FR)', en: 'Guidance Magnet (FR)', role: 'Centring · front right',
    material: 'Low-carbon steel + copper',
    description: 'Front-right guidance magnet; opposed pairs push and pull so centring never needs the gap to close.',
    explode: [0, -ux(0.4), -ux(1.8)], stage: [0.64, 0.9],
  },
  {
    id: 'guid-magnet-rl', index: 21, name: 'Guidance Magnet (RL)', en: 'Guidance Magnet (RL)', role: 'Centring · rear left',
    material: 'Low-carbon steel + copper',
    description: 'Rear-left guidance magnet on the trailing arm, wired to the same 110 V emergency bus as the lift magnets.',
    explode: [0, -ux(0.4), ux(1.8)], stage: [0.66, 0.92],
  },
  {
    id: 'guid-magnet-rr', index: 22, name: 'Guidance Magnet (RR)', en: 'Guidance Magnet (RR)', role: 'Centring · rear right',
    material: 'Low-carbon steel + copper',
    description: 'Rear-right guidance magnet; together the four units hold the car on the beam centre line through 400 m radius curves.',
    explode: [0, -ux(0.4), -ux(1.8)], stage: [0.66, 0.92],
  },
  {
    id: 'gap-sensors', index: 23, name: 'Gap Sensor Array', en: 'Gap Sensor Array', role: 'Measure 10 mm gap',
    material: 'Eddy-current probes',
    description: 'Eight eddy-current probes (four per bogie) reading the magnet-to-pack gap to ±0.1 mm at 2 kHz — the loop that keeps the car floating.',
    explode: [0, -ux(1.1), 0], stage: [0.68, 0.94],
  },
  {
    id: 'stator-pack-left', index: 24, name: 'Long-Stator Pack (left)', en: 'Long-Stator Pack (Left)', role: 'LSM armature',
    material: 'Laminated silicon steel',
    description: 'Guideway-mounted linear motor armature: 258 mm pole pitch, three-phase double-layer winding in 1.2 m packs bolted along the beam.',
    explode: [0, 0, ux(1.6)], stage: [0.6, 0.88],
  },
  {
    id: 'stator-pack-right', index: 25, name: 'Long-Stator Pack (right)', en: 'Long-Stator Pack (Right)', role: 'LSM armature',
    material: 'Laminated silicon steel',
    description: 'Right-hand armature pack; only the section ahead of the train is energised, so the line draws power in segments.',
    explode: [0, 0, -ux(1.6)], stage: [0.6, 0.88],
  },
  {
    id: 'guidance-rail-left', index: 26, name: 'Guidance Rail (left)', en: 'Guidance Rail (Left)', role: 'Centring track',
    material: 'Rolled steel, precision ground',
    description: 'Ground rail on the beam flank at the guidance magnet height; flatness 0.5 mm/m so the 10 mm gap stays centred.',
    explode: [0, 0, ux(2.2)], stage: [0.64, 0.92],
  },
  {
    id: 'guidance-rail-right', index: 27, name: 'Guidance Rail (right)', en: 'Guidance Rail (Right)', role: 'Centring track',
    material: 'Rolled steel, precision ground',
    description: 'Right-hand guidance rail; both rails carry the skid strips the car lands on if levitation is lost.',
    explode: [0, 0, -ux(2.2)], stage: [0.64, 0.92],
  },
  {
    id: 'brake-rail', index: 28, name: 'Eddy-Current Brake Rail', en: 'Eddy-Current Brake Rail', role: 'Track brake',
    material: 'Armco iron',
    description: 'Reaction rail low on the beam; the car’s brake magnets induce eddy currents in it for a wear-free 430 → 0 km/h stop in 3.5 km.',
    explode: [0, -ux(0.7), 0], stage: [0.7, 0.96],
  },
  {
    id: 'brake-magnets', index: 29, name: 'Brake Magnet Module', en: 'Brake Magnet Module', role: 'Emergency brake',
    material: 'Low-carbon steel + copper',
    description: 'Four-pole eddy-current brake magnets on the bogie arms plus spring-released friction skids for the final stop and for holding the car parked.',
    explode: [0, -ux(1.3), 0], stage: [0.72, 0.98],
  },
  {
    id: 'beam-shell', index: 30, name: 'Guideway Box Beam', en: 'Guideway Box Beam', role: 'Track structure',
    material: 'Prestressed concrete',
    description: '2.8 × 2.2 m prestressed box beam, 31.5 m spans; hollow core keeps 12.5 t/m dead load while carrying stator packs and rails. Fixed in place.',
    explode: [0, 0, 0], stage: [1, 1],
  },
  {
    id: 'pier-segment', index: 31, name: 'Pier & Bearing Plinth', en: 'Pier & Bearing Plinth', role: 'Base · y = 0',
    material: 'Reinforced concrete',
    description: 'Pier head with spherical bearings that let the beam expand; the plinth base sits at y = 0, the drawing’s ground line.',
    explode: [0, 0, 0], stage: [1, 1],
  },
];

export const NEIGHBOURS: Record<string, string[]> = {
  'bogie-front': ['lev-magnet-fl', 'lev-magnet-fr', 'guid-magnet-fl', 'guid-magnet-fr', 'gap-sensors', 'brake-magnets', 'bogie-front'],
  'lev-magnet-fl': ['gap-sensors', 'lev-magnet-fl'],
  'side-shell-left': ['door-left', 'skirt-left', 'side-shell-left'],
  'nose-cone': ['windshield', 'nose-cone'],
  'stator-pack-left': ['guidance-rail-left', 'stator-pack-left'],
};

export const BOLT_SETS: Record<string, BoltSetDef> = {
  'pack-bolts': { owner: 'stator-pack-left', distance: 900, stage: [0.6, 0.7] },
  'rail-bolts': { owner: 'guidance-rail-left', distance: 800, stage: [0.62, 0.72] },
  'magnet-bolts': { owner: 'lev-magnet-fl', distance: 700, stage: [0.58, 0.68] },
};

export const GUIDES: GuideDef[] = [
  { stage: 'nose-cone', origin: [MG.noseX + 200, MG.roofY - 600, 0] },
  { stage: 'roof-fairing', origin: [15000, MG.roofY + 200, 0] },
  { stage: 'bogie-front', origin: [MG.bogieFX, MG.beamBotY - 300, 0] },
  { stage: 'lev-magnet-fl', origin: [MG.bogieFX, 2400, 1400] },
  { stage: 'stator-pack-left', origin: [10000, 2400, 1500] },
  { stage: 'beam-shell', origin: [-4000, MG.beamTopY + 200, 0] },
];

export const CENTRE_LINES: Array<[Vec3, Vec3, number?]> = [
  [[MG.beamX0, MG.beamTopY, 0], [MG.beamX1, MG.beamTopY, 0], MG.carWidth / 2],
];

export const STEPS: StepDef[] = [
  {
    title: 'Assembly', en: 'Assembly',
    body: 'The Shanghai SMT maglev on its guideway: a streamlined 27 m nose car wrapped around a 2.8 m concrete box beam. There are no wheels — the car floats on attracted C-core magnets at a 10 mm gap, centred by guidance magnets, and is dragged along by the linear motor windings buried in the beam.',
    state: { explode: 0, section: false, running: true, select: 'bogie-front', focus: null },
  },
  {
    title: 'Half Section', en: 'Half Section',
    body: 'Cut along z = 0 through the side shells, skirts and the box beam: the window band and door pockets in the shell, the wrap-around bogie arms descending beside the beam, C-core levitation magnets facing the laminated stator packs, and the hollow prestressed beam core.',
    state: { explode: 0, section: true, running: true, select: 'lev-magnet-fl', focus: null },
  },
  {
    title: 'Levitation & Drive', en: 'Levitation & Drive',
    body: 'Each magnet is a chopper-fed electromagnet whose lift follows the square of its current over the gap squared: at 10 mm the four magnets under a bogie hold ≈ 300 kN. The long-stator phase is locked to position (2π·x / 258 mm), so the guideway’s travelling field and the car’s magnet fields stay synchronous — the same 10 mm gap does the lifting and the pulling.',
    state: { explode: 0, section: false, running: true, select: 'stator-pack-left', focus: 'bogie-front' },
  },
  {
    title: '3-Wave Explode', en: '3-Wave Explode',
    body: 'Wave 1 (0→0.35): the nose shell and windshield push +x, doors swing ±z, skirts split down-and-out and the roof fairing lifts. Wave 2 (0.30→0.68): side shells fly ±z, both bogies drop −y, the battery, converter and HVAC boxes pull out. Wave 3 (0.60→1.00): the four levitation magnets and four guidance magnets fan out of the arms, the stator packs and rails come off the beam ±z, sensors and brake gear clear — leaving the bare beam on its pier.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

export const CAMERA: CameraDef = {
  target: [13500, 5200, 0],
  offset: [48000, 18000, 56000],
  orthoDistance: 190000,
  exploded: { target: [13000, 4200, 0], scale: 1.7 },
  foci: {
    bogie: { target: [MG.bogieFX, 2800, 0], scale: 0.32 },
    nose: { target: [25000, 6000, 0], scale: 0.5 },
  },
};

/** Sheet dimension chains: overall length, body width, body height, beam width. */
export const DIMENSIONS = [
  { from: [0, 0, 0] as Vec3, to: [MG.carLength, 0, 0] as Vec3, view: 'front' as const, label: '27000', offset: 120 },
  { from: [MG.bogieFX, 0, 0] as Vec3, to: [MG.carLength, 0, 0] as Vec3, view: 'front' as const, label: '5500', offset: 40 },
  { from: [0, 0, 0] as Vec3, to: [MG.bogieFX, 0, 0] as Vec3, view: 'front' as const, label: '21500', offset: 40 },
  {
    from: [13500, MG.floorY, -MG.carWidth / 2] as Vec3,
    to: [13500, MG.floorY, MG.carWidth / 2] as Vec3,
    view: 'left' as const, label: '3700', offset: 64,
  },
  {
    from: [13500, MG.beamBotY, -MG.beamW / 2] as Vec3,
    to: [13500, MG.beamBotY, MG.beamW / 2] as Vec3,
    view: 'left' as const, label: '2800', offset: 120,
  },
  {
    from: [-1000, MG.floorY, 0] as Vec3,
    to: [-1000, MG.roofY, 0] as Vec3,
    view: 'front' as const, label: '4200', offset: -90,
  },
];

/** Sheet BOM balloons (leader-rail callouts). */
export const BOM = MAGLEV_BOM_CALLOUTS.map((c) => ({
  id: c.partId,
  p: c.anchor,
  code: c.code,
  title: c.title,
  material: c.material,
  qty: c.qty,
  rail: c.rail,
  elbowOffset: c.elbowOffset,
}));

export interface MaglevGroup {
  /** Full system name (tooltip). */
  system: string;
  /** Compact form shown on the callout. */
  short: string;
  colour: string;
  parts: string[];
}

/** Coloured callout groups: every part is tinted by its system. */
export const MAGLEV_GROUPS: MaglevGroup[] = [
  { system: 'Carbody & Aerodynamics', short: 'Carbody', colour: '#2563eb', parts: ['nose-cone', 'windshield', 'door-left', 'door-right', 'skirt-left', 'skirt-right', 'roof-fairing', 'side-shell-left', 'side-shell-right', 'nose-upper', 'nose-lower', 'windshield-panel', 'window-band', 'livery-blue', 'livery-orange', 'door-leaf', 'roof-panel', 'floor-pan'] },
  { system: 'Levitation & Gap Control', short: 'Levitation', colour: '#7c3aed', parts: ['lev-magnet-fl', 'lev-magnet-fr', 'lev-magnet-rl', 'lev-magnet-rr', 'gap-sensors', 'lev-pole-shoe', 'lev-coil', 'lev-core', 'sensor-head'] },
  { system: 'Guidance', short: 'Guidance', colour: '#0891b2', parts: ['guid-magnet-fl', 'guid-magnet-fr', 'guid-magnet-rl', 'guid-magnet-rr', 'guidance-rail-left', 'guidance-rail-right', 'rail-pad'] },
  { system: 'Propulsion (Long-Stator LSM)', short: 'LSM Propulsion', colour: '#dc2626', parts: ['stator-pack-left', 'stator-pack-right', 'stator-lamination', 'stator-core', 'winding-bar', 'mounting-bracket'] },
  { system: 'Braking', short: 'Braking', colour: '#ea580c', parts: ['brake-rail', 'brake-magnets', 'eddy-rail', 'brake-magnet', 'friction-skid', 'actuator'] },
  { system: 'Guideway & Structure', short: 'Guideway', colour: '#0d9488', parts: ['beam-shell', 'pier-segment', 'beam-top', 'beam-web-left', 'beam-web-right', 'walkway-edge', 'pier-cap'] },
  { system: 'Onboard Power & Equipment', short: 'Onboard Power', colour: '#b45309', parts: ['battery-box', 'hvac-unit', 'converter-cabinet', 'battery-module', 'converter', 'hvac-compressor', 'linear-pickup', 'bogie-front', 'bogie-rear', 'frame-crossbeam', 'frame-arm-left', 'frame-arm-right'] },
];

export const ANNOTATIONS: Record<string, PartAnnotation> = Object.fromEntries(
  MAGLEV_GROUPS.flatMap((g) => g.parts.map((id) => [id, { label: g.short, full: g.system, colour: g.colour } as PartAnnotation])),
);
