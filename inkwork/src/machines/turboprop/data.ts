import type { BoltSetDef, CameraDef, GuideDef, PartAnnotation, PartDef, StepDef, Vec3 } from '../types';
import { TURBOPROP_BOM_CALLOUTS } from './bom';

/**
 * Turboprop Engine (PT6A / T56 architecture)
 *
 * What it is: a free-turbine turboprop — air is compressed by three axial stages
 *   and a centrifugal impeller, burned in an annular reverse-flow combustor, and
 *   expanded through an HP turbine that drives the compressor spool plus two
 *   counter-rotating free power turbines that reach the propeller through a
 *   15:1 two-stage epicyclic reduction gearbox. The causal chain the animation
 *   shows: gas generator spins (1.0ω) → free turbine spins the other way
 *   (0.75ω) → carrier creeps (0.05ω) → the four blades turn.
 *
 * Dimensions: public PT6A / T56 layout data (≈2.2 m prop, ≈2.7 m core), no
 *   manufacturer drawings, no logos. Axial stations and explosion travel come
 *   from the assembly/explosion map (unit u, 1u = 400 mm): hub +2.65u, gearbox
 *   +1.45u, axial stages −0.55..−1.32u, impeller −1.85u, liner −2.85u, turbines
 *   −2.65..−3.35u, with each group's t=1 Δ and radial fan-out from the same map.
 *   The assembled layout stays strictly front-to-back (compressor → impeller →
 *   combustor → turbine) so nothing overlaps at t = 0; the combustor liner gets
 *   a wide bore so the turbine disks sit inside it — the real reverse-flow fold.
 *
 * Units & frame: millimetres. +x is forward (propeller), −x aft (exhaust
 *   tailcone), +y up; the shaft centreline is y = AY = 1150, z = 0; the bottom
 *   of the mounting truss is y = 0; z = 0 is the plane of symmetry. The section
 *   cut removes the z > 0 half — nacelles, gearbox casing, diffuser case and
 *   flame liner are symmetric about z = 0 and hollow, so the half-section opens
 *   them up on the main view and on the sheet's front view.
 *
 * Breakdown: 31 parts at the top level (the ink renderer's limit is 31) and six
 *   sub-assemblies with 42 parts (propeller / gearbox / airflow / compressor /
 *   combustor / turbine), reached from the structure tree.
 *
 * Motion: two concentric spools turning opposite ways plus epicyclic reduction
 *   (kinematics.ts pure functions and unit tests): gas generator 1.0ω, free
 *   turbine shaft + sun gear −0.75ω, carrier + propeller 0.05ω (15:1), and the
 *   planet gears spin at the true epicyclic ratio while fanning out radially.
 */

/** Key dimensions (mm). Shared by the model, the kinematics and the text. 1u = 400 mm. */
export const TP = {
  AY: 1150,
  u: 400,
  /* Axial stations (+x forward; map values × 400). */
  tailX: -1620,
  exhaustX0: -1380,
  pt2X: -1340, pt1X: -1200, hpX: -1060, ngvX: -980, baffleX: -1000,
  linerX0: -1370, linerX1: -910,
  caseX0: -1420, caseX1: 300,
  impellerX: -740,
  stator3X: -604, rotor3X: -528, stator2X: -452, rotor2X: -374, stator1X: -296, rotor1X: -220,
  bearingX: -60,
  gearX0: 320, gearX1: 860, gearMidX: 580,
  torqueX: 700,
  intakeX: 150,
  lockRingX: 900,
  hubX: 1060,
  spinnerX0: 924, spinnerX1: 1532,
  /* Radii. */
  propR: 1080,           // blade tip radius (Ø2160)
  bladeRootR: 250,
  hubR: 250,
  caseR: 330,
  gearboxR: 270,
  linerInR: 220, linerOutR: 300,
  impellerR: 230,
  rotorTipR: [210, 195, 180] as const,
  statorOuterR: 215,
  hpR: 165, ptR: 180,
  shaftR: 62,
  /* Two-stage epicyclic. */
  sunTeeth: 16, planetTeeth: 24, ringTeeth: 64, planets: 5,
  sunTeeth2: 16, planetTeeth2: 8, ringTeeth2: 32, planets2: 4,
  bladeCounts: [33, 29, 27] as const,
  statorCounts: [23, 21, 19] as const,
  wall: 18,
};

export const AY = TP.AY;
const U = TP.u;
const ux = (n: number): number => n * U;

/**
 * 31 parts (indices 1–31 = the drawing balloon numbers).
 * Three-wave teardown: W1 fasteners & skins 0→0.35, W2 major groups 0.30→0.68,
 * W3 internals 0.60→1.00. explode vectors are the map's Δ and radial fan-outs.
 */
export const PARTS: PartDef[] = [
  /* ── Wave 1 · fasteners & outer skins ──────────────────────────── */
  {
    id: 'spinner', index: 1, name: 'Spinner Dome (two-piece)', en: 'Spinner Dome', role: 'Fairing',
    material: 'Glass fibre',
    description: 'Parabolic double-walled spinner cone plus an aft bulkhead backplate (two-piece, with four blade-root cutouts), polished for drag.',
    explode: [ux(3.35), 0, 0], stage: [0, 0.22],
  },
  {
    id: 'pitch-lock-ring', index: 2, name: 'Pitch-Lock Bolt Ring', en: 'Pitch-Lock Bolt Ring', role: 'Locks pitch',
    material: '30CrMnSiA steel',
    description: 'Twelve M10 high-strength bolts around the circumference lock the pitch piston; torque 45 N·m, and they back out ahead of the flange.',
    explode: [ux(2.6), 0, 0], stage: [0.05, 0.28],
  },
  {
    id: 'cowl-upper', index: 3, name: 'Upper Nacelle Cowl', en: 'Upper Nacelle Cowl', role: 'Fairing',
    material: 'Aluminium skin',
    description: 'Upper nacelle shell, 18 mm wall, hollow and symmetric about z = 0 — the half-section opens it to show the compressor and combustor case.',
    explode: [0, ux(2.4), 0], stage: [0, 0.35],
  },
  {
    id: 'cowl-lower', index: 4, name: 'Lower Nacelle Cowl', en: 'Lower Nacelle Cowl', role: 'Fairing · intake',
    material: 'Aluminium skin',
    description: 'Lower nacelle shell with the intake lip and drain points; riveted to the upper cowl along the z = 0 split line with 24 rivets.',
    explode: [0, -ux(2.4), 0], stage: [0, 0.35],
  },
  {
    id: 'combustor-case-a', index: 5, name: 'Outer Case (right half)', en: 'Outer Case (Right Half)', role: 'Pressure shell',
    material: 'GH4169 superalloy',
    description: 'Right half of the compressor–diffuser–combustor outer case, 660 mm bore, 18 mm wall, twelve flange bolt bosses; carries 4×10⁵ Pa internal pressure.',
    explode: [0, 0, ux(1.8)], stage: [0.02, 0.35],
  },
  {
    id: 'combustor-case-b', index: 6, name: 'Outer Case (left half)', en: 'Outer Case (Left Half)', role: 'Pressure shell',
    material: 'GH4169 superalloy',
    description: 'Left half of the outer case, bolted to the right half at the horizontal split; the inner wall carries 14 nozzle bosses and 2 igniter ports.',
    explode: [0, 0, -ux(1.8)], stage: [0.02, 0.35],
  },

  /* ── Wave 2 · major groups ─────────────────────────────────────── */
  {
    id: 'prop-hub', index: 7, name: 'Prop Hub & Pitch Dome', en: 'Prop Hub & Pitch Dome', role: 'Torque · pitch',
    material: '20CrMo forged steel',
    description: 'Four-arm forged hub spider (four blade-root sockets) with the hydraulic pitch-change cylinder (±25° travel); map Δ +2.30u.',
    explode: [ux(2.3), 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'gearbox', index: 8, name: 'Reduction Gearbox Housing', en: 'Reduction Gearbox Housing', role: 'Structural',
    material: 'AZ91C magnesium',
    description: 'Two-stage epicyclic gearbox casing (with torque-meter barrel and intake screen), 16 mm wall; the half-section reveals the five first-stage planets.',
    explode: [ux(1.35), 0, 0], stage: [0.34, 0.66],
    deep: [ux(2.4), 0, 0],
  },
  {
    id: 'exhaust', index: 9, name: 'Exhaust Ducts & Tailcone', en: 'Exhaust Ducts & Tailcone', role: 'Exhaust',
    material: 'Inconel 625',
    description: 'Twin exhaust stubs (220 mm bore, canted up 15°) and the tailcone travel aft together; exhaust gas ≈ 700 °C.',
    explode: [-ux(2.2), 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'fuel-manifold', index: 10, name: 'Fuel Manifold & Nozzles', en: 'Fuel Manifold & Nozzles', role: 'Fuel · atomisation',
    material: '1Cr18Ni9Ti stainless',
    description: 'Annular fuel manifold with 14 swirl-cup nozzles and two igniter plugs; radial fan-out +0.90u per the map (Fuel Nozzles).',
    explode: [0, ux(0.9), 0], stage: [0.3, 0.6],
  },
  {
    id: 'accessory-drive', index: 11, name: 'Accessory Drive Group', en: 'Accessory Drive Group', role: 'Accessory drive',
    material: '18Cr2Ni4WA steel',
    description: 'Bevel gear pair (27/27 teeth) with the starter-generator pad and the high-pressure fuel pump housing; pulled radially −y by 1.2u.',
    explode: [0, -ux(1.2), 0], stage: [0.32, 0.62],
  },

  /* ── Wave 3 · internal telescoping & radial fan-out ─────────────── */
  {
    id: 'blade-1', index: 12, name: 'Blade 1', en: 'Blade 1', role: 'Thrust · up',
    material: 'TC4 titanium',
    description: 'Constant-speed blade: 48°→16° root-to-tip washout, pitch axis at 42% chord, counterweight clamp ring; radial fan +1.15u.',
    explode: [0, ux(1.15), 0], stage: [0.6, 0.85],
  },
  {
    id: 'blade-2', index: 13, name: 'Blade 2', en: 'Blade 2', role: 'Thrust · down',
    material: 'TC4 titanium',
    description: 'Same blade at 180°, radial −1.15u; root flange takes six M16 bolts torqued to 120 N·m.',
    explode: [0, -ux(1.15), 0], stage: [0.6, 0.85],
  },
  {
    id: 'blade-3', index: 14, name: 'Blade 3', en: 'Blade 3', role: 'Thrust · right',
    material: 'TC4 titanium',
    description: 'At 90°, radial +1.15u; solid titanium spar with a stainless erosion strip along the leading edge.',
    explode: [0, 0, ux(1.15)], stage: [0.62, 0.87],
  },
  {
    id: 'blade-4', index: 15, name: 'Blade 4', en: 'Blade 4', role: 'Thrust · left',
    material: 'TC4 titanium',
    description: 'At 270°, radial −1.15u; four blades spaced 90° apart, centrifugal load ≈ 68 kN per blade.',
    explode: [0, 0, -ux(1.15)], stage: [0.62, 0.87],
  },
  {
    id: 'sun-gear', index: 16, name: 'Sun Gear Shaft', en: 'Sun Gear Shaft', role: 'Input · 16 teeth',
    material: 'Case-hardened 18Cr2Ni4WA',
    description: 'Sun gear on the free-turbine shaft nose (16 teeth, module 5): the innermost telescoping section, +0.75u (0.35u per element).',
    explode: [ux(0.75), 0, 0], stage: [0.6, 0.8],
  },
  {
    id: 'planet-gears', index: 17, name: 'Planet Gears ×5', en: 'Planet Gears ×5', role: 'Differential · 24 teeth',
    material: 'Case-hardened 18Cr2Ni4WA',
    description: 'Five first-stage planets (24 teeth) spaced on the Ø210 pin circle; +0.40u along x and +0.55u radially along their own pins.',
    explode: [ux(0.4), 0, 0], stage: [0.63, 0.83],
  },
  {
    id: 'planet-carrier', index: 18, name: 'Planet Carrier & Pins', en: 'Planet Carrier & Pins', role: 'Output',
    material: '20CrMo forged steel',
    description: 'Carrier cage (front and aft plates) with five hollow planet pins (Ø42, Ø16 oil bore); +0.05u.',
    explode: [ux(0.05), 0, 0], stage: [0.66, 0.86],
  },
  {
    id: 'ring-gear', index: 19, name: 'Ring Gear', en: 'Ring Gear', role: 'Fixed · 64 teeth',
    material: 'Nitrided 42CrMo',
    description: 'First-stage internal ring gear (64 teeth) shrunk into the casing wall; the fixed ring gives the ratio (1 + 64/16) × (1 + 32/16) = 15:1.',
    explode: [-ux(0.3), 0, 0], stage: [0.69, 0.89],
  },
  {
    id: 'rotor-1', index: 20, name: 'Compressor Rotor 1', en: 'Compressor Rotor 1', role: 'Boost · 33 blades',
    material: 'TC11 titanium',
    description: 'First axial stage: Ø420 disk, 33 twisted cambered blades (32° stagger, 16° tip twist), fir-tree rim slots.',
    explode: [ux(0.5), 0, 0], stage: [0.62, 0.88],
  },
  {
    id: 'rotor-2', index: 21, name: 'Compressor Rotor 2', en: 'Compressor Rotor 2', role: 'Boost · 29 blades',
    material: 'TC11 titanium',
    description: 'Second stage: Ø390 disk, 29 blades at 38° stagger; the rotor chain opens by −0.50u per stage (map: 0.50u/stage).',
    explode: [0, 0, 0], stage: [0.64, 0.9],
  },
  {
    id: 'rotor-3', index: 22, name: 'Compressor Rotor 3', en: 'Compressor Rotor 3', role: 'Boost · 27 blades',
    material: 'TC11 titanium',
    description: 'Third stage: Ø360 disk, 27 blades at 44° stagger; total pressure ratio across the three stages ≈ 4:1.',
    explode: [-ux(0.5), 0, 0], stage: [0.66, 0.92],
  },
  {
    id: 'stator-1', index: 23, name: 'Stator Ring 1', en: 'Stator Ring 1', role: 'Guide · 23 vanes',
    material: 'GH4169',
    description: 'First stator, 23 vanes, turns the flow back axial before stage two; radial fan +0.85u (map: Stators).',
    explode: [0, ux(0.85), 0], stage: [0.63, 0.89],
  },
  {
    id: 'stator-2', index: 24, name: 'Stator Ring 2', en: 'Stator Ring 2', role: 'Guide · 21 vanes',
    material: 'GH4169',
    description: 'Second stator, 21 vanes, 52 mm chord height; radial +0.85u, interleaved with the rotors with zero overlap.',
    explode: [0, ux(0.85), 0], stage: [0.65, 0.91],
  },
  {
    id: 'stator-3', index: 25, name: 'Stator Ring 3', en: 'Stator Ring 3', role: 'Guide · 19 vanes',
    material: 'GH4169',
    description: 'Third stator, 19 vanes, ahead of the impeller eye; radial +0.85u, located in the casing by 24 radial pins.',
    explode: [0, ux(0.85), 0], stage: [0.67, 0.93],
  },
  {
    id: 'impeller', index: 26, name: 'Centrifugal Impeller & Diffuser', en: 'Centrifugal Impeller & Diffuser', role: 'Boost · diffusion',
    material: 'TC4 titanium',
    description: 'Single centrifugal stage: 12 full + 12 splitter swept vanes on a parabolic meridional hub, 38° backsweep, with 12 radial diffuser pipes.',
    explode: [-ux(0.9), 0, 0], stage: [0.68, 0.94],
  },
  {
    id: 'combustor-liner', index: 27, name: 'Flame Liner', en: 'Combustion Flame Liner', role: 'Burn · mix',
    material: 'GH3044',
    description: 'Reverse-flow annular flame liner (600 mm outer, 440 mm bore so the turbine disks sit inside), five rows of flanged dilution grommets.',
    explode: [-ux(1.25), 0, 0], stage: [0.7, 0.95],
  },
  {
    id: 'hp-turbine', index: 28, name: 'HP Turbine Stage', en: 'HP Turbine Stage', role: 'Drives compressor',
    material: 'Directionally-solidified superalloy',
    description: 'Nozzle guide vane ring (34 vanes) plus the HP turbine disk (29 blades) and inter-stage baffle; map Δ −2.55u down the turbine chain.',
    explode: [-ux(2.55), 0, 0], stage: [0.72, 0.96],
  },
  {
    id: 'pt-disk-1', index: 29, name: 'Power Turbine Disk 1', en: 'Power Turbine Disk 1', role: 'Output · 31 blades',
    material: 'FGH96 powder alloy',
    description: 'First free power turbine stage (31 blades) on the concentric inner shaft, counter-rotating (−0.75ω); Δ −2.85u.',
    explode: [-ux(2.85), 0, 0], stage: [0.74, 0.97],
  },
  {
    id: 'pt-disk-2', index: 30, name: 'Power Turbine Disk 2 & Shaft', en: 'Power Turbine Disk 2 & Shaft', role: 'Output · 33 blades',
    material: 'FGH96 powder alloy',
    description: 'Second stage (33 blades) with the Ø124 inner shaft (two labyrinth seal packs) that carries power forward to the sun gear; Δ −3.15u.',
    explode: [-ux(3.15), 0, 0], stage: [0.76, 0.98],
  },
  {
    id: 'mount-truss', index: 31, name: 'Mounting Truss', en: 'Mounting Truss', role: 'Base · structure',
    material: '30CrMnSiA tube',
    description: 'Four-tube welded space truss (Ø45×3), lowest point at y = 0, upper ends at the gearbox casing main fittings.',
    explode: [0, 0, 0], stage: [1, 1],
  },
];

/** Parts that come apart together on a local explode. */
export const NEIGHBOURS: Record<string, string[]> = {
  'prop-hub': ['spinner', 'pitch-lock-ring', 'blade-1', 'blade-2', 'blade-3', 'blade-4', 'prop-hub'],
  spinner: ['pitch-lock-ring', 'spinner'],
  'pitch-lock-ring': ['spinner', 'pitch-lock-ring'],
  gearbox: ['ring-gear', 'planet-carrier', 'planet-gears', 'sun-gear', 'gearbox'],
  'planet-gears': ['sun-gear', 'planet-carrier', 'ring-gear', 'planet-gears'],
  'sun-gear': ['planet-gears', 'sun-gear'],
  impeller: ['stator-3', 'rotor-3', 'impeller'],
  'hp-turbine': ['pt-disk-1', 'pt-disk-2', 'hp-turbine'],
  exhaust: ['combustor-liner', 'exhaust'],
};

export const BOLT_SETS: Record<string, BoltSetDef> = {
  'pitch-bolts': { owner: 'pitch-lock-ring', distance: 220, stage: [0, 0.1] },
  'case-bolts': { owner: 'combustor-case-a', distance: 140, stage: [0.02, 0.12] },
  'gear-bolts': { owner: 'gearbox', distance: 160, stage: [0.3, 0.42] },
};

export const GUIDES: GuideDef[] = [
  { stage: 'spinner', origin: [TP.spinnerX1 - 120, TP.AY + 200, 0] },
  { stage: 'prop-hub', origin: [TP.hubX, TP.AY + 320, 0] },
  { stage: 'gearbox', origin: [TP.gearX1 - 60, TP.AY + 300, 0] },
  { stage: 'exhaust', origin: [TP.tailX + 80, TP.AY + 160, 0] },
  { stage: 'cowl-upper', origin: [-200, TP.AY + TP.caseR + 60, 0] },
  { stage: 'blade-1', origin: [TP.hubX, TP.AY + 700, 0] },
  { stage: 'combustor-liner', origin: [TP.linerX1 - 120, TP.AY + 120, 0] },
  { stage: 'sun-gear', origin: [TP.gearMidX + 60, TP.AY + 100, 0] },
];

export const CENTRE_LINES: Array<[Vec3, Vec3, number?]> = [
  [[TP.tailX - 60, TP.AY, 0], [TP.spinnerX1 + 60, TP.AY, 0], TP.impellerR],
  [[TP.gearMidX, TP.AY, 0], [TP.gearMidX, TP.AY, 0], 260],
];

export const STEPS: StepDef[] = [
  {
    title: 'Assembly', en: 'Assembly',
    body: 'The whole turboprop: a four-blade constant-speed propeller up front, the magnesium reduction gearbox mid-way, then the axial-centrifugal compressor, the reverse-flow combustor and the two free power turbines. Running: the gas generator turns at 1.0ω, the free turbine the other way at 0.75ω, and the propeller crawls at 0.05ω through the 15:1 planetary reduction.',
    state: { explode: 0, section: false, running: true, select: 'prop-hub', focus: null },
  },
  {
    title: 'Half Section', en: 'Half Section',
    body: 'Cut along z = 0 through the nacelles, gearbox casing, diffuser case and flame liner: five first-stage planets orbit the sun gear up front, three axial rotors and stators interleave mid-engine, and the double-walled flame liner wraps the HP turbine and the two counter-rotating free turbines with labyrinth seals along the inner shaft.',
    state: { explode: 0, section: true, running: true, select: 'planet-gears', focus: null },
  },
  {
    title: 'Power Train', en: 'Power Train',
    body: 'Two planetary stages: 16/24/64 (5:1) and 16/8/32 (3:1) — fifteen to one in total. The ring gear is fixed, the sun gear runs backwards with the free turbine shaft, and five planets walk their pins to turn the carrier — that is the whole trick behind a fast turbine and a slow propeller.',
    state: { explode: 0, section: false, running: true, select: 'sun-gear', focus: 'gearbox' },
  },
  {
    title: '3-Wave Explode', en: '3-Wave Explode',
    body: 'Wave 1 (0→0.35): the spinner leaves at +3.35u and the bolt ring backs out; the cowls split ±2.4u and the outer case halves ±1.8u. Wave 2 (0.30→0.68): prop hub +2.30u, gearbox +1.35u, exhaust group −2.20u, fuel and accessories pull radially. Wave 3 (0.60→1.00): blades fan +1.15u, the gear train telescopes 0.35u per element with the planets also fanning +0.55u, rotor stages step −0.50u, stator rings rise +0.85u and the turbine chain drops Δ −2.55..−3.15u — every blade row visible, zero overlap.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

export const CAMERA: CameraDef = {
  target: [-40, TP.AY - 40, 0],
  offset: [3380, 1360, 3980],
  orthoDistance: 10000,
  exploded: { target: [-160, TP.AY, 0], scale: 1.62 },
  foci: {
    gearbox: { target: [TP.gearMidX, TP.AY, 0], scale: 0.42 },
    combustor: { target: [-1140, TP.AY, 0], scale: 0.5 },
  },
};

/** Sheet dimension chains: overall length + segment chain + rotor diameter. */
export const DIMENSIONS = [
  { from: [TP.tailX, 0, 0] as Vec3, to: [TP.spinnerX1, 0, 0] as Vec3, view: 'front' as const, label: '3152', offset: 116 },
  { from: [TP.gearX0, 0, 0] as Vec3, to: [TP.gearX1, 0, 0] as Vec3, view: 'front' as const, label: '540', offset: 34 },
  { from: [TP.caseX0, 0, 0] as Vec3, to: [TP.gearX0, 0, 0] as Vec3, view: 'front' as const, label: '1740', offset: 66 },
  { from: [TP.tailX, 0, 0] as Vec3, to: [TP.caseX0, 0, 0] as Vec3, view: 'front' as const, label: '200', offset: 34 },
  { from: [TP.gearX1, 0, 0] as Vec3, to: [TP.spinnerX1, 0, 0] as Vec3, view: 'front' as const, label: '672', offset: 34 },
  {
    from: [TP.rotor1X, TP.AY - TP.rotorTipR[0], 0] as Vec3,
    to: [TP.rotor1X, TP.AY + TP.rotorTipR[0], 0] as Vec3,
    view: 'left' as const, label: 'Ø420', offset: 64,
  },
  {
    from: [TP.hubX, TP.AY - TP.propR, 0] as Vec3,
    to: [TP.hubX, TP.AY + TP.propR, 0] as Vec3,
    view: 'left' as const, label: 'Ø2160', offset: 120,
  },
  {
    from: [-1140, TP.AY - 332, 0] as Vec3,
    to: [-1140, TP.AY + 332, 0] as Vec3,
    view: 'front' as const, label: 'Ø664', offset: -90,
  },
];

/** Sheet BOM balloons: leader-rail callouts (code / material / qty / rail). */
export const BOM = TURBOPROP_BOM_CALLOUTS.map((c) => ({
  id: c.partId,
  p: c.anchor,
  code: c.code,
  title: c.title,
  material: c.material,
  qty: c.qty,
  rail: c.rail,
  elbowOffset: c.elbowOffset,
}));

/**
 * V8 / browser-engine ↔ turboprop pairing. Each pair owns a colour: its parts'
 * callout balloons, leaders and hover/selection accents all render in it, with
 * the browser-component label under the part name.
 */
export interface V8Group {
  /** Browser (V8) component (full name). */
  v8: string;
  /** Compact form used on the callout. */
  short: string;
  /** The engine subsystem it stands for. */
  system: string;
  colour: string;
  /** Part ids across the top level and the sub-assemblies. */
  parts: string[];
}

export const V8_GROUPS: V8Group[] = [
  {
    v8: 'v8::Isolate', short: 'v8::Isolate', system: 'Complete Under-Wing Engine Pod & Nacelle', colour: '#6d28d9',
    parts: ['cowl-upper', 'cowl-lower', 'combustor-case-a', 'combustor-case-b', 'outer-case', 'gearbox-casing'],
  },
  {
    v8: 'Parser & Pre-Parser', short: 'Parser & Pre-Parser', system: 'Front Intake Cowling & Debris Splitter Lip', colour: '#0e7490',
    parts: ['spinner', 'spinner-front', 'spinner-aft', 'inlet-screen', 'front-bearing-housing'],
  },
  {
    v8: 'Hidden Classes (Map) & Inline Caches (IC)', short: 'Hidden Classes & ICs', system: 'Variable Inlet Guide Vanes & FADEC Pressure Sensors', colour: '#047857',
    parts: ['stator-1', 'stator-2', 'stator-3', 'ngv-ring'],
  },
  {
    v8: 'Ignition (Bytecode Interpreter)', short: 'Ignition Interpreter', system: 'Pneumatic Air-Turbine Starter & Igniter Box', colour: '#b45309',
    parts: ['fuel-manifold', 'accessory-drive', 'igniter-plugs', 'starter-gen-pad', 'fuel-pump-housing', 'bevel-drive-gear'],
  },
  {
    v8: 'Sparkplug & Maglev (Baseline / Mid-Tier JITs)', short: 'Sparkplug & Maglev', system: 'Low-Pressure Fan Spool (N1) & Booster Compressor', colour: '#b91c1c',
    parts: ['blade-1', 'blade-2', 'blade-3', 'blade-4', 'prop-hub', 'hub-spider', 'pitch-dome', 'rotor-1', 'rotor-2', 'rotor-3'],
  },
  {
    v8: 'TurboFan & Turboshaft (Optimizing JIT & Back-End)', short: 'TurboFan & Turboshaft', system: 'High-Pressure Compressor Core (N2), Combustor & Reduction Gearbox', colour: '#4338ca',
    parts: ['impeller', 'combustor-liner', 'flame-liner', 'hp-turbine', 'hp-turbine-disk', 'sun-gear', 'planet-gears', 'planet-carrier', 'ring-gear', 'gear-train', 'diffuser-pipes', 'nozzle-bosses', 'manifold-tubing'],
  },
  {
    v8: 'Deoptimizer', short: 'Deoptimizer', system: 'Compressor Surge Bleed Valves & Pressure Dump Gates', colour: '#c2410c',
    parts: ['exhaust', 'exhaust-stubs', 'tailcone', 'pt-disk-1', 'pt-disk-2'],
  },
  {
    v8: 'Orinoco & Oilpan (Garbage Collectors)', short: 'Orinoco & Oilpan', system: 'Under-Slung Dry-Sump Scavenge Pump & Magnetic Chip Separator', colour: '#0f766e',
    parts: ['gearbox', 'scavenge-pump-gear', 'torque-meter', 'bearing-inner', 'bearing-outer', 'bearing-cage'],
  },
  {
    v8: 'V8 Sandbox & Pointer Tables (EPT / IPT)', short: 'V8 Sandbox & EPT/IPT', system: 'Kevlar-Titanium Blade-Containment Ring & Sealed Firewall Bulkhead', colour: '#be185d',
    parts: ['pitch-lock-ring', 'mount-truss', 'inter-baffle', 'inner-shaft'],
  },
];

/** Part id → callout annotation (colour + browser-component label). */
export const ANNOTATIONS: Record<string, PartAnnotation> = Object.fromEntries(
  V8_GROUPS.flatMap((g) => g.parts.map((id) => [id, { label: g.short, full: g.v8, colour: g.colour } as PartAnnotation])),
);
