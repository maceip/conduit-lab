import type { Vec3 } from '../types';

/**
 * BOM callout, leader-line & dimension configuration (ported from the
 * Gemini "Isometric and Exploded-View" brief, adapted to this engine).
 *
 * Anchors live in millimetres on the assembled model; `resolveLiveCallouts`
 * adds each part's explosion travel so the leaders track their parts from
 * t = 0 to t = 1. Leaders dock to a top or bottom horizontal callout rail
 * through an elbow so they never cross the engine core like spaghetti.
 */

export interface BomCalloutSpec {
  /** Drawing balloon number (matches PARTS index). */
  bomNumber: number;
  /** Part id in PARTS. */
  partId: string;
  /** Sheet code, e.g. TP-101. */
  code: string;
  title: string;
  material: string;
  qty: number;
  /** Attachment point on the part, assembled, millimetres, engine frame. */
  anchor: Vec3;
  /** Leader routing dock — keeps leaders off the engine core. */
  rail: 'top' | 'bottom';
  /** Elbow offset [dx, dy] in sheet pixels before snapping to the rail. */
  elbowOffset: [number, number];
}

export const TURBOPROP_BOM_CALLOUTS: BomCalloutSpec[] = [
  { bomNumber: 1, partId: 'spinner', code: 'TP-101', title: 'Two-Piece Parabolic Spinner Dome', material: 'Glass fibre, anti-icing mat', qty: 1, anchor: [1420, 260, 0], rail: 'top', elbowOffset: [26, -40] },
  { bomNumber: 2, partId: 'pitch-lock-ring', code: 'TP-102', title: 'Pitch-Lock Bolt Ring', material: '30CrMnSiA (12× M10)', qty: 12, anchor: [900, 320, 90], rail: 'bottom', elbowOffset: [18, 52] },
  { bomNumber: 3, partId: 'cowl-upper', code: 'TP-111', title: 'Upper Nacelle Cowl', material: 'Aluminium skin, 18 mm wall', qty: 1, anchor: [-160, 420, 60], rail: 'top', elbowOffset: [-30, -46] },
  { bomNumber: 4, partId: 'cowl-lower', code: 'TP-112', title: 'Lower Nacelle Cowl', material: 'Aluminium skin, 18 mm wall', qty: 1, anchor: [-160, -420, 60], rail: 'bottom', elbowOffset: [-30, 50] },
  { bomNumber: 5, partId: 'combustor-case-a', code: 'TP-113', title: 'Outer Pressure Case (right half)', material: 'GH4169 superalloy', qty: 1, anchor: [-420, 420, 130], rail: 'top', elbowOffset: [-24, -44] },
  { bomNumber: 6, partId: 'combustor-case-b', code: 'TP-114', title: 'Outer Pressure Case (left half)', material: 'GH4169 superalloy', qty: 1, anchor: [-420, -420, -130], rail: 'bottom', elbowOffset: [-24, 48] },
  { bomNumber: 7, partId: 'prop-hub', code: 'TP-201', title: 'Four-Arm Hub Spider & Pitch Dome', material: '20CrMo forged steel', qty: 1, anchor: [1100, 330, 110], rail: 'top', elbowOffset: [30, -52] },
  { bomNumber: 8, partId: 'gearbox', code: 'TP-202', title: 'Reduction Gearbox Housing', material: 'AZ91C magnesium, 16 mm wall', qty: 1, anchor: [430, 340, 120], rail: 'top', elbowOffset: [12, -48] },
  { bomNumber: 9, partId: 'exhaust', code: 'TP-701', title: 'Exhaust Duct Stubs & Tailcone', material: 'Inconel 625', qty: 1, anchor: [-1480, 300, 140], rail: 'bottom', elbowOffset: [-34, 54] },
  { bomNumber: 10, partId: 'fuel-manifold', code: 'TP-504', title: 'Fuel Manifold & 14 Swirl-Cup Nozzles', material: '1Cr18Ni9Ti stainless', qty: 14, anchor: [-1250, -330, 100], rail: 'bottom', elbowOffset: [-16, 46] },
  { bomNumber: 11, partId: 'accessory-drive', code: 'TP-305', title: 'Accessory Bevel Drive & Pads', material: '18Cr2Ni4WA / 2A14 aluminium', qty: 1, anchor: [220, -520, 120], rail: 'bottom', elbowOffset: [20, 58] },
  { bomNumber: 12, partId: 'blade-1', code: 'TP-211', title: 'Propeller Blade 1', material: 'TC4 titanium, 48°→16° washout', qty: 4, anchor: [1300, 860, 120], rail: 'top', elbowOffset: [36, -60] },
  { bomNumber: 16, partId: 'sun-gear', code: 'TP-204', title: 'Sun Gear Shaft (16 teeth)', material: 'Case-hardened 18Cr2Ni4WA', qty: 1, anchor: [840, 380, 70], rail: 'top', elbowOffset: [22, -44] },
  { bomNumber: 17, partId: 'planet-gears', code: 'TP-205', title: 'First-Stage Planet Gears ×5 (24 teeth)', material: 'Case-hardened 18Cr2Ni4WA', qty: 5, anchor: [440, 560, 80], rail: 'top', elbowOffset: [-10, -50] },
  { bomNumber: 18, partId: 'planet-carrier', code: 'TP-206', title: 'Planet Carrier & Hollow Pins', material: '20CrMo forged steel', qty: 1, anchor: [620, -420, 80], rail: 'bottom', elbowOffset: [8, 54] },
  { bomNumber: 19, partId: 'ring-gear', code: 'TP-207', title: 'Fixed Ring Gear (64 teeth)', material: 'Nitrided 42CrMo', qty: 1, anchor: [340, 250, 70], rail: 'top', elbowOffset: [-28, -46] },
  { bomNumber: 20, partId: 'rotor-1', code: 'TP-401', title: 'Compressor Rotor Stage 1 (33 blades)', material: 'TC11 titanium', qty: 1, anchor: [-80, 340, 70], rail: 'top', elbowOffset: [-18, -48] },
  { bomNumber: 23, partId: 'stator-1', code: 'TP-411', title: 'Stator Ring 1 (23 vanes)', material: 'GH4169', qty: 3, anchor: [-296, 355, -70], rail: 'bottom', elbowOffset: [-12, 50] },
  { bomNumber: 26, partId: 'impeller', code: 'TP-420', title: 'Centrifugal Impeller & Diffuser Pipes', material: 'TC4 titanium, 38° backsweep', qty: 1, anchor: [-680, 320, 80], rail: 'top', elbowOffset: [-26, -52] },
  { bomNumber: 27, partId: 'combustor-liner', code: 'TP-501', title: 'Reverse-Flow Flame Liner', material: 'GH3044, double wall', qty: 1, anchor: [-1010, 330, 80], rail: 'top', elbowOffset: [-30, -46] },
  { bomNumber: 28, partId: 'hp-turbine', code: 'TP-601', title: 'HP Turbine Stage (NGV + disk)', material: 'DS superalloy', qty: 1, anchor: [-940, 240, 70], rail: 'bottom', elbowOffset: [-18, 52] },
  { bomNumber: 29, partId: 'pt-disk-1', code: 'TP-605', title: 'Free Power Turbine Disk 1 (31 blades)', material: 'FGH96 powder alloy', qty: 2, anchor: [-1040, 230, 70], rail: 'bottom', elbowOffset: [-30, 56] },
  { bomNumber: 31, partId: 'mount-truss', code: 'TP-710', title: 'Mounting Truss', material: '30CrMnSiA tube, y = 0 base', qty: 1, anchor: [580, 140, 280], rail: 'bottom', elbowOffset: [24, 60] },
];

const smooth = (t: number) => {
  const x = Math.min(1, Math.max(0, t));
  return x * x * (3 - 2 * x);
};

export interface LiveCallout extends BomCalloutSpec {
  /** Anchor moved by the part's explosion travel (millimetres). */
  anchor3D: Vec3;
}

/**
 * Live attachment points: each anchor rides its part's explode vector over the
 * part's own stage window, so leaders track the parts from t = 0 to t = 1.
 * `explodes` maps part id → [explode vector, stage window] in millimetres.
 */
export function resolveLiveCallouts(
  t: number,
  explodes: Record<string, { explode: Vec3; stage: [number, number] }>,
): LiveCallout[] {
  return TURBOPROP_BOM_CALLOUTS.map((item) => {
    const e = explodes[item.partId];
    let w = 0;
    if (e && e.stage[1] > e.stage[0]) w = smooth((t - e.stage[0]) / (e.stage[1] - e.stage[0]));
    const [ex, ey, ez] = e ? e.explode : [0, 0, 0];
    return {
      ...item,
      anchor3D: [item.anchor[0] + ex * w, item.anchor[1] + ey * w, item.anchor[2] + ez * w],
    };
  });
}
