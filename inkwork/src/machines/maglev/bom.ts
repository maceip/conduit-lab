import type { Vec3 } from '../types';

// Local copies of the layout stations (mirrors MG in data.ts) — this module
// must not import data.ts, which imports this one for the BOM table.
const MG = {
  floorY: 3400, roofY: 7600, beamTopY: 3400, beamBotY: 1200,
  bogieFX: 21500, bogieRX: 4500, doorFX: 21000, noseX: 27000,
};

/**
 * BOM callout, leader-line & dimension configuration for the maglev sheet —
 * same rail/elbow scheme as the turboprop plate: anchors in millimetres on the
 * assembled model, leaders dock to a top or bottom rail through an elbow, and
 * the anchors ride each part's explosion travel so leaders track parts t=0→1.
 */

export interface BomCalloutSpec {
  bomNumber: number;
  partId: string;
  code: string;
  title: string;
  material: string;
  qty: number;
  anchor: Vec3;
  rail: 'top' | 'bottom';
  elbowOffset: [number, number];
}

const F = MG.floorY;
const B = MG.beamBotY;

export const MAGLEV_BOM_CALLOUTS: BomCalloutSpec[] = [
  { bomNumber: 1, partId: 'nose-cone', code: 'MV-101', title: 'Aerodynamic Nose Shell', material: 'GFRP sandwich', qty: 1, anchor: [25800, F + 1600, 0], rail: 'top', elbowOffset: [30, -46] },
  { bomNumber: 2, partId: 'windshield', code: 'MV-102', title: 'Twin-Pane Windshield Panel', material: 'Laminated glass', qty: 1, anchor: [25200, F + 2600, 0], rail: 'top', elbowOffset: [18, -52] },
  { bomNumber: 3, partId: 'door-left', code: 'MV-111', title: 'Plug Door (left)', material: 'Aluminium honeycomb', qty: 2, anchor: [MG.doorFX, F + 1100, 1850], rail: 'bottom', elbowOffset: [-20, 50] },
  { bomNumber: 5, partId: 'skirt-left', code: 'MV-113', title: 'Undercar Skirt (left)', material: 'GFRP', qty: 2, anchor: [15000, F - 500, 1700], rail: 'bottom', elbowOffset: [-12, 54] },
  { bomNumber: 7, partId: 'roof-fairing', code: 'MV-115', title: 'Roof Fairing & HVAC Cover', material: 'Aluminium sheet', qty: 1, anchor: [15000, MG.roofY + 120, 0], rail: 'top', elbowOffset: [-26, -44] },
  { bomNumber: 8, partId: 'side-shell-left', code: 'MV-121', title: 'Side Shell (left)', material: 'Aluminium 6082', qty: 2, anchor: [10000, F + 2100, 1850], rail: 'top', elbowOffset: [-16, -50] },
  { bomNumber: 10, partId: 'bogie-front', code: 'MV-201', title: 'Front Levitation Bogie', material: 'Welded S355 steel', qty: 2, anchor: [MG.bogieFX, B + 300, 1500], rail: 'bottom', elbowOffset: [22, 56] },
  { bomNumber: 12, partId: 'battery-box', code: 'MV-301', title: 'Onboard Battery Box', material: 'NiCd 110 V / 200 Ah', qty: 1, anchor: [9000, F - 700, 0], rail: 'bottom', elbowOffset: [-18, 50] },
  { bomNumber: 13, partId: 'hvac-unit', code: 'MV-302', title: 'HVAC Unit', material: 'Aluminium casing', qty: 1, anchor: [13000, MG.roofY + 80, 0], rail: 'top', elbowOffset: [-22, -42] },
  { bomNumber: 14, partId: 'converter-cabinet', code: 'MV-303', title: 'Converter & Control Cabinet', material: 'Sheet steel', qty: 2, anchor: [16000, F - 800, -900], rail: 'bottom', elbowOffset: [16, 52] },
  { bomNumber: 15, partId: 'lev-magnet-fl', code: 'MV-211', title: 'Levitation Magnet (FL)', material: 'Low-carbon steel + copper', qty: 4, anchor: [MG.bogieFX, 2350, 1250], rail: 'bottom', elbowOffset: [26, 58] },
  { bomNumber: 19, partId: 'guid-magnet-fl', code: 'MV-221', title: 'Guidance Magnet (FL)', material: 'Low-carbon steel + copper', qty: 4, anchor: [MG.bogieFX, 2650, 1700], rail: 'top', elbowOffset: [30, -48] },
  { bomNumber: 23, partId: 'gap-sensors', code: 'MV-231', title: 'Gap Sensor Array', material: 'Eddy-current probes', qty: 8, anchor: [MG.bogieFX + 700, 2150, 0], rail: 'bottom', elbowOffset: [-14, 54] },
  { bomNumber: 24, partId: 'stator-pack-left', code: 'MV-401', title: 'Long-Stator Pack (left)', material: 'Laminated silicon steel', qty: 2, anchor: [12000, 2500, 1350], rail: 'top', elbowOffset: [-18, -50] },
  { bomNumber: 26, partId: 'guidance-rail-left', code: 'MV-411', title: 'Guidance Rail (left)', material: 'Ground steel', qty: 2, anchor: [6000, 3050, 1500], rail: 'top', elbowOffset: [-28, -44] },
  { bomNumber: 28, partId: 'brake-rail', code: 'MV-501', title: 'Eddy-Current Brake Rail', material: 'Armco iron', qty: 1, anchor: [18000, 1950, 1350], rail: 'bottom', elbowOffset: [18, 56] },
  { bomNumber: 29, partId: 'brake-magnets', code: 'MV-502', title: 'Brake Magnet Module', material: 'Steel + copper, skids', qty: 4, anchor: [MG.bogieRX, 2150, -1300], rail: 'bottom', elbowOffset: [-24, 58] },
  { bomNumber: 30, partId: 'beam-shell', code: 'MV-601', title: 'Guideway Box Beam', material: 'Prestressed concrete', qty: 1, anchor: [-3000, MG.beamTopY - 200, 0], rail: 'top', elbowOffset: [-34, -46] },
  { bomNumber: 31, partId: 'pier-segment', code: 'MV-602', title: 'Pier & Bearing Plinth', material: 'Reinforced concrete', qty: 1, anchor: [11500, 400, 0], rail: 'bottom', elbowOffset: [20, 60] },
];

const smooth = (t: number) => {
  const x = Math.min(1, Math.max(0, t));
  return x * x * (3 - 2 * x);
};

export interface LiveCallout extends BomCalloutSpec {
  anchor3D: Vec3;
}

/** Live attachment points: each anchor rides its part's explode window. */
export function resolveLiveCallouts(
  t: number,
  explodes: Record<string, { explode: Vec3; stage: [number, number] }>,
): LiveCallout[] {
  return MAGLEV_BOM_CALLOUTS.map((item) => {
    const e = explodes[item.partId];
    let w = 0;
    if (e && e.stage[1] > e.stage[0]) w = smooth((t - e.stage[0]) / (e.stage[1] - e.stage[0]));
    const [ex, ey, ez] = e ? e.explode : [0, 0, 0];
    return { ...item, anchor3D: [item.anchor[0] + ex * w, item.anchor[1] + ey * w, item.anchor[2] + ez * w] };
  });
}
