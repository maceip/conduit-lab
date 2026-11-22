import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, level, poly } from '../kit';
import { ProfileShell, Stripe, WindowBand } from './kit';
import { ANNOTATIONS, MG } from './data';

const F = MG.floorY;
const R = MG.roofY;

/** Sub-assembly A: carbody shell, glazing, doors and livery. */

const PARTS: PartDef[] = [
  { id: 'nose-upper', index: 1, name: 'Nose Shell (upper)', en: 'Nose Shell (Upper)', role: 'Aero', material: 'GFRP sandwich', description: 'Upper half of the streamlined nose, bonded to the lower shell along the centre-line seam.', explode: [900, 700, 0], stage: [0, 0.3] },
  { id: 'nose-lower', index: 2, name: 'Nose Shell (lower)', en: 'Nose Shell (Lower)', role: 'Aero · crush frame', material: 'GFRP sandwich', description: 'Lower nose shell over an aluminium crush frame that absorbs 1.5 MJ in a coupling impact.', explode: [900, -700, 0], stage: [0, 0.3] },
  { id: 'windshield-panel', index: 3, name: 'Windshield Panel', en: 'Windshield Panel', role: 'Vision', material: 'Laminated glass', description: 'Twin-pane dark glazing, bird-strike rated to 430 km/h, de-iced by a 40 W/m² film.', explode: [1500, 400, 0], stage: [0.05, 0.35] },
  { id: 'window-band', index: 4, name: 'Window Band', en: 'Window Band', role: 'Glazing', material: 'Double glazing', description: 'Ten glazed bays with 60 mm mullions along each flank; 0.6 g emergency egress via the break-out panes.', explode: [0, 500, 1400], stage: [0.1, 0.4] },
  { id: 'livery-blue', index: 5, name: 'Blue Cheatline', en: 'Blue Cheatline', role: 'Livery', material: 'Film appliqué', description: 'Raised blue stripe along the window sill line — the SMT livery band (no lettering modelled).', explode: [0, 120, 1600], stage: [0.12, 0.42] },
  { id: 'livery-orange', index: 6, name: 'Orange Cheatline', en: 'Orange Cheatline', role: 'Livery', material: 'Film appliqué', description: 'Thin orange stripe under the blue band; both stripes are appliqué film, not paint.', explode: [0, -60, 1600], stage: [0.14, 0.44] },
  { id: 'door-leaf', index: 7, name: 'Plug Door Leaf', en: 'Plug Door Leaf', role: 'Access', material: 'Aluminium honeycomb', description: '1,300 × 2,050 mm plug leaf with a break-out window; lifts 30 mm then slides into the shell pocket.', explode: [0, 0, 1900], stage: [0.16, 0.46] },
  { id: 'roof-panel', index: 8, name: 'Roof Panel', en: 'Roof Panel', role: 'Shell', material: 'Aluminium sheet', description: 'Curved roof panel with the HVAC aperture and drain gutters along both edges.', explode: [0, 1200, 0], stage: [0.18, 0.48] },
  { id: 'floor-pan', index: 9, name: 'Floor Pan & Torsion Ring', en: 'Floor Pan & Torsion Ring', role: 'Primary structure', material: 'Aluminium 6082', description: 'Extruded floor pan with the torsion ring taking 0.5 g lateral loads into the bogie mounts.', explode: [0, -1100, 0], stage: [0.2, 0.5] },
];

const STEPS: StepDef[] = [
  { title: 'Carbody', en: 'Carbody', body: 'A 27 m aerodynamic shell: rounded roof, straight flanks with a ten-bay window band, plug doors and the blue/orange cheatlines. The floor pan is the torsion ring the bogies hang from.', state: { explode: 0, section: true, running: false, select: 'window-band', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Nose halves and windshield forward, glazing and livery strips outward, doors to the sides, roof up and floor down.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [13500, F + 1900, 0],
  offset: [26000, 12000, 30000],
  orthoDistance: 95000,
  exploded: { target: [13500, F + 1900, 0], scale: 1.5 },
};

export function CarbodyGroup() {
  return (
    <group>
      <Part id="nose-upper">
        <ProfileShell k="a-noseu" shape={() => poly([[F + 900, -900], [F + 900, 900], [F + 1600, 1400], [F + 2600, 1200], [F + 3100, 400], [F + 3100, -400], [F + 2600, -1200], [F + 1600, -1400]])()} x0={24000} x1={26900} />
        <Callout id="nose-upper" p={[25600, F + 2200, 700]} />
      </Part>
      <Part id="nose-lower">
        <ProfileShell k="a-nosel" shape={() => poly([[F - 100, -1200], [F + 900, -900], [F + 900, 900], [F - 100, 1200]])()} x0={24000} x1={26900} />
        <Callout id="nose-lower" p={[25600, F + 200, -700]} />
      </Part>
      <Part id="windshield-panel">
        <Box c={[25350, F + 2450, 0]} s={[1500, 900, 1750]} r={[0, 0, -0.32]} />
        <Callout id="windshield-panel" p={[25350, F + 2950, 700]} />
      </Part>
      <Part id="window-band">
        <WindowBand x0={4200} x1={24200} y0={F + 1500} y1={F + 2350} z={1812} side={1} panes={10} />
        <WindowBand x0={4200} x1={24200} y0={F + 1500} y1={F + 2350} z={-1812} side={-1} panes={10} />
        <Callout id="window-band" p={[12000, F + 2000, 1850]} />
      </Part>
      <Part id="livery-blue">
        <Stripe x0={3000} x1={25500} y={F + 1350} z={1846} h={110} />
        <Stripe x0={3000} x1={25500} y={F + 1350} z={-1846} h={110} />
        <Callout id="livery-blue" p={[8000, F + 1350, 1880]} />
      </Part>
      <Part id="livery-orange">
        <Stripe x0={3000} x1={25500} y={F + 1180} z={1846} h={70} />
        <Stripe x0={3000} x1={25500} y={F + 1180} z={-1846} h={70} />
        <Callout id="livery-orange" p={[8000, F + 1180, -1880]} />
      </Part>
      <Part id="door-leaf">
        <Box c={[MG.doorFX, F + 1150, 1808]} s={[1300, 2050, 130]} />
        <Box c={[MG.doorFX, F + 1700, 1878]} s={[800, 860, 40]} />
        <Callout id="door-leaf" p={[MG.doorFX, F + 1150, 1900]} />
      </Part>
      <Part id="roof-panel">
        <Box c={[14250, R - 150, 0]} s={[22500, 300, 3300]} />
        <Callout id="roof-panel" p={[14250, R + 250, 600]} />
      </Part>
      <Part id="floor-pan">
        <Box c={[13500, F - 120, 0]} s={[22000, 240, 3400]} />
        <Box c={[13500, F - 320, 0]} s={[22000, 180, 2600]} />
        <Callout id="floor-pan" p={[13500, F - 420, 900]} />
      </Part>
    </group>
  );
}

export const carbody: MachineDef = level({
  id: 'maglev/carbody',
  parent: 'maglev',
  unit: 10 / 30000,
  bounds: [[23800, F - 600, -2200], [27200, R + 400, 2200]],
  name: 'Carbody Shell & Livery',
  en: 'Carbody Shell & Livery',
  subtitle: 'Sub-assembly A · aerodynamic shell · plug doors',
  summary: '9 parts · GFRP nose, aluminium torsion shell, ten-bay glazing, appliqué livery',
  drawingNo: 'GW-MV-A',
  scale: '1 : 60',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'nose-upper': ['windshield-panel', 'nose-upper'], 'window-band': ['door-leaf', 'window-band'] },
  guides: [{ stage: 'nose-upper', origin: [26200, F + 2600, 0] }, { stage: 'roof-panel', origin: [14000, R + 300, 0] }],
  centreLines: [[[23800, F + 1600, 0], [27200, F + 1600, 0], 1850]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: CarbodyGroup,
});
