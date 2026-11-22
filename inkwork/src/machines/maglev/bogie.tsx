import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, Cyl, level } from '../kit';
import { MagnetArray, SensorHead, WrapArm } from './kit';
import { ANNOTATIONS, MG } from './data';

const F = MG.floorY;

/** Sub-assembly B: wrap-around levitation bogie with magnet cores and sensors. */

const PARTS: PartDef[] = [
  { id: 'frame-crossbeam', index: 1, name: 'Bogie Crossbeam', en: 'Bogie Crossbeam', role: 'Frame', material: 'Welded S355 steel', description: '1,300 mm crossbeam tying the two wrap arms to the car floor mounts; takes the full 300 kN lift per bogie.', explode: [0, -500, 0], stage: [0, 0.3] },
  { id: 'frame-arm-left', index: 2, name: 'Wrap Arm (left)', en: 'Wrap Arm (Left)', role: 'Frame', material: 'Welded S355 steel', description: 'Box-section arm descending beside the beam to y ≈ 2,250, carrying the magnet shelves.', explode: [0, -400, 1200], stage: [0.05, 0.35] },
  { id: 'frame-arm-right', index: 3, name: 'Wrap Arm (right)', en: 'Wrap Arm (Right)', role: 'Frame', material: 'Welded S355 steel', description: 'Right arm; the pair wraps the beam so lift and guidance forces close inside the steel structure.', explode: [0, -400, -1200], stage: [0.05, 0.35] },
  { id: 'lev-core', index: 4, name: 'Levitation Magnet Core', en: 'Levitation Magnet Core', role: 'Lift', material: 'Low-carbon steel', description: 'Laminated C-core, 12 poles, 300 × 340 mm face — the flux path from coil to pole shoe to stator pack.', explode: [0, -700, 900], stage: [0.15, 0.45] },
  { id: 'lev-coil', index: 5, name: 'Levitation Coil', en: 'Levitation Coil', role: 'Lift · chopper-fed', material: 'Copper on glass-fibre', description: '1,200-turn coil per pole pair, 30 A nominal, chopped at 2 kHz to hold the 10 mm gap.', explode: [0, -700, -900], stage: [0.18, 0.48] },
  { id: 'lev-pole-shoe', index: 6, name: 'Pole Shoes', en: 'Pole Shoes', role: 'Flux face', material: 'Armco iron', description: 'Ground pole shoes (flatness 0.05 mm) that present a uniform face to the pack — the air gap lives here.', explode: [0, -1100, 0], stage: [0.2, 0.5] },
  { id: 'sensor-head', index: 7, name: 'Gap Sensor Heads', en: 'Gap Sensor Heads', role: 'Measure 10 mm', material: 'Eddy-current probes', description: 'Two probes per magnet reading gap to ±0.1 mm at 2 kHz — the feedback that makes levitation stable.', explode: [600, -1300, 0], stage: [0.22, 0.52] },
];

const STEPS: StepDef[] = [
  { title: 'Bogie', en: 'Bogie', body: 'The wrap-around frame: two arms descending beside the beam carry C-core levitation magnets whose pole shoes face the stator packs across a 10 mm gap, with gap probes right behind them.', state: { explode: 0, section: true, running: false, select: 'lev-core', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Crossbeam up, arms out sideways, cores and coils apart, pole shoes and sensor heads last.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [MG.bogieFX, 2700, 0],
  offset: [6500, 3200, 7500],
  orthoDistance: 22000,
  exploded: { target: [MG.bogieFX, 2700, 0], scale: 1.6 },
};

export function BogieGroup() {
  return (
    <group>
      <Part id="frame-crossbeam">
        <Box c={[MG.bogieFX, F - 200, 0]} s={[1300, 320, 3200]} />
        <Callout id="frame-crossbeam" p={[MG.bogieFX, F - 300, 900]} />
      </Part>
      <Part id="frame-arm-left">
        <WrapArm x={MG.bogieFX} side={1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <Callout id="frame-arm-left" p={[MG.bogieFX, 2800, 1750]} />
      </Part>
      <Part id="frame-arm-right">
        <WrapArm x={MG.bogieFX} side={-1} topY={F - 100} botY={2250} z0={1250} z1={2050} />
        <Callout id="frame-arm-right" p={[MG.bogieFX, 2800, -1750]} />
      </Part>
      <Part id="lev-core">
        <group position={[MG.bogieFX, 2330, 1620]}><MagnetArray x0={-850} x1={850} poles={12} side={1} /></group>
        <Callout id="lev-core" p={[MG.bogieFX, 2250, 1700]} />
      </Part>
      <Part id="lev-coil">
        {[-1, 1].map((s) => (
          <Cyl key={s} c={[MG.bogieFX, 2330, s * 1450]} r={240} len={1600} axis="x" seg={18} />
        ))}
        <Callout id="lev-coil" p={[MG.bogieFX, 2330, -1500]} />
      </Part>
      <Part id="lev-pole-shoe">
        {[-1, 1].map((s) => (
          <Box key={s} c={[MG.bogieFX, 2250, s * 1800]} s={[1600, 130, 180]} />
        ))}
        <Callout id="lev-pole-shoe" p={[MG.bogieFX, 2150, 1850]} />
      </Part>
      <Part id="sensor-head">
        <SensorHead x={MG.bogieFX - 700} y={2260} z={1450} />
        <SensorHead x={MG.bogieFX + 700} y={2260} z={1450} />
        <Callout id="sensor-head" p={[MG.bogieFX + 700, 2100, 1500]} />
      </Part>
    </group>
  );
}

export const bogie: MachineDef = level({
  id: 'maglev/bogie',
  parent: 'maglev',
  unit: 10 / 8000,
  bounds: [[MG.bogieFX - 1600, 1800, -2400], [MG.bogieFX + 1600, F + 400, 2400]],
  name: 'Levitation Bogie',
  en: 'Levitation Bogie',
  subtitle: 'Sub-assembly B · wrap-around frame · 10 mm gap',
  summary: '7 parts · C-core lift magnets, ground pole shoes, eddy-current gap probes',
  drawingNo: 'GW-MV-B',
  scale: '1 : 10',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'lev-core': ['lev-coil', 'lev-pole-shoe', 'lev-core'], 'frame-crossbeam': ['frame-arm-left', 'frame-arm-right', 'frame-crossbeam'] },
  guides: [{ stage: 'frame-arm-left', origin: [MG.bogieFX, 2600, 1900] }, { stage: 'lev-core', origin: [MG.bogieFX, 2200, 1700] }],
  centreLines: [[[MG.bogieFX - 1800, 2400, 0], [MG.bogieFX + 1800, 2400, 0], 1600]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: BogieGroup,
});
