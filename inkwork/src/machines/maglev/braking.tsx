import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, Cyl, level } from '../kit';
import { MagnetArray } from './kit';
import { ANNOTATIONS, MG } from './data';

/** Sub-assembly F: eddy-current track brake and parking skids. */

const PARTS: PartDef[] = [
  { id: 'eddy-rail', index: 1, name: 'Eddy-Current Reaction Rail', en: 'Eddy-Current Reaction Rail', role: 'Track brake', material: 'Armco iron', description: 'Reaction rail low on each beam web; brake magnets induce eddy currents in it for a wear-free stop.', explode: [0, -600, 1100], stage: [0, 0.32] },
  { id: 'brake-magnet', index: 2, name: 'Brake Magnet Core', en: 'Brake Magnet Core', role: 'Emergency brake', material: 'Low-carbon steel + copper', description: 'Four-pole DC magnet, 120 kN of braking force per module at 430 km/h, falling with speed as the eddies weaken.', explode: [0, -600, -1100], stage: [0.06, 0.36] },
  { id: 'friction-skid', index: 3, name: 'Friction Skid', en: 'Friction Skid', role: 'Parking · final stop', material: 'Sintered friction', description: 'Spring-released skid bearing on the rail for the final metres and for holding the car parked on a grade.', explode: [0, -1000, 0], stage: [0.12, 0.42] },
  { id: 'actuator', index: 4, name: 'Brake Actuator', en: 'Brake Actuator', role: 'Apply & release', material: 'Spring-applied cylinder', description: 'Spring-applied, electrically released actuator — a power loss applies the brakes, it never removes them.', explode: [600, -800, 0], stage: [0.18, 0.48] },
];

const STEPS: StepDef[] = [
  { title: 'Braking', en: 'Braking', body: 'Stopping 40 tonnes at 430 km/h takes the eddy-current track brake first — wear-free, force falling with speed — and the spring-applied friction skids for the last metres and for parking.', state: { explode: 0, section: true, running: false, select: 'brake-magnet', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Reaction rail outboard, brake magnets down, skids and actuators last.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [MG.bogieFX, 2100, 0],
  offset: [7000, 3400, 8000],
  orthoDistance: 24000,
  exploded: { target: [MG.bogieFX, 2100, 0], scale: 1.6 },
};

export function BrakingGroup() {
  return (
    <group>
      <Part id="eddy-rail">
        <Box c={[12000, 1950, 1430]} s={[22000, 220, 120]} />
        <Box c={[12000, 1950, -1430]} s={[22000, 220, 120]} />
        <Callout id="eddy-rail" p={[12000, 1850, 1550]} />
      </Part>
      <Part id="brake-magnet">
        {[MG.bogieFX, MG.bogieRX].map((x) => (
          <group key={x}>
            <group position={[x, 1980, 1620]}><MagnetArray x0={-560} x1={560} poles={4} w={240} h={240} depth={160} side={1} /></group>
            <group position={[x, 1980, -1620]}><MagnetArray x0={-560} x1={560} poles={4} w={240} h={240} depth={160} side={-1} /></group>
          </group>
        ))}
        <Callout id="brake-magnet" p={[MG.bogieFX, 1900, 1750]} />
      </Part>
      <Part id="friction-skid">
        {[MG.bogieFX, MG.bogieRX].map((x) => (
          <Box key={x} c={[x, 1720, 1430]} s={[900, 120, 300]} />
        ))}
        <Callout id="friction-skid" p={[MG.bogieRX, 1650, 1500]} />
      </Part>
      <Part id="actuator">
        {[MG.bogieFX, MG.bogieRX].map((x) => (
          <Cyl key={x} c={[x, 1750, 1700]} r={180} len={500} axis="y" seg={16} />
        ))}
        <Callout id="actuator" p={[MG.bogieRX, 1800, -1750]} />
      </Part>
    </group>
  );
}

export const braking: MachineDef = level({
  id: 'maglev/braking',
  parent: 'maglev',
  unit: 10 / 9000,
  bounds: [[MG.bogieFX - 1800, 1500, -2000], [MG.bogieFX + 1800, 2400, 2000]],
  name: 'Braking System',
  en: 'Braking System',
  subtitle: 'Sub-assembly F · eddy-current track brake · skids',
  summary: '4 parts · wear-free eddy brake plus spring-applied friction skids',
  drawingNo: 'GW-MV-F',
  scale: '1 : 15',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'brake-magnet': ['friction-skid', 'actuator', 'brake-magnet'] },
  guides: [{ stage: 'brake-magnet', origin: [MG.bogieFX, 1900, 1800] }],
  centreLines: [[[MG.bogieFX - 1800, 2000, 0], [MG.bogieFX + 1800, 2000, 0], 1450]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: BrakingGroup,
});
