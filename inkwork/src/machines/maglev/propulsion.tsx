import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, level } from '../kit';
import { StatorPack } from './kit';
import { ANNOTATIONS, MG } from './data';

/** Sub-assembly C: long-stator linear motor armature packs on the beam. */

const PARTS: PartDef[] = [
  { id: 'stator-lamination', index: 1, name: 'Stator Lamination Stack', en: 'Stator Lamination Stack', role: 'LSM armature', material: 'Silicon steel 0.5 mm', description: '0.5 mm coated laminations stacked to 240 mm and welded at the corners; eddy losses kept under 1.2 W/kg at 200 Hz.', explode: [0, 500, 1200], stage: [0, 0.32] },
  { id: 'stator-core', index: 2, name: 'Stator Core Teeth', en: 'Stator Core Teeth', role: 'Flux guide', material: 'Silicon steel', description: 'Skewed teeth on a 258 mm pole pitch; skewing one slot pitch cuts the travelling-field harmonics that would ripple the gap.', explode: [0, 500, -1200], stage: [0.05, 0.36] },
  { id: 'winding-bar', index: 3, name: 'Three-Phase Winding Bars', en: 'Three-Phase Winding Bars', role: 'Travelling field', material: 'Copper, class H', description: 'Double-layer diamond bars in 1.2 m half-packs, series-connected so the drive energises only the section ahead of the train.', explode: [0, 900, 0], stage: [0.1, 0.42] },
  { id: 'mounting-bracket', index: 4, name: 'Mounting Brackets', en: 'Mounting Brackets', role: 'Fixing', material: 'Cast steel', description: 'Brackets bolt the packs to the beam web at 2.4 m centres, setting the 10 mm nominal magnet gap to ±0.5 mm over the span.', explode: [0, -600, 0], stage: [0.15, 0.46] },
  { id: 'end-plate', index: 5, name: 'Pack End Plate', en: 'Pack End Plate', role: 'Protection', material: 'Stainless steel', description: 'End plates between 1.2 m packs shield the winding ends and carry the section-joint links.', explode: [-600, 200, 0], stage: [0.18, 0.5] },
];

const STEPS: StepDef[] = [
  { title: 'Long Stator', en: 'Long Stator', body: 'The motor lives in the track: laminated packs on both beam flanks carry a three-phase winding whose travelling field drags the car’s excitation magnets. Only the section ahead of the train is energised.', state: { explode: 0, section: true, running: false, select: 'winding-bar', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Laminations and core teeth split outward, winding bars lift free, brackets and end plates follow.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [12000, 2500, 0],
  offset: [14000, 7000, 17000],
  orthoDistance: 52000,
  exploded: { target: [12000, 2500, 0], scale: 1.6 },
};

export function PropulsionGroup() {
  return (
    <group>
      <Part id="stator-lamination">
        <group position={[0, 2400, 1250]}><StatorPack x0={8000} x1={16000} side={1} /></group>
        <Callout id="stator-lamination" p={[12000, 2650, 1500]} />
      </Part>
      <Part id="stator-core">
        {[0, 1, 2, 3, 4, 5, 6].map((i) => (
          <Box key={i} c={[8300 + i * 1100, 2400, 1520]} s={[420, 560, 120]} />
        ))}
        <Callout id="stator-core" p={[12000, 2400, 1650]} />
      </Part>
      <Part id="winding-bar">
        {[-1, 0, 1].map((row) => (
          <Box key={row} c={[12000, 2400 + row * 190, 1530]} s={[8000, 90, 90]} />
        ))}
        <Callout id="winding-bar" p={[12000, 2750, 1650]} />
      </Part>
      <Part id="mounting-bracket">
        {[0, 1, 2, 3].map((i) => (
          <Box key={i} c={[8600 + i * 2400, 2400, 1140]} s={[200, 600, 360]} />
        ))}
        <Callout id="mounting-bracket" p={[13400, 2400, 900]} />
      </Part>
      <Part id="end-plate">
        <Box c={[7900, 2400, 1400]} s={[90, 700, 420]} />
        <Box c={[16100, 2400, 1400]} s={[90, 700, 420]} />
        <Callout id="end-plate" p={[7900, 2850, 1400]} />
      </Part>
    </group>
  );
}

export const propulsion: MachineDef = level({
  id: 'maglev/propulsion',
  parent: 'maglev',
  unit: 10 / 11000,
  bounds: [[7600, 1800, 700], [16400, 3100, 1900]],
  name: 'Long-Stator Linear Motor',
  en: 'Long-Stator Linear Motor',
  subtitle: 'Sub-assembly C · 258 mm pole pitch · three-phase armature',
  summary: '5 parts · laminated packs, double-layer winding, section-jointed supply',
  drawingNo: 'GW-MV-C',
  scale: '1 : 20',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'stator-lamination': ['stator-core', 'winding-bar', 'stator-lamination'] },
  guides: [{ stage: 'winding-bar', origin: [12000, 2900, 1500] }],
  centreLines: [[[7600, 2400, 0], [16400, 2400, 0], 620]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: PropulsionGroup,
});
