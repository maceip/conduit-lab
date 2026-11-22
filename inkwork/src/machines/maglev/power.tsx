import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, Cyl, level } from '../kit';
import { ANNOTATIONS, MG } from './data';

const F = MG.floorY;

/** Sub-assembly E: onboard power, conversion and climate equipment. */

const PARTS: PartDef[] = [
  { id: 'battery-module', index: 1, name: 'Battery Module', en: 'Battery Module', role: 'Emergency power', material: 'NiCd 110 V', description: '200 Ah NiCd set holding levitation and gap control alive for a controlled touchdown if ground power drops.', explode: [0, -800, 0], stage: [0, 0.32] },
  { id: 'converter', index: 2, name: 'Levitation Chopper', en: 'Levitation Chopper', role: 'Magnet supply', material: 'IGBT stack', description: '2 kHz chopper feeding the lift magnets; current loop at 20 kHz inside the 20 Hz gap loop.', explode: [600, -600, -900], stage: [0.06, 0.36] },
  { id: 'hvac-compressor', index: 3, name: 'HVAC Compressor', en: 'HVAC Compressor', role: 'Climate', material: 'Scroll compressor', description: 'Scroll compressor (25 kW) in the roof pack, fed from the converter’s auxiliary output.', explode: [0, 900, 0], stage: [0.12, 0.42] },
  { id: 'linear-pickup', index: 4, name: 'Inductive Power Pickup', en: 'Inductive Power Pickup', role: 'Ground power', material: 'Ferrite + copper', description: 'Inductive pickup along the beam feeding the onboard bus — no pantograph, no contact, at 430 km/h.', explode: [-600, -400, 900], stage: [0.18, 0.48] },
];

const STEPS: StepDef[] = [
  { title: 'Onboard Power', en: 'Onboard Power', body: 'Power comes off the beam inductively, is chopped for the magnets, conditioned by the converter cabinets, and backed by the battery set for the emergency touchdown.', state: { explode: 0, section: true, running: false, select: 'battery-module', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Battery down, chopper to the side, compressor up and the pickup outboard.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [12500, 3000, 0],
  offset: [11000, 5200, 13000],
  orthoDistance: 40000,
  exploded: { target: [12500, 3000, 0], scale: 1.6 },
};

export function PowerGroup() {
  return (
    <group>
      <Part id="battery-module">
        <Box c={[9000, 2950, 0]} s={[3200, 720, 2400]} />
        {[0, 1, 2, 3].map((i) => (
          <Box key={i} c={[7900 + i * 730, 2950, 0]} s={[600, 760, 2440]} />
        ))}
        <Callout id="battery-module" p={[9000, 2850, 1100]} />
      </Part>
      <Part id="converter">
        <Box c={[16000, 2820, -900]} s={[2400, 950, 1250]} />
        {[0, 1, 2].map((i) => (
          <Cyl key={i} c={[15200 + i * 800, 2820, -900]} r={220} len={1300} axis="y" seg={14} />
        ))}
        <Callout id="converter" p={[16000, 2750, -1450]} />
      </Part>
      <Part id="hvac-compressor">
        <Box c={[13000, 7730, 0]} s={[3600, 420, 2600]} />
        <Cyl c={[13000, 8060, 0]} r={420} len={300} axis="y" seg={20} />
        <Callout id="hvac-compressor" p={[13000, 8150, 700]} />
      </Part>
      <Part id="linear-pickup">
        <Box c={[11500, 2650, 1180]} s={[3200, 340, 160]} />
        {[0, 1, 2, 3, 4].map((i) => (
          <Box key={i} c={[10300 + i * 600, 2650, 1280]} s={[300, 300, 120]} />
        ))}
        <Callout id="linear-pickup" p={[11500, 2650, 1400]} />
      </Part>
    </group>
  );
}

export const power: MachineDef = level({
  id: 'maglev/power',
  parent: 'maglev',
  unit: 10 / 12000,
  bounds: [[7000, 2400, -1600], [18000, F + 4700, 1600]],
  name: 'Onboard Power & Equipment',
  en: 'Onboard Power & Equipment',
  subtitle: 'Sub-assembly E · inductive pickup · chopper · battery',
  summary: '4 parts · emergency battery, levitation chopper, HVAC, inductive pickup',
  drawingNo: 'GW-MV-E',
  scale: '1 : 25',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'battery-module': ['converter', 'battery-module'] },
  guides: [{ stage: 'battery-module', origin: [9000, 2600, 900] }],
  centreLines: [[[7000, 3000, 0], [18000, 3000, 0], 1200]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: PowerGroup,
});
