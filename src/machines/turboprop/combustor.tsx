import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Hoop, level, Rod } from '../kit';
import { BoltCircle, FuelManifold, Shell } from './kit';
import { ANNOTATIONS, TP } from './data';

const AY = TP.AY;

/**
 * Sub-assembly E: annular reverse-flow combustor — outer pressure shell, flame
 * liner (3 dilution rows), 14 nozzle bosses, the fuel manifold and 2 igniter plugs.
 */

const PARTS: PartDef[] = [
  {
    id: 'outer-case', index: 1, name: 'Outer Pressure Shell', en: 'Outer Pressure Vessel Shell', role: 'Pressure vessel',
    material: 'GH4169', description: '580 mm bore, 18 mm wall, holding 4×10⁵ Pa; twelve bolts on each flange and 14 nozzle holes along the split line.',
    explode: [0, 0, -420], stage: [0, 0.32],
  },
  {
    id: 'flame-liner', index: 2, name: 'Flame Liner', en: 'Combustion Flame Liner', role: 'Burn · mix',
    material: 'GH3044', description: 'Reverse-flow annular liner (460 mm outer, 3 mm wall) with three dilution rows totalling 96 holes (32 per row) and film cooling along the wall.',
    explode: [0, 0, 420], stage: [0.12, 0.44],
  },
  {
    id: 'nozzle-bosses', index: 3, name: 'Nozzle Bosses ×14', en: 'Fuel Nozzle Bosses ×14', role: 'Atomisation',
    material: '1Cr18Ni9Ti stainless', description: 'Fourteen bosses evenly spaced (25.7° apart), 80° spray cone, 0.12 L/s per nozzle.',
    explode: [0, 380, 0], stage: [0.3, 0.6],
  },
  {
    id: 'manifold-tubing', index: 4, name: 'Manifold Tubing', en: 'Fuel Manifold Tubing', role: 'Equalised feed',
    material: '1Cr18Ni9Ti stainless', description: 'Annular manifold 572 mm outer with Ø34 tubing; equal-length branches keep the circumferential fuel distribution even.',
    explode: [0, 520, 0], stage: [0.34, 0.64],
  },
  {
    id: 'igniter-plugs', index: 5, name: 'Igniter Plugs ×2', en: 'Igniter Plugs ×2', role: 'Ignition',
    material: 'Nickel alloy', description: 'Two semiconductor igniters (2 J spark energy) in the liner recirculation zone; lights on the ground and can relight in flight.',
    explode: [-120, 320, 0], stage: [0.38, 0.68],
  },
];

const STEPS: StepDef[] = [
  {
    title: 'Combustor', en: 'Combustor',
    body: 'Diffused air splits into two streams around the liner: primary holes and fuel nozzles hold a stable recirculating flame, and the dilution holes cool the gas to ≈ 1,100 °C before the turbine.',
    state: { explode: 0, section: true, running: false, select: 'flame-liner', focus: null },
  },
  {
    title: 'Exploded', en: 'Exploded',
    body: 'Liner and pressure shell part along their split; the 14 nozzle bosses leave radially with the manifold, and the igniter plugs come last.',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

const CAMERA: CameraDef = {
  target: [-540, AY, 0],
  offset: [1050, 500, 1300],
  orthoDistance: 3300,
  exploded: { target: [-540, AY, 0], scale: 1.7 },
};

export function CombustorGroup() {
  return (
    <group>
      <Part id="outer-case">
        <Shell
          k="tp-e-case"
          t={18}
          profile={[
            [252, 240], [292, 196], [292, 60], [292, -510], [308, -520], [308, -556], [288, -566], [276, -760],
          ]}
        />
        <BoltCircle x={225} r={318} count={12} d={18} len={44} />
        <Callout id="outer-case" p={[-320, AY + 320, 130]} />
      </Part>
      <Part id="flame-liner">
        <Shell k="tp-e-liner" t={10} profile={[[152, TP.linerX1], [232, TP.linerX1 - 24], [232, TP.linerX0 + 40], [168, TP.linerX0]]} />
        {[0, 1, 2].map((row) => {
          const x = TP.linerX1 - 90 - row * 105;
          return (
            <group key={row}>
              <Hoop k={`tp-e-hoop-${row}`} c={[x, AY, 0]} R={234} r={10} axis="x" seg={40} />
              {Array.from({ length: 12 }, (_, i) => {
                const a = (i / 12) * Math.PI * 2 + row * 0.13;
                return (
                  <Rod key={i} a={[x, AY + Math.cos(a) * 150, Math.sin(a) * 150]} b={[x, AY + Math.cos(a) * 238, Math.sin(a) * 238]} r={7} seg={8} />
                );
              })}
            </group>
          );
        })}
        <Callout id="flame-liner" p={[-500, AY + 280, 130]} />
      </Part>
      <Part id="nozzle-bosses">
        <FuelManifold x={-430} r={286} tubeR={17} />
        <Callout id="nozzle-bosses" p={[-430, AY + 330, -110]} />
      </Part>
      <Part id="manifold-tubing">
        <Hoop k="tp-e-manif" c={[-450, AY, 0]} R={286} r={17} axis="x" seg={48} />
        <Callout id="manifold-tubing" p={[-450, AY - 260, 130]} />
      </Part>
      <Part id="igniter-plugs">
        {[1, -1].map((s) => (
          <Rod key={s} a={[-560, AY + s * 120, 150]} b={[-560, AY + s * 246, 150]} r={14} seg={10} />
        ))}
        <Callout id="igniter-plugs" p={[-560, AY + 280, 160]} />
      </Part>
    </group>
  );
}

export const combustor: MachineDef = level({
  id: 'turboprop/combustor',
  parent: 'turboprop',
  unit: 10 / 1100,
  bounds: [[-800, AY - 340, -340], [280, AY + 360, 340]],
  name: 'Annular Reverse-Flow Combustor',
  en: 'Annular Reverse-Flow Combustor',
  subtitle: 'Sub-assembly E · 14 nozzles · reverse-flow liner',
  summary: '5 parts · three rows, 96 dilution holes, ≈ 1,100 °C before the turbine',
  drawingNo: 'GW-TP-E',
  scale: '1 : 3',
  parts: PARTS,
  annotations: ANNOTATIONS,
  boltSets: {},
  neighbours: {
    'flame-liner': ['nozzle-bosses', 'manifold-tubing', 'igniter-plugs', 'flame-liner'],
    'outer-case': ['flame-liner', 'outer-case'],
  },
  guides: [
    { stage: 'flame-liner', origin: [-520, AY + 280, 0] },
    { stage: 'manifold-tubing', origin: [-450, AY + 320, 0] },
  ],
  centreLines: [[[-800, AY, 0], [280, AY, 0], 290]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: CombustorGroup,
});
