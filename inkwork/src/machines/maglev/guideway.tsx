import { Part } from '../../scene/Part';
import { Callout } from '../../scene/Overlay';
import type { CameraDef, MachineDef, PartDef, StepDef, Vec3 } from '../types';
import { Box, level } from '../kit';
import { ANNOTATIONS, MG } from './data';

/** Sub-assembly D: prestressed concrete box beam, rails and pier. */

const PARTS: PartDef[] = [
  { id: 'beam-top', index: 1, name: 'Beam Top Slab', en: 'Beam Top Slab', role: 'Deck', material: 'Prestressed concrete', description: 'Top slab of the box section, 220 mm thick, finished to ±2 mm over 31.5 m spans for the guidance rails.', explode: [0, 700, 0], stage: [0, 0.3] },
  { id: 'beam-web-left', index: 2, name: 'Beam Web (left)', en: 'Beam Web (Left)', role: 'Shear', material: 'Prestressed concrete', description: 'Left web carrying the stator packs and guidance rail; hollow core keeps the beam at 12.5 t/m.', explode: [0, 0, 1100], stage: [0.05, 0.35] },
  { id: 'beam-web-right', index: 3, name: 'Beam Web (right)', en: 'Beam Web (Right)', role: 'Shear', material: 'Prestressed concrete', description: 'Right web; the twin webs close into a torsion box that resists the eccentric braking loads.', explode: [0, 0, -1100], stage: [0.05, 0.35] },
  { id: 'walkway-edge', index: 4, name: 'Walkway Edge', en: 'Walkway Edge', role: 'Maintenance', material: 'Concrete + steel', description: 'Raised edge along both top flanges forming the maintenance walkway and its fall barrier.', explode: [0, 500, 1500], stage: [0.1, 0.4] },
  { id: 'rail-pad', index: 5, name: 'Rail Mounting Pads', en: 'Rail Mounting Pads', role: 'Interface', material: 'Elastomer', description: 'Elastomer pads under the guidance rails isolating rail vibration from the beam, 45 ShA hardness.', explode: [0, -300, 0], stage: [0.15, 0.45] },
  { id: 'pier-cap', index: 6, name: 'Pier Cap & Bearings', en: 'Pier Cap & Bearings', role: 'Support', material: 'Reinforced concrete + steel', description: 'Pier head with spherical bearings that let the beam expand 60 mm across the temperature range.', explode: [0, -1200, 0], stage: [0.2, 0.5] },
];

const STEPS: StepDef[] = [
  { title: 'Guideway', en: 'Guideway', body: 'A 2.8 × 2.2 m prestressed box beam on 31.5 m spans: the webs carry the long-stator packs and the ground guidance rails, the hollow core carries the dead load, and the pier bearings let it breathe.', state: { explode: 0, section: true, running: false, select: 'beam-web-left', focus: null } },
  { title: 'Exploded', en: 'Exploded', body: 'Top slab lifts, webs split ±z, walkway edges and rail pads follow, pier cap last.', state: { explode: 1, section: false, running: false, select: null, focus: null } },
];

const CAMERA: CameraDef = {
  target: [11500, 2200, 0],
  offset: [16000, 8000, 19000],
  orthoDistance: 58000,
  exploded: { target: [11500, 2200, 0], scale: 1.6 },
};

export function GuidewayGroup() {
  return (
    <group>
      <Part id="beam-top">
        <Box c={[11500, MG.beamTopY - 110, 0]} s={[MG.beamX1 - MG.beamX0, 220, MG.beamW]} />
        <Callout id="beam-top" p={[6000, MG.beamTopY + 80, 800]} />
      </Part>
      <Part id="beam-web-left">
        <Box c={[11500, 2300, 1300]} s={[MG.beamX1 - MG.beamX0, 1900, 200]} />
        <Callout id="beam-web-left" p={[6000, 2300, 1400]} />
      </Part>
      <Part id="beam-web-right">
        <Box c={[11500, 2300, -1300]} s={[MG.beamX1 - MG.beamX0, 1900, 200]} />
        <Callout id="beam-web-right" p={[6000, 2300, -1400]} />
      </Part>
      <Part id="walkway-edge">
        <Box c={[11500, MG.beamTopY + 40, MG.beamW / 2 - 140]} s={[MG.beamX1 - MG.beamX0, 80, 260]} />
        <Box c={[11500, MG.beamTopY + 40, -(MG.beamW / 2 - 140)]} s={[MG.beamX1 - MG.beamX0, 80, 260]} />
        <Callout id="walkway-edge" p={[11500, MG.beamTopY + 140, 1300]} />
      </Part>
      <Part id="rail-pad">
        {[1, -1].map((s) => (
          <Box key={s} c={[11500, 3000, s * 1520]} s={[MG.beamX1 - MG.beamX0, 70, 220]} />
        ))}
        <Callout id="rail-pad" p={[11500, 3000, -1650]} />
      </Part>
      <Part id="pier-cap">
        <Box c={[11500, 1180, 0]} s={[3200, 240, 2600]} />
        <Box c={[11500, 1310, 0]} s={[2600, 120, 2000]} />
        <Callout id="pier-cap" p={[11500, 1250, 1300]} />
      </Part>
    </group>
  );
}

export const guideway: MachineDef = level({
  id: 'maglev/guideway',
  parent: 'maglev',
  unit: 10 / 22000,
  bounds: [[MG.beamX0, 900, -2000], [MG.beamX1, MG.beamTopY + 200, 2000]],
  name: 'Guideway Beam & Pier',
  en: 'Guideway Beam & Pier',
  subtitle: 'Sub-assembly D · prestressed box beam · 31.5 m spans',
  summary: '6 parts · hollow box section, walkway edges, rail pads, bearing pier cap',
  drawingNo: 'GW-MV-D',
  scale: '1 : 40',
  parts: PARTS,
  boltSets: {},
  neighbours: { 'beam-top': ['beam-web-left', 'beam-web-right', 'beam-top'] },
  guides: [{ stage: 'beam-top', origin: [8000, MG.beamTopY + 200, 0] }],
  centreLines: [[[MG.beamX0, MG.beamTopY, 0], [MG.beamX1, MG.beamTopY, 0], MG.beamW / 2]] as Array<[Vec3, Vec3, number?]>,
  steps: STEPS,
  camera: CAMERA,
  Model: GuidewayGroup,
});
