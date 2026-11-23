import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Old-generation heap.
 *
 * Source: `v8-iso/pages/fig-07-old-space.html`. That plate draws an open
 * lattice tubular high-bay storage rack — four columns, three tiers, X
 * bracing — holding flanged cylindrical memory capsule drums, with twin floor
 * and overhead crane guide rails, a twin-mast stacker crane with its bogie
 * carriage and laser marking turret, and the compaction of dead drums.
 *
 * The memory capsule is a surface of revolution about the origin, exactly as
 * the drum is in the source figure.
 */
export const OLD_SPACE_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'floor-rail',
      label: 'Floor rail',
      balloon: 1,
      geometry: { kind: 'box', at: [-170, 76, 0], size: [340, 16, 12] },
    },
    {
      id: 'column',
      label: 'Rack column',
      balloon: 2,
      explode: [0, 0, 48],
      geometry: { kind: 'cyl', from: [-120, -20, 0], to: [-120, -20, 176], r0: 8, r1: 8 },
    },
    {
      id: 'shelf-beam',
      label: 'Shelf beam',
      balloon: 3,
      explode: [0, 0, 96],
      geometry: { kind: 'box', at: [-170, -26, 0], size: [340, 14, 10] },
    },
    {
      id: 'capsule',
      label: 'Memory capsule',
      balloon: 4,
      explode: [0, 0, 144],
      sectioned: true,
      geometry: {
        kind: 'revolve',
        profile: [
          [0, 22],
          [8, 24],
          [44, 24],
          [52, 17],
          [57, 1],
        ],
        segments: 20,
      },
    },
    {
      id: 'crane',
      label: 'Stacker crane',
      balloon: 5,
      explode: [0, 0, 192],
      geometry: { kind: 'box', at: [-40, 36, 0], size: [78, 38, 14] },
    },
    {
      id: 'mast',
      label: 'Crane mast',
      balloon: 6,
      explode: [0, 0, 240],
      sectioned: true,
      geometry: { kind: 'cyl', from: [0, 56, 0], to: [0, 56, 168], r0: 7, r1: 4 },
    },
    {
      id: 'barrier',
      label: 'Remembered-set barrier',
      balloon: 7,
      explode: [0, 0, 288],
      geometry: { kind: 'box', at: [-130, -58, 0], size: [260, 10, 38] },
    },
  ],
};

export function OldSpaceIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(OLD_SPACE_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
