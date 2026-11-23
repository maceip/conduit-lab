import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { projectAssembly, renderPlate, stadiumLoop, type Assembly } from '../engine';

/**
 * Scavenger nursery.
 *
 * Source: `v8-iso/pages/fig-08-new-space.html`. That plate draws an angled
 * A-frame trestle carrying the upper from-space stadium conveyor belt with
 * its tail pulley and magnetic eddy-current head drum, the nursery chip
 * allocations riding the top run, the zero-cost conical dead-chip gravity
 * drop funnel below the drum, the splitter knife that separates the dead
 * vertical fall from the repelled parabolic live-chip leap, and the tall
 * helical screw-auger promotion elevator climbing to old space.
 *
 * The belt is a real closed stadium loop, swept as a tube.
 */
export const NEW_SPACE_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [1, 0, 0],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'trestle',
      label: 'A-frame trestle',
      balloon: 1,
      geometry: { kind: 'box', at: [-152, -58, 0], size: [304, 116, 14] },
    },
    {
      id: 'belt',
      label: 'From-space belt',
      balloon: 2,
      explode: [32, 0, 0],
      geometry: {
        kind: 'tube',
        points: stadiumLoop(-40, 0, 70, 126, 28, 5),
        radius: 9,
      },
    },
    {
      id: 'drum',
      label: 'Eddy-current head drum',
      balloon: 3,
      explode: [64, 0, 0],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-4, -38, 70], to: [-4, 38, 70], r0: 25, r1: 25 },
    },
    {
      id: 'funnel',
      label: 'Gravity drop funnel',
      balloon: 4,
      explode: [96, 0, 0],
      geometry: { kind: 'cyl', from: [70, 0, 0], to: [70, 0, 52], r0: 42, r1: 17 },
    },
    {
      id: 'knife',
      label: 'Splitter knife',
      balloon: 5,
      explode: [128, 0, 0],
      geometry: { kind: 'box', at: [104, -27, 34], size: [8, 54, 38] },
    },
    {
      id: 'auger',
      label: 'Auger promotion elevator',
      balloon: 6,
      explode: [160, 0, 0],
      sectioned: true,
      geometry: { kind: 'cyl', from: [176, 52, 0], to: [176, 52, 126], r0: 28, r1: 28 },
    },
    {
      id: 'chip',
      label: 'Nursery chip',
      balloon: 7,
      explode: [192, 0, 0],
      geometry: { kind: 'cyl', from: [20, 0, 0], to: [20, 0, 14], r0: 15, r1: 12 },
    },
  ],
};

export function NewSpaceIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(NEW_SPACE_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
