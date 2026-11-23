import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Tagged pointer lattice.
 *
 * Source: `v8-iso/pages/fig-02-pointer-tagging.html`. That plate draws an open
 * A-frame conveyor trestle with twin tubular stringers, a run of crowned
 * steel rollers, a parabolic tubular bit-0 laser scanner arch with its
 * overhead scan pod, the carrier payload in the laser gate (a forged Smi gear
 * casting on the carrier, or a flat RFID transponder wafer when the pointer
 * is tagged into the heap), and the off-bridge rotating heap-object carousel
 * with its six field pods.
 *
 * The explode axis is the travel direction of the conveyor, so the machine
 * reads as a line of machinery taken apart along its own axis.
 */
export const POINTER_TAGGING_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [1, 0, 0],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'deck',
      label: 'Conveyor deck',
      balloon: 1,
      geometry: { kind: 'box', at: [-152, -78, 0], size: [304, 156, 14] },
    },
    {
      id: 'roller',
      label: 'Crowned roller',
      balloon: 2,
      explode: [32, 0, 0],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-46, -60, 34], to: [-46, 60, 34], r0: 16, r1: 16 },
    },
    {
      id: 'arch',
      label: 'Scanner arch',
      balloon: 3,
      explode: [64, 0, 0],
      geometry: {
        kind: 'tube',
        points: [
          [-6, -78, 40],
          [-6, -78, 96],
          [-6, -56, 142],
          [-6, 0, 166],
          [-6, 56, 142],
          [-6, 78, 96],
          [-6, 78, 40],
        ],
        radius: 8,
      },
    },
    {
      id: 'pod',
      label: 'Scan pod',
      balloon: 4,
      explode: [96, 0, 0],
      geometry: { kind: 'cyl', from: [-6, 0, 132], to: [-6, 0, 108], r0: 15, r1: 11 },
    },
    {
      id: 'carrier',
      label: 'Carrier tray',
      balloon: 5,
      explode: [128, 0, 0],
      geometry: { kind: 'box', at: [-54, -38, 46], size: [108, 76, 10] },
    },
    {
      id: 'wafer',
      label: 'RFID tag wafer',
      balloon: 6,
      explode: [160, 0, 0],
      geometry: { kind: 'cyl', from: [0, 0, 56], to: [0, 0, 63], r0: 29, r1: 29 },
    },
    {
      id: 'carousel',
      label: 'Heap carousel',
      balloon: 7,
      explode: [192, 0, 0],
      geometry: { kind: 'cyl', from: [96, 104, 0], to: [96, 104, 30], r0: 36, r1: 31 },
    },
  ],
};

export function PointerTaggingIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(POINTER_TAGGING_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
