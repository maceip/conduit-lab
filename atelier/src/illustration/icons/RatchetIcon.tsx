import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { gear2D, projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * The trusted-item ratchet.
 *
 * Source: `browser/ratchet.json` and the `scripts/collect_stats.py` pipeline
 * that produces it. The ratchet reports eleven crates, every one of them
 * proved with a trusted-item count of zero, and its whole meaning is that the
 * count never rises between releases.
 *
 * The mechanism is drawn as a real machine: a locked pawl engaging a toothed
 * wheel whose angle is the trusted-item count, a detent post, the wheel hub,
 * the counter drum that reads the count, and the cam post that drives the
 * pawl. No number is baked into the drawing — the counter is the component
 * that carries the live value.
 */
export const RATCHET_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'base',
      label: 'Ratchet base plate',
      balloon: 1,
      geometry: { kind: 'box', at: [-128, -96, 0], size: [256, 192, 14] },
    },
    {
      id: 'wheel',
      label: 'Trusted-item wheel',
      balloon: 2,
      explode: [0, 0, 42],
      geometry: {
        kind: 'extrude',
        poly: gear2D(12, 52, 66),
        depth: 15,
      },
    },
    {
      id: 'pawl',
      label: 'Locking pawl',
      balloon: 3,
      explode: [0, 0, 84],
      geometry: { kind: 'box', at: [46, -12, 0], size: [56, 16, 12] },
    },
    {
      id: 'detent',
      label: 'Detent post',
      balloon: 4,
      explode: [0, 0, 126],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-88, 56, 0], to: [-88, 56, 34], r0: 11, r1: 11 },
    },
    {
      id: 'hub',
      label: 'Wheel hub',
      balloon: 5,
      explode: [0, 0, 168],
      geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 22], r0: 22, r1: 19 },
    },
    {
      id: 'counter',
      label: 'Trusted-item counter',
      balloon: 6,
      explode: [0, 0, 210],
      sectioned: true,
      geometry: { kind: 'cyl', from: [96, 34, 0], to: [96, 34, 17], r0: 32, r1: 32 },
    },
    {
      id: 'post',
      label: 'Cam post',
      balloon: 7,
      explode: [0, 0, 252],
      geometry: { kind: 'cyl', from: [88, -54, 0], to: [88, -54, 38], r0: 9, r1: 9 },
    },
  ],
};

export function RatchetIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(RATCHET_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
