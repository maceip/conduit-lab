import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * `v8::Isolate` — twin-silo process skid.
 *
 * Source: `v8-iso/pages/fig-01-isolate.html`. That plate draws an I-beam skid
 * with transverse cross-channels, a safety handrail, a tall domed heap silo
 * with support legs and a flanged manway, a smaller realm silo carrying sight
 * rings, an overhead swept manifold joining the two silos, a centrifugal
 * microtask pump with a tangential discharge stack, and the rotary locker cam
 * valve with its handwheel.
 *
 * Seven parts here: the skid, both silos, the manifold, the pump, the
 * discharge stack and the cam valve. The main silo is sectioned, so the plate
 * always carries the hatching cue.
 */
export const ISOLATE_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'skid',
      label: 'Skid base',
      balloon: 1,
      geometry: { kind: 'box', at: [-196, -92, 0], size: [392, 184, 16] },
    },
    {
      id: 'silo-main',
      label: 'Main silo',
      balloon: 2,
      explode: [0, 0, 52],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-120, -30, 0], to: [-120, -30, 104], r0: 48, r1: 43 },
    },
    {
      id: 'silo-realm',
      label: 'Realm silo',
      balloon: 3,
      explode: [0, 0, 104],
      geometry: { kind: 'cyl', from: [72, -42, 0], to: [72, -42, 80], r0: 33, r1: 30 },
    },
    {
      id: 'manifold',
      label: 'Process manifold',
      balloon: 4,
      explode: [0, 0, 156],
      geometry: {
        kind: 'tube',
        points: [
          [-120, -30, 128],
          [-40, -26, 152],
          [72, -42, 104],
        ],
        radius: 11,
      },
    },
    {
      id: 'pump',
      label: 'Microtask pump',
      balloon: 5,
      explode: [0, 0, 208],
      geometry: { kind: 'cyl', from: [152, 46, 0], to: [152, 46, 64], r0: 26, r1: 22 },
    },
    {
      id: 'discharge',
      label: 'Task discharge',
      balloon: 6,
      explode: [0, 0, 260],
      geometry: { kind: 'cyl', from: [198, 46, 72], to: [198, 46, 122], r0: 10, r1: 9 },
    },
    {
      id: 'valve',
      label: 'Locker cam valve',
      balloon: 7,
      explode: [0, 0, 312],
      geometry: { kind: 'cyl', from: [-190, 64, 0], to: [-190, 64, 56], r0: 17, r1: 15 },
    },
  ],
};

export function IsolateIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(ISOLATE_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
