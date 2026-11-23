import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Hidden-class transition tree.
 *
 * Source: `v8-iso/pages/fig-03-hidden-classes.html`. That plate draws a
 * monolithic cast-iron swan-neck C-frame with stiffening flange ribs, a top
 * hydraulic striker cylinder with its descending ram, a coaxial rotating
 * upper punch platter over a lower die bolster, six hardened punch and die
 * bushing stations around the rotary turret, and a cantilevered pantograph
 * arm carrying a perforated JSObject sheet-metal blank.
 *
 * The C-frame is lofted as a bent web, which is the one part in this package
 * that uses the `loft` primitive.
 *
 * Tones: the ramp is applied within the part's own palette, exactly as the
 * published figures do it — `hi` for the prominent machined element, `dark`
 * for understructure, `body` for the main mass. Here: `hi` = punch, striker; `dark` = bolster, turret; the rest `body`.
 */
export const HIDDEN_CLASSES_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'c-frame',
      label: 'Swan-neck C-frame',
      palette: 'body',
      balloon: 1,
      geometry: {
        kind: 'loft',
        stations: [
          [-170, 0, 0],
          [-170, 0, 96],
          [-150, 0, 150],
          [-60, 0, 176],
          [70, 0, 176],
          [140, 0, 150],
          [140, 0, 60],
        ],
      },
    },
    {
      id: 'bolster',
      label: 'Die bolster',
      palette: 'dark',
      balloon: 2,
      explode: [0, 0, 48],
      sectioned: true,
      geometry: { kind: 'cyl', from: [10, 0, 0], to: [10, 0, 22], r0: 47, r1: 47 },
    },
    {
      id: 'turret',
      label: 'Punch turret',
      palette: 'dark',
      balloon: 3,
      explode: [0, 0, 96],
      geometry: { kind: 'cyl', from: [10, 0, 44], to: [10, 0, 64], r0: 45, r1: 45 },
    },
    {
      id: 'die',
      label: 'Die station',
      palette: 'body',
      balloon: 4,
      explode: [0, 0, 144],
      geometry: { kind: 'cyl', from: [10, 0, 0], to: [10, 0, 22], r0: 16, r1: 13 },
    },
    {
      id: 'punch',
      label: 'Punch',
      palette: 'hi',
      balloon: 5,
      explode: [0, 0, 192],
      geometry: { kind: 'cyl', from: [10, 0, 0], to: [10, 0, 20], r0: 13, r1: 14 },
    },
    {
      id: 'sheet',
      label: 'JSObject sheet',
      palette: 'body',
      balloon: 6,
      explode: [0, 0, 240],
      geometry: { kind: 'box', at: [58, -44, 0], size: [92, 88, 9] },
    },
    {
      id: 'striker',
      label: 'Hydraulic striker',
      palette: 'hi',
      balloon: 7,
      explode: [0, 0, 288],
      geometry: { kind: 'cyl', from: [30, 0, 0], to: [30, 0, 56], r0: 20, r1: 17 },
    },
  ],
};

export function HiddenClassesIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(HIDDEN_CLASSES_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
