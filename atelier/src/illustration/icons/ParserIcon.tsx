import { useId, useMemo } from 'react';
import type { IconProps } from '../../contract';
import { helix3D, projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Lexer to Pratt parser to AST.
 *
 * Source: `v8-iso/pages/fig-04-parser.html`. That plate draws a circular
 * electromagnetic drive base with three helical coil isolation springs, an
 * open conical stepped vibratory feeder bowl with a climbing helical token
 * track, a tangential linear outfeed chute with an overhead optical ring
 * sensor, a pivoting flapper diverter vane at the Y junction, and the two
 * conical hopper cyclones — one for the AST, one for ScopeInfo.
 *
 * The token track is the real 3D helix from the source figure, swept as a
 * tube.
 */
export const PARSER_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [1, 0, 0],
  explodeScale: 1,
  partsList: false,
  parts: [
    {
      id: 'drive-base',
      label: 'Drive base',
      balloon: 1,
      geometry: { kind: 'cyl', from: [-150, 0, 0], to: [-150, 0, 22], r0: 56, r1: 50 },
    },
    {
      id: 'bowl',
      label: 'Feeder bowl',
      balloon: 2,
      explode: [34, 0, 0],
      geometry: { kind: 'cyl', from: [-150, 0, 22], to: [-150, 0, 88], r0: 46, r1: 78 },
    },
    {
      id: 'spiral',
      label: 'Token spiral',
      balloon: 3,
      explode: [68, 0, 0],
      geometry: {
        kind: 'tube',
        points: helix3D(-150, 0, 50, 70, 30, 82, 2.15, 12),
        radius: 5,
      },
    },
    {
      id: 'chute',
      label: 'Outfeed chute',
      balloon: 4,
      explode: [102, 0, 0],
      geometry: {
        kind: 'tube',
        points: [
          [-86, -40, 88],
          [-20, -30, 108],
          [56, -18, 116],
        ],
        radius: 11,
      },
    },
    {
      id: 'sensor',
      label: 'Optical ring sensor',
      balloon: 5,
      explode: [136, 0, 0],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-40, -30, 104], to: [-18, -22, 99], r0: 23, r1: 23 },
    },
    {
      id: 'vane',
      label: 'Y-diverter vane',
      balloon: 6,
      explode: [170, 0, 0],
      geometry: { kind: 'box', at: [66, -26, 94], size: [46, 12, 22] },
    },
    {
      id: 'cyclone',
      label: 'AST cyclone',
      balloon: 7,
      explode: [204, 0, 0],
      geometry: { kind: 'cyl', from: [150, -52, 0], to: [150, -52, 58], r0: 23, r1: 39 },
    },
  ],
};

export function ParserIcon({
  size = 32,
  className,
  tone = 'neutral',
  annotated = true,
  title,
}: IconProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(PARSER_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated, title, size, className });
}
