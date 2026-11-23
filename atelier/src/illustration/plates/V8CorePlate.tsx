import { useId, useMemo } from 'react';
import type { PlateProps } from '../../contract';
import { projectAssembly, renderPlate, stadiumLoop, type Assembly } from '../engine';

/**
 * V8 Mandatory Core, exploded — the hero plate.
 *
 * The eight core machines of the V8 browser engine as ONE continuous exploded
 * assembly along a single shared vertical axis: the base skid, the isolate
 * twin silos and their manifold, the tagged pointer lattice and a tagged
 * pointer cell, the hidden-class trunk and node, the lexer, the Pratt parser
 * and the AST it builds, the bytecode dispatch loop with its injector, the
 * old-generation slab, and the new-space nursery.
 *
 * Each machine keeps the geometry of its own figure in `v8-iso/pages/`, so
 * the plate reads as the same machinery as the eight icons, taken apart
 * further.
 */
export const V8_CORE_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: true,
  caption: {
    figure: 'FIG 09',
    name: 'V8 mandatory core — exploded',
    scale: 'NTS',
    note: 'One continuous explode axis',
  },
  parts: [
    {
      id: 'base',
      label: 'Base skid',
      balloon: 1,
      geometry: { kind: 'box', at: [-150, -76, 0], size: [300, 152, 12] },
    },
    {
      id: 'isolate-main',
      label: 'Isolate main silo',
      balloon: 2,
      explode: [0, 0, 40],
      sectioned: true,
      geometry: { kind: 'cyl', from: [-96, -36, 0], to: [-96, -36, 36], r0: 26, r1: 23 },
    },
    {
      id: 'isolate-realm',
      label: 'Isolate realm silo',
      balloon: 3,
      explode: [0, 0, 80],
      geometry: { kind: 'cyl', from: [52, -28, 0], to: [52, -28, 30], r0: 17, r1: 15 },
    },
    {
      id: 'isolate-manifold',
      label: 'Isolate manifold',
      balloon: 4,
      explode: [0, 0, 120],
      geometry: {
        kind: 'tube',
        points: [
          [-96, -36, 42],
          [-40, -30, 52],
          [52, -28, 34],
        ],
        radius: 6,
      },
    },
    {
      id: 'tag-lattice',
      label: 'Tagged pointer lattice',
      balloon: 5,
      explode: [0, 0, 160],
      geometry: { kind: 'box', at: [-124, -52, 0], size: [248, 104, 8] },
    },
    {
      id: 'tag-cell',
      label: 'Tagged pointer cell',
      balloon: 6,
      explode: [0, 0, 200],
      geometry: { kind: 'box', at: [-36, -28, 0], size: [72, 56, 16] },
    },
    {
      id: 'hidden-trunk',
      label: 'Hidden class trunk',
      balloon: 7,
      explode: [0, 0, 240],
      geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 34], r0: 11, r1: 11 },
    },
    {
      id: 'hidden-node',
      label: 'Hidden class node',
      balloon: 8,
      explode: [0, 0, 280],
      geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 22], r0: 19, r1: 19 },
    },
    {
      id: 'lexer',
      label: 'Lexer',
      balloon: 9,
      explode: [0, 0, 320],
      geometry: { kind: 'box', at: [-58, -36, 0], size: [116, 72, 20] },
    },
    {
      id: 'pratt',
      label: 'Pratt parser',
      balloon: 10,
      explode: [0, 0, 360],
      sectioned: true,
      geometry: { kind: 'box', at: [-50, -32, 0], size: [100, 64, 26] },
    },
    {
      id: 'ast',
      label: 'AST',
      balloon: 11,
      explode: [0, 0, 400],
      geometry: { kind: 'box', at: [-32, -26, 0], size: [64, 52, 12] },
    },
    {
      id: 'ignition-loop',
      label: 'Bytecode dispatch loop',
      balloon: 12,
      explode: [0, 0, 440],
      geometry: {
        kind: 'tube',
        points: stadiumLoop(0, 0, 18, 68, 18, 8),
        radius: 5,
      },
    },
    {
      id: 'injector',
      label: 'Dispatch injector',
      balloon: 13,
      explode: [0, 0, 480],
      sectioned: true,
      geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 34], r0: 11, r1: 8 },
    },
    {
      id: 'old-space',
      label: 'Old generation slab',
      balloon: 14,
      explode: [0, 0, 520],
      geometry: { kind: 'box', at: [-130, -58, 0], size: [260, 116, 10] },
    },
    {
      id: 'new-space',
      label: 'New space nursery',
      balloon: 15,
      explode: [0, 0, 560],
      geometry: { kind: 'box', at: [-104, -50, 0], size: [208, 100, 14] },
    },
  ],
};

export function V8CorePlate({ className, tone = 'neutral', title }: PlateProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(V8_CORE_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated: true, title, className });
}
