import { useId, useMemo } from 'react';
import type { PlateProps } from '../../contract';
import { gear2D, projectAssembly, renderPlate, type Assembly } from '../engine';

/**
 * Verified kernel vs. sandboxed renderer — the Act 3 strategy plate.
 *
 * Source: Act 3 of `docs/site-redesign-proposal.md` — "one isometric plate,
 * proved kernel in front of disposable per-site renderers, hatched where
 * components are still design-only (kernel, Nanvix, HTML/CSS)".
 *
 * On this plate `sectioned` carries the meaning the proposal asks for:
 *
 *  - `sectioned: true`  -> the component is **design only**, not yet proved.
 *    Its cut face is hatched, so it reads as an open question.
 *  - `sectioned: false` -> the component is **proved** against the published
 *    standard and stays clean.
 *
 * The proved core sits in front (smaller y, nearer the camera) and the
 * per-site renderers behind it, which is the argument the plate has to make.
 * The legend in the title block states the reading outright.
 *
 * Tones: the ramp is applied within the part's own palette, exactly as the
 * published figures do it — `hi` for the prominent machined element, `dark`
 * for understructure, `body` for the main mass. Here: `hi` = kernel-core; `dark` = proof-link, nanvix-isolation; the rest `body`.
 */
export const KERNEL_RENDERER_ASSEMBLY: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [1, 0, 0],
  explodeScale: 1,
  partsList: true,
  caption: {
    figure: 'FIG 10',
    name: 'Verified kernel vs sandboxed renderer',
    scale: 'NTS',
    note: 'Hatched = design only',
    legend: [
      { label: 'Design only — not yet proved', hatched: true },
      { label: 'Proved against the standard', hatched: false },
    ],
  },
  parts: [
    {
      id: 'kernel-core',
      label: 'Proved kernel core',
      palette: 'hi',
      balloon: 1,
      geometry: { kind: 'box', at: [-200, -110, 0], size: [220, 130, 62] },
    },
    {
      id: 'ratchet',
      label: 'Trusted-item ratchet',
      palette: 'body',
      balloon: 2,
      explode: [96, 0, 0],
      geometry: {
        kind: 'extrude',
        poly: gear2D(12, 34, 44).map(([u, v]) => [u - 30, v + 40] as [number, number]),
        depth: 16,
      },
    },
    {
      id: 'proof-link',
      label: 'Proof obligation link',
      palette: 'dark',
      balloon: 3,
      explode: [192, 0, 0],
      geometry: { kind: 'cyl', from: [0, -20, 0], to: [90, -20, 0], r0: 9, r1: 9 },
    },
    {
      id: 'site-renderer',
      label: 'Disposable per-site renderer',
      palette: 'body',
      balloon: 4,
      explode: [288, 0, 0],
      geometry: { kind: 'box', at: [-80, 26, 0], size: [170, 108, 50] },
    },
    {
      id: 'kernel-theorems',
      label: 'Kernel theorem set',
      palette: 'body',
      balloon: 5,
      explode: [384, 0, 0],
      sectioned: true,
      geometry: { kind: 'box', at: [-80, -18, 0], size: [160, 96, 44] },
    },
    {
      id: 'nanvix-isolation',
      label: 'Nanvix renderer isolation',
      palette: 'dark',
      balloon: 6,
      explode: [480, 0, 0],
      sectioned: true,
      geometry: { kind: 'box', at: [-70, 30, 0], size: [140, 92, 58] },
    },
    {
      id: 'html-css-layout',
      label: 'HTML/CSS layout',
      palette: 'body',
      balloon: 7,
      explode: [576, 0, 0],
      sectioned: true,
      geometry: { kind: 'box', at: [-60, -44, 0], size: [120, 86, 34] },
    },
  ],
};

export function KernelRendererPlate({ className, tone = 'neutral', title }: PlateProps) {
  const id = useId();
  const plate = useMemo(() => projectAssembly(KERNEL_RENDERER_ASSEMBLY), []);
  return renderPlate(plate, { idPrefix: id, tone, annotated: true, title, className });
}
