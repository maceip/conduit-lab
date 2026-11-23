export const BOARD = {
  page: '#0c0d0e',
  plate: '#141516',
  raised: '#1a1d20',
  line: '#586068',
  rib: '#2e3338',
  edgeHi: '#b2b8be',
  ink: '#8a9096',
  inkHi: '#e8ecee',
  live: '#f4f6f7',
  accent: '#74c7b0',
  warn: '#d9a441',
  fail: '#d4645c',
} as const;

/**
 * The three published body palettes from `v8-iso/iso-cad.mjs`.
 *
 * These are byte-identical to the published `--bd0..--bd3`, `--dk0..--dk2`
 * and `--hi0..--hi3` custom properties, so an atelier face and a published
 * face with the same normal land on the same tone. A part selects its
 * palette; the ramp is applied within it.
 *
 * There is deliberately no single flat ramp here. Collapsing every part onto
 * one ramp is what destroys the form — see `docs/drawing-standard.md` §5.
 */
export const SHADE_BODY = ['#111315', '#171a1d', '#1e2226', '#262b30'] as const;
export const SHADE_DARK = ['#0b0c0e', '#101214', '#16191c'] as const;
export const SHADE_HI = ['#8e959c', '#b2b8be', '#cfd4d8', '#e8ecef'] as const;

export const PALETTES = {
  dark: SHADE_DARK,
  body: SHADE_BODY,
  hi: SHADE_HI,
} as const;

/**
 * The tone of a machined cut face. A cut surface is a bright machined face in
 * the drawing convention, so section faces take the top of the `hi` ramp with
 * the section hatch laid over them.
 */
export const CUT_FACE = '#e8ecef';

export const STROKE = {
  structure: 1.05,
  cutEdge: 1.35,
  hidden: 0.75,
  centerline: 0.6,
  hatch: 0.5,
  leader: 0.9,
} as const;

export const DASH = {
  hidden: '2.5 2',
  centerline: '8 2 1.6 2',
} as const;

export const DURATION = { d1: 120, d2: 240, d3: 480, d4: 960 } as const;

export const EASE = {
  standard: 'cubic-bezier(0.22, 0.61, 0.36, 1)',
  feature: 'cubic-bezier(0.16, 0.84, 0.44, 1)',
} as const;

export const ISO = { azDeg: 42, elDeg: 30 } as const;
