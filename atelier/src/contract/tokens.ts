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

export const SHADE = [
  '#111315',
  '#171a1d',
  '#1e2226',
  '#262b30',
  '#343a40',
  '#454c53',
] as const;

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
