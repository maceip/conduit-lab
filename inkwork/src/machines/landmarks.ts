import type { Vec3 } from './types';

export interface PrimaryLandmark {
  partId: string;
  /** Drawing index 1..31 from PARTS. */
  index: number;
  /** Concise mechanical assembly label (<= 15 chars so Ortho pills never crowd). */
  short: string;
  /** Mapped browser-engine / security-kernel counterpart. */
  counterpart: string;
  /** Non-overlapping Ortho leader rail & horizontal slot (0 = aft, 1 = mid, 2 = fwd). */
  rail: 'top' | 'bottom';
  slot: 0 | 1 | 2;
  /** Model-space datum point (unscaled mm) on the outer rim of the part. */
  anchor: Vec3;
}

export const MACHINE_LANDMARKS: Record<string, PrimaryLandmark[]> = {
  turboprop: [
    {
      partId: 'exhaust',
      index: 9,
      short: 'Exhaust Ducts',
      counterpart: 'Deoptimizer',
      rail: 'top',
      slot: 0,
      anchor: [-1460, 1340, 0],
    },
    {
      partId: 'impeller',
      index: 26,
      short: 'Impeller Core',
      counterpart: 'TurboFan JIT',
      rail: 'top',
      slot: 1,
      anchor: [-590, 1410, 0],
    },
    {
      partId: 'spinner',
      index: 1,
      short: 'Spinner Cone',
      counterpart: 'Parser (J3)',
      rail: 'top',
      slot: 2,
      anchor: [1340, 1180, 0],
    },
    {
      partId: 'combustor-liner',
      index: 27,
      short: 'Flame Liner',
      counterpart: 'Ignition VM (J7)',
      rail: 'bottom',
      slot: 0,
      anchor: [-1120, 760, 0],
    },
    {
      partId: 'rotor-1',
      index: 20,
      short: 'Axial Rotor',
      counterpart: 'Hidden Classes (J2)',
      rail: 'bottom',
      slot: 1,
      anchor: [-140, 760, 0],
    },
    {
      partId: 'gearbox',
      index: 8,
      short: '15:1 Gearbox',
      counterpart: 'Orinoco GC (J6)',
      rail: 'bottom',
      slot: 2,
      anchor: [620, 740, 220],
    },
  ],
  maglev: [
    {
      partId: 'roof-fairing',
      index: 7,
      short: 'Roof & Bulkhead',
      counterpart: 'SOP / CSP Policy',
      rail: 'top',
      slot: 0,
      anchor: [10600, 7820, 0],
    },
    {
      partId: 'side-shell-left',
      index: 8,
      short: 'Torsion Carbody',
      counterpart: 'Per-Site Renderer',
      rail: 'top',
      slot: 1,
      anchor: [16400, 7550, 900],
    },
    {
      partId: 'nose-cone',
      index: 1,
      short: 'TR08 Nose Cab',
      counterpart: 'Verdict X.509',
      rail: 'top',
      slot: 2,
      anchor: [24600, 5850, 0],
    },
    {
      partId: 'beam-shell',
      index: 30,
      short: 'Guideway Girder',
      counterpart: 'OS / Hardware Base',
      rail: 'bottom',
      slot: 0,
      anchor: [1800, 1250, 1400],
    },
    {
      partId: 'stator-pack-left',
      index: 24,
      short: 'LSM Stator',
      counterpart: 'Verus Kernel',
      rail: 'bottom',
      slot: 1,
      anchor: [12600, 1280, 1400],
    },
    {
      partId: 'lev-magnet-fl',
      index: 15,
      short: '10 mm EMS Gap',
      counterpart: 'Vest IPC Gap',
      rail: 'bottom',
      slot: 2,
      anchor: [21500, 1380, 1620],
    },
  ],
};

export function findLandmark(machineId: string, partId: string): PrimaryLandmark | undefined {
  return MACHINE_LANDMARKS[machineId]?.find((l) => l.partId === partId);
}
