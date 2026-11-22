/**
 * Maglev kinematics (pure functions).
 *
 * The car lifts on attracted C-core magnets to a nominal 10 mm gap; the
 * long-stator linear motor's travelling field is locked to position, so the
 * electrical phase advances 2π per pole pitch of travel. Everything derives
 * from one shared phase — nothing keeps its own clock.
 */

import { MG } from './data';

/** Nominal levitation and guidance gap (mm). */
export const LEV_GAP = MG.levGap;

const smooth = (t: number) => {
  const x = Math.min(1, Math.max(0, t));
  return x * x * (3 - 2 * x);
};

/** Levitation gap in mm: 0 on the skid rails, easing open to 10 mm airborne. */
export function levitationGap(t: number): number {
  return LEV_GAP * smooth(t);
}

/** Guidance centreline offset (mm): ±1 mm of measured wander at speed. */
export function guidanceOffset(phase: number): number {
  return Math.sin(phase * 0.5) * 1.0;
}

/** Travel along the beam (mm) for animation phase p (radians), at a crawl. */
export function travelX(phase: number): number {
  return phase * 60;
}

/**
 * Long-stator electrical phase for a position x: 2π per pole pitch.
 * Synchronous by construction — the field and the car's magnets never slip
 * unless the controller commands it.
 */
export function statorPhase(x: number): number {
  return (x / MG.polePitch) * Math.PI * 2;
}

/** Plug-door travel 0..1 (lift + slide into the shell pocket). */
export function doorTravel(t: number): number {
  return smooth(t);
}

/** Normalise into [0, 2π). */
export const normAngle = (a: number) => ((a % (Math.PI * 2)) + Math.PI * 2) % (Math.PI * 2);
