/**
 * Turboprop kinematics (pure functions).
 *
 * Concentric twin spools with two-stage epicyclic reduction (PT6A / T56 layout):
 *   gas generator spool (3 axial stages + impeller + HP turbine)  ω_hp   = 1.00 ω
 *   free power turbine shaft (two PT stages + sun gear)          ω_free = −0.75 ω (reversed)
 *   carrier + propeller hub + 4 blades                          ω_prop = 0.05 ω (15:1 reduction)
 * Planets spin on their own pins at the rate the tooth counts dictate.
 * Every angle derives from one shared phase — nothing keeps its own clock.
 */

/** Reduction: sun (free turbine shaft) → carrier (propeller) = 0.75/0.05 = 15:1. */
export const REDUCTION = 15;

/** Two-stage teeth: stage one 5:1 (16/24/64), stage two 3:1 (16/8/32), 15:1 together. */
export const STAGE1 = { sun: 16, planet: 24, ring: 64, count: 5 };
export const STAGE2 = { sun: 16, planet: 8, ring: 32, count: 4 };

/** One planetary stage with a fixed ring: 1 + N_ring / N_sun. */
export const stageRatio = (sun: number, ring: number) => 1 + ring / sun;

/** Both stages in series. */
export const totalRatio = () => stageRatio(STAGE1.sun, STAGE1.ring) * stageRatio(STAGE2.sun, STAGE2.ring);

/** Normalise into [0, 2π). */
export const normAngle = (a: number) => ((a % (Math.PI * 2)) + Math.PI * 2) % (Math.PI * 2);

/** Gas generator spool angle (positive). */
export const hpAngle = (phase: number) => phase;

/** Free turbine shaft + sun gear angle (reversed, ×0.75). */
export const freeAngle = (phase: number) => -0.75 * phase;

/** Carrier (hub + blades) angle: ×0.05, the 15:1 reduction. */
export const carrierAngle = (phase: number) => 0.05 * phase;

/**
 * Planet spin about its own axis (relative to the carrier).
 * Fixed ring: ω_p = (ω_sun − ω_carrier) · N_sun / N_planet.
 * Counter-rotation means this value is negative (sun forward ⇒ planet reverses).
 */
export const planetSpin = (phase: number, sun: number = STAGE1.sun, planet: number = STAGE1.planet) =>
  (freeAngle(phase) - carrierAngle(phase)) * (sun / planet);

/**
 * Centre of planet i at a given phase (around the x axis, radius r, offset a0).
 * In the y-z plane: y = cos, z = sin — the same convention as the pins.
 */
export function planetCentre(i: number, phase: number, r: number, count = STAGE1.count, a0 = 0): [number, number, number] {
  const a = (i / count) * Math.PI * 2 + a0 + carrierAngle(phase);
  return [0, Math.cos(a) * r, Math.sin(a) * r];
}

/**
 * Axial fan-out of the internal chain (3 rotors + 3 stators + impeller + liner
 * + 3 turbine stages) at t = 1: each stage steps −fanStep from an anchor stage.
 * Adjacent stages gain the step in spacing, the ends giving way outward.
 */
export const fanOffset = (k: number, anchor: number, fanStep: number) => (anchor - k) * fanStep;

/** Second-stage planets (on the first-stage carrier): their spin angle. */
export const planetSpin2 = (phase: number) =>
  planetSpin(phase, STAGE2.sun, STAGE2.planet) + (carrierAngle(phase) - carrierAngle(phase)) * (STAGE2.sun / STAGE2.planet);
