import { describe, expect, it } from 'vitest';
import { CP } from './coupling/data';
import { normAngle, pinPosition } from './coupling';

/**
 * Kinematics unit tests: write the motion logic as pure functions and test them
 * (skill step 4). When the machine changes, add limit / symmetry / travel checks here.
 */
describe('Pin coupling · pin circle', () => {
  it('all six pins sit on the bolt circle (radius = boltR)', () => {
    for (let i = 0; i < CP.pins; i += 1) {
      const [x, y, z] = pinPosition(i, 0);
      expect(x).toBe(0);
      expect(Math.hypot(y, z)).toBeCloseTo(CP.boltR, 6);
    }
  });

  it('pins orbit the x axis in the y-z plane: +θ rotates the position by θ', () => {
    const p0 = pinPosition(1, 0);
    const p1 = pinPosition(1, Math.PI / 2);
    expect(p0[0]).toBe(p1[0]); // x stays put (no axial travel)
    expect(Math.hypot(p1[1], p1[2])).toBeCloseTo(Math.hypot(p0[1], p0[2]), 6);
  });

  it('a full turn returns to the start', () => {
    for (let i = 0; i < CP.pins; i += 1) {
      const a = pinPosition(i, 0);
      const b = pinPosition(i, Math.PI * 2);
      expect(a[1]).toBeCloseTo(b[1], 6);
      expect(a[2]).toBeCloseTo(b[2], 6);
    }
  });

  it('normalised angle lands in [0, 2π)', () => {
    for (const a of [-7, -0.1, 0, 9.9, 123]) {
      const n = normAngle(a);
      expect(n).toBeGreaterThanOrEqual(0);
      expect(n).toBeLessThan(Math.PI * 2);
    }
  });

  it('pin count, pin length and other key sizes are sensible positives', () => {
    expect(CP.pins).toBeGreaterThanOrEqual(3);
    expect(CP.pinLen).toBeGreaterThan(CP.gap);
    expect(CP.discR).toBeGreaterThan(CP.boreR);
  });
});

/* ────────────────────────── Turboprop ────────────────────────── */

import {
  REDUCTION, STAGE1, STAGE2, carrierAngle, freeAngle, hpAngle,
  normAngle as tpNorm, planetCentre, planetSpin, stageRatio, totalRatio,
} from './turboprop/kinematics';
import { PARTS, TP } from './turboprop/data';

describe('Turboprop · twin spools and epicyclic reduction', () => {
  it('speeds run 1 : −0.75 : 0.05, and 0.75/0.05 = 15:1', () => {
    expect(hpAngle(1)).toBeCloseTo(1, 12);
    expect(freeAngle(1)).toBeCloseTo(-0.75, 12);
    expect(carrierAngle(1)).toBeCloseTo(0.05, 12);
    expect(freeAngle(1) / carrierAngle(1)).toBeCloseTo(-REDUCTION, 12);
  });

  it('the two planetary stages are 5:1 and 3:1, 15:1 in series', () => {
    expect(stageRatio(STAGE1.sun, STAGE1.ring)).toBeCloseTo(5, 12);
    expect(stageRatio(STAGE2.sun, STAGE2.ring)).toBeCloseTo(3, 12);
    expect(totalRatio()).toBeCloseTo(REDUCTION, 12);
  });

  it('planets counter-spin: with the sun forward their spin is negative, ratio N_sun/N_planet', () => {
    const ph = 2.5;
    const expected = (freeAngle(ph) - carrierAngle(ph)) * (STAGE1.sun / STAGE1.planet);
    expect(planetSpin(ph)).toBeCloseTo(expected, 12);
    expect(planetSpin(ph)).toBeLessThan(0); // opposite direction
  });

  it('five planets sit evenly on the pin circle and orbit with the carrier at 0.05ω', () => {
    const r = 105;
    for (let i = 0; i < STAGE1.count; i += 1) {
      const [x, y, z] = planetCentre(i, 0, r);
      expect(x).toBe(0);
      expect(Math.hypot(y, z)).toBeCloseTo(r, 6);
    }
    const a = planetCentre(0, 0, r);
    const b = planetCentre(0, Math.PI * 2 / 0.05 / 2, r); // carrier turns π
    expect(Math.atan2(b[2], b[1]) - Math.atan2(a[2], a[1])).toBeCloseTo(Math.PI, 6);
  });

  it('a full carrier turn returns to the start; angles normalise to [0, 2π)', () => {
    for (const ph of [-7, -0.1, 0, 9.9, 123]) {
      const n = tpNorm(ph);
      expect(n).toBeGreaterThanOrEqual(0);
      expect(n).toBeLessThan(Math.PI * 2);
    }
    // One full carrier turn (carrierAngle = 2π ⇒ phase = 2π/0.05) returns to the start.
    const a = planetCentre(2, 0, 105);
    const b = planetCentre(2, Math.PI * 2 / 0.05, 105);
    expect(a[1]).toBeCloseTo(b[1], 6);
    expect(a[2]).toBeCloseTo(b[2], 6);
  });

  it('internal fan-out: rotors −0.50u per stage, stators +0.85u radial, turbine chain Δ −2.55..−3.15u (map)', () => {
    const byId = (id: string) => PARTS.find((pp) => pp.id === id)!;
    // rotor stages step 0.50u apart
    expect(byId('rotor-1').explode[0] - byId('rotor-2').explode[0]).toBeCloseTo(TP.u * 0.5, 6);
    expect(byId('rotor-2').explode[0] - byId('rotor-3').explode[0]).toBeCloseTo(TP.u * 0.5, 6);
    // stator rings rise radially +0.85u
    for (const id of ['stator-1', 'stator-2', 'stator-3']) {
      expect(byId(id).explode[1]).toBeCloseTo(TP.u * 0.85, 6);
    }
    // turbine chain Δ: HP −2.55u, PT1 −2.85u, PT2 −3.15u
    expect(byId('hp-turbine').explode[0]).toBeCloseTo(-TP.u * 2.55, 6);
    expect(byId('pt-disk-1').explode[0]).toBeCloseTo(-TP.u * 2.85, 6);
    expect(byId('pt-disk-2').explode[0]).toBeCloseTo(-TP.u * 3.15, 6);
    // blades +1.15u radial, liner −1.25u, impeller −0.90u (map)
    expect(byId('blade-1').explode[1]).toBeCloseTo(TP.u * 1.15, 6);
    expect(byId('combustor-liner').explode[0]).toBeCloseTo(-TP.u * 1.25, 6);
    expect(byId('impeller').explode[0]).toBeCloseTo(-TP.u * 0.9, 6);
  });

  it('key sizes are positive and blade counts sit in the engineering range', () => {
    expect(TP.propR).toBeGreaterThan(TP.bladeRootR);
    expect(TP.AY).toBeGreaterThan(TP.propR * 0.4);
    for (const n of TP.bladeCounts) { expect(n).toBeGreaterThanOrEqual(19); expect(n).toBeLessThanOrEqual(37); }
    for (const n of TP.statorCounts) { expect(n).toBeGreaterThanOrEqual(19); expect(n).toBeLessThanOrEqual(37); }
    expect(TP.ringTeeth).toBe(TP.sunTeeth + 2 * TP.planetTeeth); // planetary congruence
  });
});
