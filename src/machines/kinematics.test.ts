import { describe, expect, it } from 'vitest';
import { CP } from './coupling/data';
import { normAngle, pinPosition } from './coupling';

/**
 * 运动学单元测试：把"动的逻辑"写成纯函数再测（见 .claude/skills/mechanical-drawing/SKILL.md 第 4 步）。
 * 改机器时照着这个文件加自己的极限位置 / 对称 / 行程检查。
 */
describe('弹性柱销联轴器 · 柱销分布', () => {
  it('一圈 6 根柱销，都落在分布圆上（半径 = boltR）', () => {
    for (let i = 0; i < CP.pins; i += 1) {
      const [x, y, z] = pinPosition(i, 0);
      expect(x).toBe(0);
      expect(Math.hypot(y, z)).toBeCloseTo(CP.boltR, 6);
    }
  });

  it('柱销绕轴线（x）在 y-z 平面内转：转角增加 θ，位置绕 x 轴转 θ', () => {
    const p0 = pinPosition(1, 0);
    const p1 = pinPosition(1, Math.PI / 2);
    expect(p0[0]).toBe(p1[0]); // x 不变（轴向不移动）
    expect(Math.hypot(p1[1], p1[2])).toBeCloseTo(Math.hypot(p0[1], p0[2]), 6);
  });

  it('转一整圈回到原位', () => {
    for (let i = 0; i < CP.pins; i += 1) {
      const a = pinPosition(i, 0);
      const b = pinPosition(i, Math.PI * 2);
      expect(a[1]).toBeCloseTo(b[1], 6);
      expect(a[2]).toBeCloseTo(b[2], 6);
    }
  });

  it('角度归一化落在 [0, 2π)', () => {
    for (const a of [-7, -0.1, 0, 9.9, 123]) {
      const n = normAngle(a);
      expect(n).toBeGreaterThanOrEqual(0);
      expect(n).toBeLessThan(Math.PI * 2);
    }
  });

  it('柱销数、柱销长等关键尺寸为合理正值', () => {
    expect(CP.pins).toBeGreaterThanOrEqual(3);
    expect(CP.pinLen).toBeGreaterThan(CP.gap);
    expect(CP.discR).toBeGreaterThan(CP.boreR);
  });
});

/* ────────────────────────── 涡桨发动机 ────────────────────────── */

import {
  REDUCTION, STAGE1, STAGE2, carrierAngle, fanOffset, freeAngle, hpAngle,
  normAngle as tpNorm, planetCentre, planetSpin, stageRatio, totalRatio,
} from './turboprop/kinematics';
import { TP, fanX } from './turboprop/data';

describe('涡桨发动机 · 双转子与行星减速', () => {
  it('三个转速比 = 1 : −0.75 : 0.05，且 0.75/0.05 = 15:1', () => {
    expect(hpAngle(1)).toBeCloseTo(1, 12);
    expect(freeAngle(1)).toBeCloseTo(-0.75, 12);
    expect(carrierAngle(1)).toBeCloseTo(0.05, 12);
    expect(freeAngle(1) / carrierAngle(1)).toBeCloseTo(-REDUCTION, 12);
  });

  it('两级行星齿数各约 5:1 / 3:1，串联总减速比 = 15:1', () => {
    expect(stageRatio(STAGE1.sun, STAGE1.ring)).toBeCloseTo(5, 12);
    expect(stageRatio(STAGE2.sun, STAGE2.ring)).toBeCloseTo(3, 12);
    expect(totalRatio()).toBeCloseTo(REDUCTION, 12);
  });

  it('行星轮反向自转：太阳轮正转时自转角为负，比例 = N_sun/N_planet', () => {
    const ph = 2.5;
    const expected = (freeAngle(ph) - carrierAngle(ph)) * (STAGE1.sun / STAGE1.planet);
    expect(planetSpin(ph)).toBeCloseTo(expected, 12);
    expect(planetSpin(ph)).toBeLessThan(0); // 反向
  });

  it('5 个行星轮在销圆上均布，随行星架公转 0.05ω', () => {
    const r = 105;
    for (let i = 0; i < STAGE1.count; i += 1) {
      const [x, y, z] = planetCentre(i, 0, r);
      expect(x).toBe(0);
      expect(Math.hypot(y, z)).toBeCloseTo(r, 6);
    }
    const a = planetCentre(0, 0, r);
    const b = planetCentre(0, Math.PI * 2 / 0.05 / 2, r); // 行星架转 π
    expect(Math.atan2(b[2], b[1]) - Math.atan2(a[2], a[1])).toBeCloseTo(Math.PI, 6);
  });

  it('转一整圈相位回到原位，角度归一化落在 [0, 2π)', () => {
    for (const ph of [-7, -0.1, 0, 9.9, 123]) {
      const n = tpNorm(ph);
      expect(n).toBeGreaterThanOrEqual(0);
      expect(n).toBeLessThan(Math.PI * 2);
    }
    // 行星架转满一整圈（carrierAngle = 2π → phase = 2π/0.05）后回到原位。
    const a = planetCentre(2, 0, 105);
    const b = planetCentre(2, Math.PI * 2 / 0.05, 105);
    expect(a[1]).toBeCloseTo(b[1], 6);
    expect(a[2]).toBeCloseTo(b[2], 6);
  });

  it('内部链扇出：每级步长 −0.4u，t=1 时相邻级间距增加 0.4u', () => {
    const step = TP.u * TP.fanStep;
    for (let k = 0; k < 10; k += 1) {
      expect(fanX(k) - fanX(k + 1)).toBeCloseTo(step, 6);
      expect(fanOffset(k, TP.fanAnchor, step)).toBeCloseTo(fanX(k), 6);
    }
  });

  it('关键尺寸为正且桨叶数/叶排数在工程范围内', () => {
    expect(TP.propR).toBeGreaterThan(TP.bladeRootR);
    expect(TP.AY).toBeGreaterThan(TP.propR * 0.4);
    for (const n of TP.bladeCounts) { expect(n).toBeGreaterThanOrEqual(19); expect(n).toBeLessThanOrEqual(37); }
    for (const n of TP.statorCounts) { expect(n).toBeGreaterThanOrEqual(19); expect(n).toBeLessThanOrEqual(37); }
    expect(TP.ringTeeth).toBe(TP.sunTeeth + 2 * TP.planetTeeth); // 行星同心条件
  });
});
