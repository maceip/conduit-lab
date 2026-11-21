/**
 * 涡轮螺旋桨发动机 · 运动学纯函数 / turboprop kinematics (pure).
 *
 * 共轴双转子 + 两级行星减速（PT6A / T56 布局）：
 *   高压燃气发生器转子（轴流三级 + 离心叶轮 + 高压涡轮盘）  ω_hp   = 1.00 ω（正向）
 *   自由动力涡轮轴（两级动力涡轮 + 太阳轮）                ω_free = −0.75 ω（反向）
 *   行星架 + 螺旋桨毂 + 4 叶                              ω_prop = 0.05 ω（15:1 减速）
 * 行星轮绕自身行星销轴自转，转速由真实齿数差动关系给出。
 * 所有转角都从同一个相位量 phase 推出，不各自计时。
 */

/** 减速比：太阳轮(自由涡轮轴) → 行星架(螺旋桨) = 0.75/0.05 = 15:1。 */
export const REDUCTION = 15;

/** 两级行星轮系齿数：第一级 5:1（16/24/64），第二级 3:1（16/8/32），合计 15:1。 */
export const STAGE1 = { sun: 16, planet: 24, ring: 64, count: 5 };
export const STAGE2 = { sun: 16, planet: 8, ring: 32, count: 4 };

/** 单级行星减速比（齿圈固定）：1 + N_ring / N_sun。 */
export const stageRatio = (sun: number, ring: number) => 1 + ring / sun;

/** 两级串联总减速比。 */
export const totalRatio = () => stageRatio(STAGE1.sun, STAGE1.ring) * stageRatio(STAGE2.sun, STAGE2.ring);

/** 归一化到 [0, 2π)。 */
export const normAngle = (a: number) => ((a % (Math.PI * 2)) + Math.PI * 2) % (Math.PI * 2);

/** 高压燃气发生器转子转角（正向）。 */
export const hpAngle = (phase: number) => phase;

/** 自由动力涡轮轴 + 太阳轮转角（反向，0.75 倍）。 */
export const freeAngle = (phase: number) => -0.75 * phase;

/** 行星架（螺旋桨毂 + 桨叶）转角：0.05 倍，15:1 减速。 */
export const carrierAngle = (phase: number) => 0.05 * phase;

/**
 * 行星轮绕自身轴线的自转角（相对行星架）。
 * 齿圈固定：ω_p = (ω_sun − ω_carrier) · N_sun / N_planet。
 * 「反向自转」即该值为负（太阳轮正转时行星轮倒转）。
 */
export const planetSpin = (phase: number, sun: number = STAGE1.sun, planet: number = STAGE1.planet) =>
  (freeAngle(phase) - carrierAngle(phase)) * (sun / planet);

/**
 * 第 i 个行星轮中心在相位 phase 时的位置（绕 x 轴、半径 r，参考角 a0）。
 * yz 平面内：y = cos, z = sin，与柱销同一约定。
 */
export function planetCentre(i: number, phase: number, r: number, count = STAGE1.count, a0 = 0): [number, number, number] {
  const a = (i / count) * Math.PI * 2 + a0 + carrierAngle(phase);
  return [0, Math.cos(a) * r, Math.sin(a) * r];
}

/**
 * 内部轴向链（三级轴流转子 + 三级静子环 + 离心叶轮 + 燃烧室火焰筒 + 三级涡轮）
 * 在 t = 1 时的 x 向扇出偏移：每级 −fanStep，锚点级不动。
 * 「−0.4u step per stage」：相邻级间距增加 0.4u，前后级向两端让开。
 */
export const fanOffset = (k: number, anchor: number, fanStep: number) => (anchor - k) * fanStep;

/** 两级行星：第二级行星轮（装在第一级行星架上）的自转角。 */
export const planetSpin2 = (phase: number) =>
  planetSpin(phase, STAGE2.sun, STAGE2.planet) + (carrierAngle(phase) - carrierAngle(phase)) * (STAGE2.sun / STAGE2.planet);
