import type { BoltSetDef, CameraDef, GuideDef, PartDef, StepDef, Vec3 } from '../types';

/**
 * 涡轮螺旋桨发动机 · Turboprop Engine (PT6A / T56 架构)
 *
 * 是什么、讲什么：自由涡轮式涡桨发动机——空气经轴流三级压气机加压后在离心叶轮扩压，
 *   环形回流燃烧室点火做功，高压涡轮驱动压气机转子，两级反向旋转自由动力涡轮
 *   经 15:1 两级行星减速器带动恒速螺旋桨。动画的因果：燃气发生器转（1.0ω）→
 *   自由涡轮反向转（0.75ω）→ 行星架慢转（0.05ω）→ 桨叶随之转。
 *
 * 尺寸来源：公开的普惠 PT6A / 艾利逊 T56 通用布局与公开外形数据，非具体型号图纸。
 *   轴向站位与爆炸位移按「装配/爆炸对照表」（u 单位，1u = 400 mm）落位：
 *   桨毂 +2.65u、减速箱 +1.45u、三级轴流 −0.55..−1.32u、离心叶轮 −1.85u、
 *   火焰筒 −2.85u、涡轮 −2.65..−3.35u；t=1 时各组按表中 Δ 与径向扇出移开。
 *   为保证 t=0 零重叠，本机保留顺序轴向布局（压气机→叶轮→火焰筒→涡轮向后排），
 *   火焰筒取大涵道内径（涡轮盘置于筒内孔中）——即回流折返的真实结构。
 *
 * 单位与坐标：毫米。+x 朝前（螺旋桨方向），−x 朝后（尾锥排气），+y 朝上，
 *   发动机轴线在 y=AY=1150、z=0，安装桁架最低点 y=0；左右对称面 z=0。
 *   剖视沿 z=0 切掉 z>0 半边——短舱、齿轮箱机匣、扩压机匣、火焰筒均关于 z=0
 *   对称且挖空，半剖即露出行星齿轮、叶排与迷宫密封（主视图与三视图同步剖开）。
 *
 * 分级：31 个零件一级（线稿渲染器上限 31）；A–F 六个子组件共 46 个零件
 *   （propeller / gearbox / airflow / compressor / combustor / turbine）。
 *
 * 怎么动：双转子同心反转 + 行星减速（kinematics.ts 纯函数与单测）：
 *   高压燃气发生器 1.0ω，自由涡轮轴+太阳轮 −0.75ω，行星架+桨毂+桨叶 0.05ω（15:1），
 *   行星轮按真实齿数差动自转并沿各自销轴径向散开（表：Planets +0.55u）。
 */

/** 关键尺寸（毫米）。模型、运动学与说明共用。1u = 400 mm（对照表单位）。 */
export const TP = {
  AY: 1150,
  u: 400,
  /* 轴向站位（+x 桨向前；对照表 u × 400）。 */
  tailX: -1620,          // 尾锥尖
  exhaustX0: -1380,      // 排气短管前端
  pt2X: -1340, pt1X: -1200, hpX: -1060, ngvX: -980, baffleX: -1000,
  linerX0: -1370, linerX1: -910,   // 火焰筒 −2.85u ± 0.575u
  caseX0: -1420, caseX1: 300,
  impellerX: -740,       // −1.85u
  stator3X: -604, rotor3X: -528, stator2X: -452, rotor2X: -374, stator1X: -296, rotor1X: -220,
  bearingX: -60,
  gearX0: 320, gearX1: 860, gearMidX: 580,   // +1.45u
  torqueX: 700,
  intakeX: 150,
  lockRingX: 900,
  hubX: 1060,            // +2.65u（变距桨组件原点）
  spinnerX0: 924, spinnerX1: 1532,
  /* 半径。 */
  propR: 1080,           // 桨尖半径（Ø2160）
  bladeRootR: 250,
  hubR: 250,
  caseR: 330,            // 外机匣（包住 Ø600 火焰筒外壁）
  gearboxR: 270,
  linerInR: 220, linerOutR: 300,   // 回流火焰筒（涡轮盘置于内孔）
  impellerR: 230,
  rotorTipR: [210, 195, 180] as const,
  statorOuterR: 215,
  hpR: 165, ptR: 180,
  shaftR: 62,
  /* 两级行星轮系。 */
  sunTeeth: 16, planetTeeth: 24, ringTeeth: 64, planets: 5,
  sunTeeth2: 16, planetTeeth2: 8, ringTeeth2: 32, planets2: 4,
  bladeCounts: [33, 29, 27] as const,
  statorCounts: [23, 21, 19] as const,
  wall: 18,
};

export const AY = TP.AY;
const U = TP.u;
const ux = (n: number): number => n * U;

/**
 * 31 个零件（1–31 连续编号 = 图上件号）。
 * 三波拆解窗口：W1 紧固件与外皮 0→0.35，W2 大部件 0.30→0.68，W3 内部 0.60→1.00。
 * explode 向量 = 对照表的 Δ（u）与径向扇出（1u = 400 mm）。
 */
export const PARTS: PartDef[] = [
  /* ── Wave 1 · 紧固件与外皮 ─────────────────────────────────────── */
  {
    id: 'spinner', index: 1, name: '整流罩（两片）', en: 'Spinner Dome', role: '整流 · 包住桨毂',
    material: '玻璃钢',
    description: '抛物线双层整流锥 + 后部环形背板（两片对合，4 个桨根让位缺口），顺气流抛光减阻。',
    explode: [ux(3.35), 0, 0], stage: [0, 0.22],
  },
  {
    id: 'pitch-lock-ring', index: 2, name: '变距锁紧螺栓环', en: 'Pitch-Lock Bolt Ring', role: '锁紧变距',
    material: '30CrMnSiA',
    description: '12 条 M10 高强度螺栓沿周向锁紧变距活塞，先于法兰脱出；预紧力矩 45 N·m。',
    explode: [ux(2.6), 0, 0], stage: [0.05, 0.28],
  },
  {
    id: 'cowl-upper', index: 3, name: '上短舱', en: 'Upper Nacelle Cowl', role: '整流 · 包覆',
    material: '铝合金蒙皮',
    description: '上半短舱壳体，壁厚 18 mm，沿 z=0 对称挖空，半剖后可见压气机与燃烧室外机匣。',
    explode: [0, ux(2.4), 0], stage: [0, 0.35],
  },
  {
    id: 'cowl-lower', index: 4, name: '下短舱', en: 'Lower Nacelle Cowl', role: '整流 · 进气',
    material: '铝合金蒙皮',
    description: '下半短舱壳体，带进气唇口与放水口，与上短舱在 z=0 水平面用 24 颗铆钉对接。',
    explode: [0, -ux(2.4), 0], stage: [0, 0.35],
  },
  {
    id: 'combustor-case-a', index: 5, name: '外机匣（右半）', en: 'Outer Case (Right Half)', role: '承力 · 压力壳',
    material: 'GH4169 高温合金',
    description: '压气机-扩压-燃烧室外机匣右半，内径 660 mm、壁厚 18 mm，含 12 个凸缘螺栓座。',
    explode: [0, 0, ux(1.8)], stage: [0.02, 0.35],
  },
  {
    id: 'combustor-case-b', index: 6, name: '外机匣（左半）', en: 'Outer Case (Left Half)', role: '承力 · 压力壳',
    material: 'GH4169 高温合金',
    description: '外机匣左半，与右半在上下中分面螺栓对接；内壁开 14 个喷嘴安装孔与 2 个点火器孔。',
    explode: [0, 0, -ux(1.8)], stage: [0.02, 0.35],
  },

  /* ── Wave 2 · 大部件分离 ───────────────────────────────────────── */
  {
    id: 'prop-hub', index: 7, name: '桨毂与变距缸', en: 'Prop Hub & Pitch Dome', role: '传扭 · 变距',
    material: '20CrMo 锻钢',
    description: '4 臂整体锻钢桨毂辐条（4 个桨根承力套筒）+ 液压变距缸（行程 ±25°），对照表 Δ +2.30u。',
    explode: [ux(2.3), 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'gearbox', index: 8, name: '减速齿轮箱机匣', en: 'Reduction Gearbox Housing', role: '承力 · 包住轮系',
    material: '镁合金 AZ91C',
    description: '两级行星减速箱机匣（含扭矩计筒与进气导流窗），壁厚 16 mm；半剖露出 5 个一级行星轮。',
    explode: [ux(1.35), 0, 0], stage: [0.34, 0.66],
    deep: [ux(2.4), 0, 0],
  },
  {
    id: 'exhaust', index: 9, name: '排气短管与尾锥', en: 'Exhaust Ducts & Tailcone', role: '排气 · 整流',
    material: 'Inconel 625',
    description: '双侧排气短管（内径 220 mm，上偏 15°）与尾锥整体后脱，排气温度约 700 °C。',
    explode: [-ux(2.2), 0, 0], stage: [0.3, 0.62],
  },
  {
    id: 'fuel-manifold', index: 10, name: '燃油总管与喷嘴', en: 'Fuel Manifold & Nozzles', role: '供油 · 雾化',
    material: '1Cr18Ni9Ti',
    description: '环形燃油总管 + 14 个旋流喷嘴杯 + 2 支点火电嘴，径向扇出 +0.90u（对照表 Fuel Nozzles）。',
    explode: [0, ux(0.9), 0], stage: [0.3, 0.6],
  },
  {
    id: 'accessory-drive', index: 11, name: '附件传动组', en: 'Accessory Drive Group', role: '驱动附件',
    material: '18Cr2Ni4WA',
    description: '锥齿轮副（齿数 27/27）+ 起动发电机安装座 + 高压燃油泵壳，径向 −y 拉出 1.2u。',
    explode: [0, -ux(1.2), 0], stage: [0.32, 0.62],
  },

  /* ── Wave 3 · 内部 telescoping 与径向扇出 ───────────────────────── */
  {
    id: 'blade-1', index: 12, name: '桨叶 1', en: 'Blade 1', role: '拉力 · 上',
    material: '钛合金 TC4',
    description: '变距桨叶：48°→16° 桨根到桨尖洗出扭转、42% 弦长变距轴、桨根配重夹环；径向 +1.15u。',
    explode: [0, ux(1.15), 0], stage: [0.6, 0.85],
  },
  {
    id: 'blade-2', index: 13, name: '桨叶 2', en: 'Blade 2', role: '拉力 · 下',
    material: '钛合金 TC4',
    description: '与 1 号桨叶同型、相位 180°，径向 −1.15u；桨根螺栓 6×M16 预紧 120 N·m。',
    explode: [0, -ux(1.15), 0], stage: [0.6, 0.85],
  },
  {
    id: 'blade-3', index: 14, name: '桨叶 3', en: 'Blade 3', role: '拉力 · 右',
    material: '钛合金 TC4',
    description: '相位 90°，径向 +1.15u；叶身大梁为实心钛，前缘包不锈钢防蚀条。',
    explode: [0, 0, ux(1.15)], stage: [0.62, 0.87],
  },
  {
    id: 'blade-4', index: 15, name: '桨叶 4', en: 'Blade 4', role: '拉力 · 左',
    material: '钛合金 TC4',
    description: '相位 270°，径向 −1.15u；四叶按 90° 均布，离心载荷约 68 kN/叶。',
    explode: [0, 0, -ux(1.15)], stage: [0.62, 0.87],
  },
  {
    id: 'sun-gear', index: 16, name: '太阳轮轴', en: 'Sun Gear Shaft', role: '输入 · 16 齿',
    material: '18Cr2Ni4WA 渗碳',
    description: '自由涡轮内轴前端太阳轮（16 齿、模数 5），telescoping 最内节：+x 伸 0.75u（0.35u/件）。',
    explode: [ux(0.75), 0, 0], stage: [0.6, 0.8],
  },
  {
    id: 'planet-gears', index: 17, name: '一级行星轮（5 个）', en: 'Planet Gears ×5', role: '差动 · 24 齿',
    material: '18Cr2Ni4WA 渗碳',
    description: '5 个一级行星轮（24 齿）均布销圆 Ø210；+x 伸 0.40u，并沿各自销轴径向散开 +0.55u。',
    explode: [ux(0.4), 0, 0], stage: [0.63, 0.83],
  },
  {
    id: 'planet-carrier', index: 18, name: '行星架与销轴', en: 'Planet Carrier & Pins', role: '输出 · 承载',
    material: '20CrMo 锻钢',
    description: '行星架（前/后夹板）与 5 根中空行星销（Ø42，内孔 Ø16 通滑油），+x 伸 0.05u。',
    explode: [ux(0.05), 0, 0], stage: [0.66, 0.86],
  },
  {
    id: 'ring-gear', index: 19, name: '内齿圈', en: 'Ring Gear', role: '固定 · 64 齿',
    material: '42CrMo 氮化',
    description: '一级内齿圈（64 齿）压装在机匣内壁；15:1 减速比由此齿数关系（1+64/16）×（1+32/16）得出。',
    explode: [-ux(0.3), 0, 0], stage: [0.69, 0.89],
  },
  {
    id: 'rotor-1', index: 20, name: '压气机一级转子', en: 'Compressor Rotor 1', role: '增压 · 33 叶',
    material: '钛合金 TC11',
    description: '轴流第一级：盘径 Ø420、33 片弯扭翼型叶片（安装角 32°、叶尖扭转 16°），榫槽盘缘。',
    explode: [ux(0.5), 0, 0], stage: [0.62, 0.88],
  },
  {
    id: 'rotor-2', index: 21, name: '压气机二级转子', en: 'Compressor Rotor 2', role: '增压 · 29 叶',
    material: '钛合金 TC11',
    description: '第二级盘径 Ø390、29 叶、安装角 38°；转子链每级 −0.50u 让开（对照表 0.50u/stage）。',
    explode: [0, 0, 0], stage: [0.64, 0.9],
  },
  {
    id: 'rotor-3', index: 22, name: '压气机三级转子', en: 'Compressor Rotor 3', role: '增压 · 27 叶',
    material: '钛合金 TC11',
    description: '第三级盘径 Ø360、27 叶、安装角 44°；三级后空气总压升至约 4×10⁵ Pa。',
    explode: [-ux(0.5), 0, 0], stage: [0.66, 0.92],
  },
  {
    id: 'stator-1', index: 23, name: '一级静子环', en: 'Stator Ring 1', role: '整流 · 23 叶',
    material: 'GH4169',
    description: '一级静子 23 片，把气流扭回轴向再进二级；径向扇出 +0.85u（对照表 Stators）。',
    explode: [0, ux(0.85), 0], stage: [0.63, 0.89],
  },
  {
    id: 'stator-2', index: 24, name: '二级静子环', en: 'Stator Ring 2', role: '整流 · 21 叶',
    material: 'GH4169',
    description: '二级静子 21 片、叶高 52 mm；径向 +0.85u，与转子交错排布零重叠。',
    explode: [0, ux(0.85), 0], stage: [0.65, 0.91],
  },
  {
    id: 'stator-3', index: 25, name: '三级静子环', en: 'Stator Ring 3', role: '整流 · 19 叶',
    material: 'GH4169',
    description: '三级静子 19 片，后接离心叶轮进口导叶；径向 +0.85u，环外缘 24 个径向销定位。',
    explode: [0, ux(0.85), 0], stage: [0.67, 0.93],
  },
  {
    id: 'impeller', index: 26, name: '离心叶轮与扩压管', en: 'Centrifugal Impeller & Diffuser', role: '增压 · 扩压',
    material: '钛合金 TC4',
    description: '单级离心叶轮：12 长叶 + 12 交错分流短叶、38° 后弯、子午流道抛物轮毂；+12 根径向扩压管。',
    explode: [-ux(0.9), 0, 0], stage: [0.68, 0.94],
  },
  {
    id: 'combustor-liner', index: 27, name: '火焰筒', en: 'Combustion Flame Liner', role: '燃烧 · 掺混',
    material: 'GH3044',
    description: '回流环形双层火焰筒（外径 600 mm、内径 440 mm，涡轮盘置于内孔），5 排凸缘掺混孔环。',
    explode: [-ux(1.25), 0, 0], stage: [0.7, 0.95],
  },
  {
    id: 'hp-turbine', index: 28, name: '高压涡轮级', en: 'HP Turbine Stage', role: '驱动压气机',
    material: 'DS 高温合金',
    description: '导向器环（34 片）+ 一级高压涡轮盘（29 叶）+ 级间挡板；对照表 Δ −2.55u，随涡轮链后移。',
    explode: [-ux(2.55), 0, 0], stage: [0.72, 0.96],
  },
  {
    id: 'pt-disk-1', index: 29, name: '动力涡轮一级盘', en: 'Power Turbine Disk 1', role: '输出功 · 31 叶',
    material: 'FGH96 粉末合金',
    description: '自由动力涡轮第一级（31 叶），装在同心内轴上，反转（−0.75ω）；Δ −2.85u。',
    explode: [-ux(2.85), 0, 0], stage: [0.74, 0.97],
  },
  {
    id: 'pt-disk-2', index: 30, name: '动力涡轮二级盘与内轴', en: 'Power Turbine Disk 2 & Shaft', role: '输出功 · 33 叶',
    material: 'FGH96 粉末合金',
    description: '第二级（33 叶）与 Ø124 内轴（带 2 组迷宫密封）整体，把功率送到太阳轮；Δ −3.15u。',
    explode: [-ux(3.15), 0, 0], stage: [0.76, 0.98],
  },
  {
    id: 'mount-truss', index: 31, name: '安装桁架', en: 'Mounting Truss', role: '基座 · 承力',
    material: '30CrMnSiA 焊管',
    description: '4 管空间桁架（Ø45×3），最低点 y=0，上端接齿轮箱机匣 4 个主接头。',
    explode: [0, 0, 0], stage: [1, 1],
  },
];

export const NEIGHBOURS: Record<string, string[]> = {
  'prop-hub': ['spinner', 'pitch-lock-ring', 'blade-1', 'blade-2', 'blade-3', 'blade-4', 'prop-hub'],
  spinner: ['pitch-lock-ring', 'spinner'],
  'pitch-lock-ring': ['spinner', 'pitch-lock-ring'],
  gearbox: ['ring-gear', 'planet-carrier', 'planet-gears', 'sun-gear', 'gearbox'],
  'planet-gears': ['sun-gear', 'planet-carrier', 'ring-gear', 'planet-gears'],
  'sun-gear': ['planet-gears', 'sun-gear'],
  impeller: ['stator-3', 'rotor-3', 'impeller'],
  'hp-turbine': ['pt-disk-1', 'pt-disk-2', 'hp-turbine'],
  exhaust: ['combustor-liner', 'exhaust'],
};

export const BOLT_SETS: Record<string, BoltSetDef> = {
  'pitch-bolts': { owner: 'pitch-lock-ring', distance: 220, stage: [0, 0.1] },
  'case-bolts': { owner: 'combustor-case-a', distance: 140, stage: [0.02, 0.12] },
  'gear-bolts': { owner: 'gearbox', distance: 160, stage: [0.3, 0.42] },
};

export const GUIDES: GuideDef[] = [
  { stage: 'spinner', origin: [TP.spinnerX1 - 120, TP.AY + 200, 0] },
  { stage: 'prop-hub', origin: [TP.hubX, TP.AY + 320, 0] },
  { stage: 'gearbox', origin: [TP.gearX1 - 60, TP.AY + 300, 0] },
  { stage: 'exhaust', origin: [TP.tailX + 80, TP.AY + 160, 0] },
  { stage: 'cowl-upper', origin: [-200, TP.AY + TP.caseR + 60, 0] },
  { stage: 'blade-1', origin: [TP.hubX, TP.AY + 700, 0] },
  { stage: 'combustor-liner', origin: [TP.linerX1 - 120, TP.AY + 120, 0] },
  { stage: 'sun-gear', origin: [TP.gearMidX + 60, TP.AY + 100, 0] },
];

export const CENTRE_LINES: Array<[Vec3, Vec3, number?]> = [
  [[TP.tailX - 60, TP.AY, 0], [TP.spinnerX1 + 60, TP.AY, 0], TP.impellerR],
  [[TP.gearMidX, TP.AY, 0], [TP.gearMidX, TP.AY, 0], 260],
];

export const STEPS: StepDef[] = [
  {
    title: '装配体', en: 'Assembly',
    body: '涡桨发动机全景：4 叶恒速螺旋桨在前，中段是镁合金行星减速箱，后段轴流-离心压气机、回流燃烧室与两级自由动力涡轮。运转时高压转子 1.0ω 正转，自由涡轮反向 0.75ω，桨毂经 15:1 行星减速只转 0.05ω。',
    state: { explode: 0, section: false, running: true, select: 'prop-hub', focus: null },
  },
  {
    title: '半剖', en: 'Half Section',
    body: '沿 z=0 剖开短舱、齿轮箱机匣、扩压机匣与火焰筒：前段 5 个一级行星轮绕太阳轮公转，中段三级轴流转子与静子交错，后段双层火焰筒包着高压涡轮与两级反转动力涡轮，迷宫密封沿内轴布置。',
    state: { explode: 0, section: true, running: true, select: 'planet-gears', focus: null },
  },
  {
    title: '传动链', en: 'Power Train',
    body: '两级行星轮系：一级 16/24/64 齿（5:1）、二级 16/8/32 齿（3:1），合计 15:1。太阳轮随自由涡轮轴反转，5 个行星轮绕销轴自转并带动行星架，桨毂与 4 叶以 0.05ω 慢转。',
    state: { explode: 0, section: false, running: true, select: 'sun-gear', focus: 'gearbox' },
  },
  {
    title: '三波拆解', en: '3-Wave Explode',
    body: '第 1 波：整流罩 +3.35u、锁紧环先脱，上下短舱 ±2.4u、左右外机匣 ±1.8u 分开。第 2 波：桨毂 +2.30u、齿轮箱 +1.35u、排气组 −2.20u，供油与附件径向拉出。第 3 波：桨叶径向 +1.15u，行星轮系沿 +x 伸缩 0.35u/件并径向 +0.55u，转子链每级 −0.50u、静子环径向 +0.85u，涡轮链 Δ −2.55..−3.15u，全部叶排零重叠。',
    state: { explode: 1, section: false, running: false, select: null, focus: null },
  },
];

export const CAMERA: CameraDef = {
  target: [-40, TP.AY, 0],
  offset: [4300, 1800, 5300],
  orthoDistance: 10000,
  exploded: { target: [-160, TP.AY, 0], scale: 1.55 },
  foci: {
    gearbox: { target: [TP.gearMidX, TP.AY, 0], scale: 0.42 },
    combustor: { target: [-1140, TP.AY, 0], scale: 0.5 },
  },
};

/** 三视图尺寸链（Sheet）：总长 + 分段链 + 转子直径。 */
export const DIMENSIONS = [
  { from: [TP.tailX, 0, 0] as Vec3, to: [TP.spinnerX1, 0, 0] as Vec3, view: 'front' as const, label: '3152', offset: 116 },
  { from: [TP.gearX0, 0, 0] as Vec3, to: [TP.gearX1, 0, 0] as Vec3, view: 'front' as const, label: '540', offset: 34 },
  { from: [TP.caseX0, 0, 0] as Vec3, to: [TP.gearX0, 0, 0] as Vec3, view: 'front' as const, label: '1740', offset: 66 },
  { from: [TP.tailX, 0, 0] as Vec3, to: [TP.caseX0, 0, 0] as Vec3, view: 'front' as const, label: '200', offset: 34 },
  { from: [TP.gearX1, 0, 0] as Vec3, to: [TP.spinnerX1, 0, 0] as Vec3, view: 'front' as const, label: '672', offset: 34 },
  {
    from: [TP.rotor1X, TP.AY - TP.rotorTipR[0], 0] as Vec3,
    to: [TP.rotor1X, TP.AY + TP.rotorTipR[0], 0] as Vec3,
    view: 'left' as const, label: 'Ø420', offset: 64,
  },
];

/** 图面 BOM 气泡（主视图投影引线）。 */
export const BOM = [
  { id: 'spinner', p: [TP.spinnerX1 - 160, TP.AY + 210, 0] as Vec3 },
  { id: 'prop-hub', p: [TP.hubX + 40, TP.AY + 330, 0] as Vec3 },
  { id: 'gearbox', p: [TP.gearX0 + 180, TP.AY + 320, 0] as Vec3 },
  { id: 'sun-gear', p: [TP.gearMidX + 40, TP.AY + 120, 0] as Vec3 },
  { id: 'planet-gears', p: [TP.gearMidX - 120, TP.AY + 190, 0] as Vec3 },
  { id: 'rotor-1', p: [TP.rotor1X, TP.AY + 250, 0] as Vec3 },
  { id: 'stator-2', p: [TP.stator2X, TP.AY + 250, 0] as Vec3 },
  { id: 'impeller', p: [TP.impellerX, TP.AY + 270, 0] as Vec3 },
  { id: 'combustor-liner', p: [TP.linerX1 - 200, TP.AY + 330, 0] as Vec3 },
  { id: 'hp-turbine', p: [TP.hpX, TP.AY + 220, 0] as Vec3 },
  { id: 'pt-disk-2', p: [TP.pt2X, TP.AY + 230, 0] as Vec3 },
  { id: 'exhaust', p: [TP.exhaustX0 - 120, TP.AY + 190, 0] as Vec3 },
  { id: 'mount-truss', p: [580, 140, 0] as Vec3 },
];
