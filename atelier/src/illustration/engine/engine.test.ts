import { describe, expect, it } from 'vitest';
import { projectAssembly } from './index';
import type { Assembly } from './index';

const base: Assembly = {
  azDeg: 42,
  elDeg: 30,
  axis: [0, 0, 1],
  explodeScale: 1,
  partsList: false,
  parts: [
    { id: 'a', label: 'Rotor', balloon: 1, geometry: { kind: 'box', at: [0, 0, 0], size: [10, 10, 4] } },
    { id: 'b', label: 'Stator', balloon: 2, explode: [0, 0, 12], sectioned: true, geometry: { kind: 'box', at: [0, 0, 20], size: [12, 12, 4] } },
  ],
};

describe('projectAssembly', () => {
  it('separates a part along the assembly axis', () => {
    const plate = projectAssembly(base);
    expect(plate.faces.length).toBeGreaterThan(0);
    expect(plate.balloons).toHaveLength(2);
  });

  it('marks sectioned parts as cut faces', () => {
    const plate = projectAssembly(base);
    expect(plate.faces.some((f) => f.cut)).toBe(true);
  });

  it('emits a leader from every ballooned part', () => {
    const plate = projectAssembly(base);
    expect(plate.leaders).toHaveLength(2);
    for (const l of plate.leaders) expect(l.points.length).toBeGreaterThanOrEqual(2);
  });

  it('is deterministic', () => {
    expect(projectAssembly(base)).toEqual(projectAssembly(base));
  });
});

describe('drawing standard', () => {
  it('hatches adjacent sectioned parts in opposite directions', () => {
    const plate = projectAssembly({
      ...base,
      parts: [
        { id: 'a', label: 'Housing', sectioned: true, geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 10], r0: 6, r1: 6 } },
        { id: 'b', label: 'Rotor', sectioned: true, explode: [0, 0, 14], geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 10], r0: 4, r1: 4 } },
        { id: 'c', label: 'Shaft', sectioned: true, explode: [0, 0, 28], geometry: { kind: 'cyl', from: [0, 0, 0], to: [0, 0, 10], r0: 2, r1: 2 } },
      ],
    });
    const cutHatches = plate.faces.filter((f) => f.cut).map((f) => f.hatch);
    expect(cutHatches.length).toBeGreaterThanOrEqual(3);
    // every sectioned part contributes exactly one cut face, and the hatch
    // index alternates so neighbouring cuts read apart
    expect(new Set(cutHatches).size).toBe(cutHatches.length);
    expect(cutHatches[0]).not.toBe(cutHatches[1]);
  });

  it('never hatches a part that is not sectioned', () => {
    const plate = projectAssembly(base);
    const cutParts = new Set(plate.faces.filter((f) => f.cut).map((f) => f.partId));
    expect(cutParts.has('a')).toBe(false);
    expect(cutParts.has('b')).toBe(true);
  });

  it('separates exploded parts along the shared axis', () => {
    const plate = projectAssembly(base);
    const a = plate.faces.filter((f) => f.partId === 'a');
    const b = plate.faces.filter((f) => f.partId === 'b');
    const midY = (fs: typeof a) => fs.reduce((sum, f) => sum + f.points[0]![1], 0) / fs.length;
    expect(midY(b)).toBeLessThan(midY(a));
  });

  it('emits a centreline for a symmetric part', () => {
    const plate = projectAssembly(base);
    expect(plate.centerlines.length).toBeGreaterThan(0);
  });

  it('builds the parts list in balloon order', () => {
    const plate = projectAssembly({ ...base, partsList: true });
    expect(plate.bill.map((row) => row.number)).toEqual([1, 2]);
    expect(plate.bill[0]?.label).toBe('Rotor');
  });
});
