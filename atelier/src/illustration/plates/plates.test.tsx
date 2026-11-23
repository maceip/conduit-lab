import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { V8CorePlate, V8_CORE_ASSEMBLY } from './V8CorePlate';
import { KernelRendererPlate, KERNEL_RENDERER_ASSEMBLY } from './KernelRendererPlate';

describe('plates', () => {
  it('renders the V8 core plate with a parts list', () => {
    const html = renderToStaticMarkup(<V8CorePlate />);
    expect(html).toContain('<svg');
    expect(html.toLowerCase()).toContain('parts');
  });

  it('hatches design-only components on the strategy plate', () => {
    const html = renderToStaticMarkup(<KernelRendererPlate />);
    expect(html).toContain('url(#');
  });
});

describe('the hatched-versus-clean distinction', () => {
  it('marks only the design-only components as sectioned', () => {
    const designOnly = ['kernel-theorems', 'nanvix-isolation', 'html-css-layout'];
    const proved = ['kernel-core', 'ratchet', 'proof-link', 'site-renderer'];
    const sectioned = new Set(
      KERNEL_RENDERER_ASSEMBLY.parts.filter((p) => p.sectioned).map((p) => p.id),
    );
    for (const id of designOnly) expect(sectioned.has(id)).toBe(true);
    for (const id of proved) expect(sectioned.has(id)).toBe(false);
  });

  it('states the meaning of the hatching on the plate', () => {
    const html = renderToStaticMarkup(<KernelRendererPlate />);
    expect(html.toUpperCase()).toContain('DESIGN ONLY');
    expect(html.toUpperCase()).toContain('PROVED');
  });

  it('draws the V8 core plate as one continuous assembly', () => {
    expect(V8_CORE_ASSEMBLY.parts.length).toBeGreaterThanOrEqual(12);
    expect(V8_CORE_ASSEMBLY.parts.length).toBeLessThanOrEqual(16);
    expect(V8_CORE_ASSEMBLY.partsList).toBe(true);
    // every part explodes along the same shared axis
    const axis = V8_CORE_ASSEMBLY.axis;
    expect(axis[0]).toBe(0);
    expect(axis[1]).toBe(0);
    expect(axis[2]).toBe(1);
  });
});
