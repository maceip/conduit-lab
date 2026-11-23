import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { CUT_FACE, SHADE_DARK, SHADE_HI } from '../../contract/tokens';
import { IsolateIcon } from './IsolateIcon';
import { RatchetIcon } from './RatchetIcon';
import { ISOLATE_ASSEMBLY } from './IsolateIcon';
import { RATCHET_ASSEMBLY } from './RatchetIcon';
import { POINTER_TAGGING_ASSEMBLY } from './PointerTaggingIcon';
import { HIDDEN_CLASSES_ASSEMBLY } from './HiddenClassesIcon';
import { PARSER_ASSEMBLY } from './ParserIcon';
import { IGNITION_ASSEMBLY } from './IgnitionIcon';
import { OLD_SPACE_ASSEMBLY } from './OldSpaceIcon';
import { NEW_SPACE_ASSEMBLY } from './NewSpaceIcon';

const idsIn = (html: string) =>
  [...html.matchAll(/id="([^"]+)"/g)].map((m) => m[1] ?? '');

describe('icons', () => {
  it('renders an inline svg element', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={48} />);
    expect(html).toContain('<svg');
    expect(html).toContain('viewBox');
  });

  it('honours the size prop', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={64} />);
    expect(html).toMatch(/width="64"/);
  });

  it('namespaces defs ids across sibling instances', () => {
    const html = renderToStaticMarkup(
      <>
        <IsolateIcon />
        <IsolateIcon />
      </>,
    );
    const ids = idsIn(html);
    expect(ids.length).toBeGreaterThan(0);
    expect(new Set(ids).size).toBe(ids.length);
  });

  it('omits balloons when annotated is false', () => {
    const on = renderToStaticMarkup(<IsolateIcon annotated />);
    const off = renderToStaticMarkup(<IsolateIcon annotated={false} />);
    expect(on.length).toBeGreaterThan(off.length);
  });

  it('renders an accessible title when provided', () => {
    const html = renderToStaticMarkup(<RatchetIcon title="The ratchet" />);
    expect(html).toContain('<title');
    expect(html).toContain('The ratchet');
  });
});

describe('icon assemblies', () => {
  const assemblies = [
    ISOLATE_ASSEMBLY,
    POINTER_TAGGING_ASSEMBLY,
    HIDDEN_CLASSES_ASSEMBLY,
    PARSER_ASSEMBLY,
    IGNITION_ASSEMBLY,
    OLD_SPACE_ASSEMBLY,
    NEW_SPACE_ASSEMBLY,
    RATCHET_ASSEMBLY,
  ];

  it('covers all eight icons', () => {
    expect(assemblies).toHaveLength(8);
  });

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'draws %s with five to eight parts',
    (_id, assembly) => {
      expect(assembly.parts.length).toBeGreaterThanOrEqual(5);
      expect(assembly.parts.length).toBeLessThanOrEqual(8);
    },
  );

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'draws %s with at least one sectioned part',
    (_id, assembly) => {
      expect(assembly.parts.some((p) => p.sectioned)).toBe(true);
    },
  );

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'numbers the balloons of %s 1..n in assembly order',
    (_id, assembly) => {
      const balloons = assembly.parts
        .filter((p) => typeof p.balloon === 'number')
        .map((p) => p.balloon);
      expect(balloons.length).toBeGreaterThan(0);
      expect(balloons).toEqual(balloons.map((_, i) => i + 1));
    },
  );

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'explodes %s along its assembly axis',
    (_id, assembly) => {
      const offsets = assembly.parts.map((p) => {
        const e = p.explode ?? [0, 0, 0];
        return [e[0] ?? 0, e[1] ?? 0, e[2] ?? 0] as const;
      });
      const ax = assembly.axis[0] ?? 0;
      const ay = assembly.axis[1] ?? 0;
      const az = assembly.axis[2] ?? 0;
      for (const offset of offsets) {
        // every explode offset is parallel to the shared axis
        const cross = ay * offset[2] - az * offset[1];
        const cross2 = az * offset[0] - ax * offset[2];
        const cross3 = ax * offset[1] - ay * offset[0];
        expect(Math.hypot(cross, cross2, cross3)).toBeLessThan(1e-9);
      }
    },
  );
});

describe('icon tonal range', () => {
  const assemblies = [
    ISOLATE_ASSEMBLY,
    POINTER_TAGGING_ASSEMBLY,
    HIDDEN_CLASSES_ASSEMBLY,
    PARSER_ASSEMBLY,
    IGNITION_ASSEMBLY,
    OLD_SPACE_ASSEMBLY,
    NEW_SPACE_ASSEMBLY,
    RATCHET_ASSEMBLY,
  ];

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'gives every part of %s an explicit palette',
    (_id, assembly) => {
      for (const part of assembly.parts) {
        expect(part.palette).toBeDefined();
      }
    },
  );

  it.each(assemblies.map((a) => [a.parts[0]?.id ?? '?', a] as const))(
    'gives %s a bright element and dark structure',
    (_id, assembly) => {
      const palettes = assembly.parts.map((p) => p.palette);
      expect(palettes.filter((p) => p === 'hi').length).toBeGreaterThanOrEqual(1);
      expect(palettes.filter((p) => p === 'hi').length).toBeLessThanOrEqual(2);
      expect(palettes.filter((p) => p === 'dark').length).toBeGreaterThanOrEqual(2);
      expect(palettes.filter((p) => p === 'dark').length).toBeLessThanOrEqual(4);
      expect(palettes.filter((p) => p === 'body').length).toBeGreaterThanOrEqual(1);
    },
  );

  it('fills faces from the published palette ramps', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={48} />);
    // the bright 'hi' ramp, the dark ramp, and the bright machined cut face
    expect(html).toContain(SHADE_HI[3]);
    expect(html).toContain(SHADE_DARK[0]);
    expect(html).toContain(CUT_FACE);
  });

  it('draws a cut face bright with the section hatch over it', () => {
    const html = renderToStaticMarkup(<IsolateIcon size={48} />);
    expect(html).toContain('url(#');
    expect(html).toContain(CUT_FACE);
  });
});
