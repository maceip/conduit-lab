import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { GcHeapScene } from './GcHeapScene';
import { findTriColorViolations } from './triColor';

/**
 * The inline style declarations of one element of a rendered scene.
 *
 * The declarations are read from the serialised attribute rather than from
 * the CSSOM, because jsdom's CSSOM drops properties it does not model — and
 * because what the component ships is the attribute itself.
 */
function styleOf(html: string, className: string): Record<string, string> {
  const document = new DOMParser().parseFromString(html, 'text/html');
  const element = document.querySelector(`.${className}`);
  if (element === null) throw new Error(`no element with class ${className}`);
  const declarations: Record<string, string> = {};
  for (const declaration of (element.getAttribute('style') ?? '').split(';')) {
    const separator = declaration.indexOf(':');
    if (separator === -1) continue;
    declarations[declaration.slice(0, separator).trim()] = declaration
      .slice(separator + 1)
      .trim();
  }
  return declarations;
}

describe('GcHeapScene', () => {
  it('renders a canvas host element', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]} edges={[]} />,
    );
    expect(html).toContain('canvas');
  });

  it('lays out its own label layer, so it needs no stylesheet to read', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]} edges={[]} />,
    );
    const layer = styleOf(html, 'stage-gc-heap-labels');
    expect(layer.position).toBe('absolute');
    expect(layer.inset).toBe('0');
    expect(layer.overflow).toBe('hidden');
    expect(layer['pointer-events']).toBe('none');
  });

  it('makes the viewport the positioning context of the label layer', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]} edges={[]} />,
    );
    expect(styleOf(html, 'stage-gc-heap-viewport').position).toBe('relative');
  });

  it('marks a tri-color violation', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene
        objects={[
          { id: 'a', position: [0, 0, 0], color: 'grey' },
          { id: 'b', position: [1, 0, 0], color: 'black' },
        ]}
        edges={[{ from: 'a', to: 'b' }]}
        violation={{ from: 'a', to: 'b' }}
      />,
    );
    expect(html).toContain('data-violation="true"');
  });

  it('reports no violation for a heap that respects the barrier', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene
        objects={[
          { id: 'a', position: [0, 0, 0], color: 'grey' },
          { id: 'b', position: [1, 0, 0], color: 'grey' },
        ]}
        edges={[{ from: 'a', to: 'b' }]}
      />,
    );
    expect(html).toContain('data-violation="false"');
  });

  it('detects a grey object holding a black pointer without an explicit violation', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene
        objects={[
          { id: 'a', position: [0, 0, 0], color: 'grey' },
          { id: 'b', position: [1, 0, 0], color: 'black' },
        ]}
        edges={[{ from: 'a', to: 'b' }]}
      />,
    );
    expect(html).toContain('data-violation="true"');
    expect(html).toContain('data-violation-from="a"');
    expect(html).toContain('data-violation-to="b"');
  });

  it('renders without touching the DOM (SSR safe)', () => {
    // `renderToStaticMarkup` never runs effects, so no WebGL context is created.
    const html = renderToStaticMarkup(
      <GcHeapScene
        objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]}
        edges={[]}
      />,
    );
    expect(html).toContain('data-testid="gc-heap-scene"');
    expect(html).toContain('data-violation="false"');
  });
});

describe('findTriColorViolations', () => {
  it('finds a grey object that points at a black object', () => {
    const found = findTriColorViolations(
      [
        { id: 'a', position: [0, 0, 0], color: 'grey' },
        { id: 'b', position: [1, 0, 0], color: 'black' },
      ],
      [{ from: 'a', to: 'b' }],
    );
    expect(found).toHaveLength(1);
    expect(found[0]?.from).toBe('a');
    expect(found[0]?.to).toBe('b');
  });

  it('allows a black object to point at a black object', () => {
    const found = findTriColorViolations(
      [
        { id: 'a', position: [0, 0, 0], color: 'black' },
        { id: 'b', position: [1, 0, 0], color: 'black' },
      ],
      [{ from: 'a', to: 'b' }],
    );
    expect(found).toHaveLength(0);
  });

  it('ignores edges that reference unknown objects', () => {
    const found = findTriColorViolations(
      [{ id: 'a', position: [0, 0, 0], color: 'grey' }],
      [{ from: 'a', to: 'ghost' }],
    );
    expect(found).toHaveLength(0);
  });
});
