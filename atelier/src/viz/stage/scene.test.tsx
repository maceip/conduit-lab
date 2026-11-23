import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { GcHeapScene } from './GcHeapScene';
import { findTriColorViolations } from './triColor';

describe('GcHeapScene', () => {
  it('renders a canvas host element', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={[{ id: 'a', position: [0, 0, 0], color: 'white' }]} edges={[]} />,
    );
    expect(html).toContain('canvas');
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
