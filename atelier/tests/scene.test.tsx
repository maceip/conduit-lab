import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import {
  GcHeapScene,
  PrattParserScene,
  TriColorGcScene,
  type GcHeapEdge,
  type GcHeapObject,
} from '../src/viz/stage';
import { SceneSheet } from '../src/gallery/SceneSheet';

const OBJECTS: GcHeapObject[] = [
  { id: 'root', position: [0, 0, 0], color: 'black' },
  { id: 'grey-a', position: [-2.6, 0.4, 0], color: 'grey' },
  { id: 'white-a', position: [-3.6, -1.8, 0], color: 'white' },
];

const CLEAN_EDGES: GcHeapEdge[] = [
  { from: 'root', to: 'grey-a' },
  { from: 'grey-a', to: 'white-a' },
];

const VIOLATION_EDGES: GcHeapEdge[] = [...CLEAN_EDGES, { from: 'grey-a', to: 'root' }];

describe('the tier-3 scenes', () => {
  it('exposes the step index and the step count', () => {
    for (const [name, Scene] of [
      ['pratt', PrattParserScene],
      ['tricolor', TriColorGcScene],
    ] as const) {
      const html = renderToStaticMarkup(<Scene title={name} />);
      expect(html, name).toContain('data-step-index');
      expect(html, name).toContain('data-step-count');
    }
  });

  it('starts on a real step', () => {
    const html = renderToStaticMarkup(<PrattParserScene title="pratt" />);
    expect(html).toMatch(/data-step-index="0"/);
    expect(html).toMatch(/data-step-count="[1-9]/);
  });

  it('names the spec clause of the step being shown', () => {
    const html = renderToStaticMarkup(<TriColorGcScene title="gc" />);
    expect(html).toContain('data-testid="stepper-clause"');
  });
});

describe('the tier-2 scene', () => {
  it('renders a canvas host without touching WebGL during render', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={OBJECTS} edges={CLEAN_EDGES} title="heap" />,
    );
    expect(html).toContain('<canvas');
    expect(html).toContain('data-testid="gc-heap-scene"');
    expect(html).toContain('role="group"');
  });

  it('reports a heap that respects the barrier', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={OBJECTS} edges={CLEAN_EDGES} title="heap" />,
    );
    expect(html).toContain('data-violation="false"');
    expect(html).toContain('BARRIER HELD');
  });

  it('reports a heap that breaks the barrier', () => {
    const html = renderToStaticMarkup(
      <GcHeapScene objects={OBJECTS} edges={VIOLATION_EDGES} title="heap" />,
    );
    expect(html).toContain('data-violation="true"');
    expect(html).toContain('BARRIER VIOLATION');
  });
});

describe('the scene sheet', () => {
  const html = renderToStaticMarkup(<SceneSheet />);

  it('renders on the sheet', () => {
    expect(html).toContain('data-testid="scene-sheet"');
    expect(html).toContain('data-testid="scene-gc-heap"');
    expect(html).toContain('data-testid="scene-gc-heap-violation"');
    expect(html).toContain('data-testid="scene-pratt-parser"');
    expect(html).toContain('data-testid="scene-tri-color-gc"');
  });

  it('mounts both step-through scenes with their step metadata', () => {
    expect(html).toContain('data-step-index');
    expect(html).toContain('data-step-count');
  });

  it('shows the heap on both sides of the barrier', () => {
    expect(html).toContain('data-violation="false"');
    expect(html).toContain('data-violation="true"');
  });
});
