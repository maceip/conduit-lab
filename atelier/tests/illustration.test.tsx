import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import type { ComponentType } from 'react';
import type { IconProps } from '../src/contract';
import {
  HiddenClassesIcon,
  IgnitionIcon,
  IsolateIcon,
  NewSpaceIcon,
  OldSpaceIcon,
  ParserIcon,
  PointerTaggingIcon,
  RatchetIcon,
} from '../src/illustration/icons';
import { KernelRendererPlate, V8CorePlate } from '../src/illustration/plates';
import { IconSheet } from '../src/gallery/IconSheet';
import { PlateSheet } from '../src/gallery/PlateSheet';

const ICONS: ReadonlyArray<readonly [string, ComponentType<IconProps>]> = [
  ['isolate', IsolateIcon],
  ['pointer-tagging', PointerTaggingIcon],
  ['hidden-classes', HiddenClassesIcon],
  ['parser', ParserIcon],
  ['ignition', IgnitionIcon],
  ['old-space', OldSpaceIcon],
  ['new-space', NewSpaceIcon],
  ['ratchet', RatchetIcon],
];

const idsIn = (html: string): string[] =>
  [...html.matchAll(/id="([^"]+)"/g)].map((match) => match[1] ?? '');

describe('the eight icons', () => {
  it('renders every icon as inline SVG', () => {
    expect(ICONS).toHaveLength(8);
    for (const [slug, Icon] of ICONS) {
      const html = renderToStaticMarkup(<Icon />);
      expect(html, slug).toContain('<svg');
      expect(html, slug).toContain('viewBox');
    }
  });

  it('gives every icon an accessible name', () => {
    for (const [slug, Icon] of ICONS) {
      const html = renderToStaticMarkup(<Icon title={`${slug} icon`} />);
      expect(html, slug).toContain('role="img"');
      expect(html, slug).toContain(`aria-label="${slug} icon"`);
    }
  });

  it('marks an untitled icon decorative instead of naming it', () => {
    const html = renderToStaticMarkup(<IsolateIcon />);
    expect(html).toContain('aria-hidden="true"');
  });

  it('namespaces defs ids across sibling instances', () => {
    const html = renderToStaticMarkup(
      <>
        <IsolateIcon title="first" />
        <IsolateIcon title="second" />
      </>,
    );
    const ids = idsIn(html);
    expect(ids.length).toBeGreaterThan(0);
    expect(new Set(ids).size).toBe(ids.length);
  });

  it('draws balloons only when annotated', () => {
    const on = renderToStaticMarkup(<IsolateIcon annotated />);
    const off = renderToStaticMarkup(<IsolateIcon annotated={false} />);
    expect(on.length).toBeGreaterThan(off.length);
  });
});

describe('the two plates', () => {
  it('renders both plates as inline SVG', () => {
    for (const [name, Plate] of [
      ['V8CorePlate', V8CorePlate],
      ['KernelRendererPlate', KernelRendererPlate],
    ] as const) {
      const html = renderToStaticMarkup(<Plate title={name} />);
      expect(html, name).toContain('<svg');
      expect(html, name).toContain('aria-label');
    }
  });

  it('hatches the cut faces of the strategy plate', () => {
    const html = renderToStaticMarkup(<KernelRendererPlate title="kernel" />);
    expect(html).toContain('url(#');
  });
});

describe('the icon sheet', () => {
  const html = renderToStaticMarkup(<IconSheet />);

  it('renders every icon on the sheet', () => {
    expect(html).toContain('data-testid="icon-sheet"');
    for (const [slug] of ICONS) {
      expect(html, slug).toContain(`data-testid="icon-${slug}"`);
    }
  });

  it('shows each machinery annotated and small', () => {
    // Every card carries the large reading and the inline reading.
    expect(html.match(/atelier__icon-large/g)?.length).toBe(ICONS.length);
    expect(html.match(/atelier__icon-small/g)?.length).toBe(ICONS.length);
  });

  it('gives every icon on the sheet an accessible name', () => {
    expect(html).not.toContain('aria-hidden="true"');
  });
});

describe('the plate sheet', () => {
  const html = renderToStaticMarkup(<PlateSheet />);

  it('renders both plates', () => {
    expect(html).toContain('data-testid="plate-sheet"');
    expect(html).toContain('data-testid="plate-v8-core"');
    expect(html).toContain('data-testid="plate-kernel-renderer"');
  });
});
