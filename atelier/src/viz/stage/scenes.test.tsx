import { describe, expect, it } from 'vitest';
import { createElement as h } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { BOARD } from '../../contract/tokens';
import { PRATT_PARSER_STEPS, PrattParserScene } from './PrattParserScene';
import { TRICOLOR_GC_STEPS, TriColorGcScene } from './TriColorGcScene';

/**
 * The width of a mono label, in viewBox units. JetBrains Mono advances
 * 0.6em per glyph and the register adds 0.08em of tracking, so a label of
 * `n` characters at `size` pixels is `n * 0.68 * size` wide.
 */
function labelWidth(text: string, size: number): number {
  return text.length * 0.68 * size;
}

/**
 * Every `<text>` label of a rendered diagram, with the box it occupies.
 * A label that leaves the 720-wide frame is a drafting fault: the caption
 * is the only thing the reader can fall back on.
 */
function overflowingLabels(markup: string): string[] {
  const document = new DOMParser().parseFromString(markup, 'image/svg+xml');
  const problems: string[] = [];
  for (const text of Array.from(document.querySelectorAll('text'))) {
    const x = Number(text.getAttribute('x') ?? '0');
    const anchor = text.getAttribute('text-anchor') ?? 'start';
    const style = text.getAttribute('style') ?? '';
    const size = /font-size:\s*([\d.]+)px/.exec(style);
    const fontSize = size === null ? 9 : Number(size[1]);
    const content = text.textContent ?? '';
    const width = labelWidth(content, fontSize);
    const left = anchor === 'middle' ? x - width / 2 : anchor === 'end' ? x - width : x;
    const right = left + width;
    if (left < 0 || right > 720) {
      problems.push(`"${content.slice(0, 60)}" occupies [${left.toFixed(0)}, ${right.toFixed(0)}]`);
    }
  }
  return problems;
}

/**
 * The two Tier 3 scenes are the part of the stage that Proof's gallery will
 * mount, so they are rendered here for real: an unhandled throw inside a
 * scene would otherwise only show up in the browser.
 */
describe('PrattParserScene', () => {
  const html = renderToStaticMarkup(<PrattParserScene />);

  it('renders a stepper over the real parser pipeline', () => {
    expect(html).toContain('data-testid="pratt-parser-scene"');
    expect(html).toContain('data-step-index="0"');
    expect(html).toContain('data-step-count="5"');
  });

  it('renders the diagram as SVG, not WebGL', () => {
    expect(html).toContain('<svg');
    expect(html).toContain('role="img"');
    expect(html).not.toContain('<canvas');
  });

  it('gives every step a caption and a clause', () => {
    for (const step of PRATT_PARSER_STEPS) {
      expect(step.caption.length).toBeGreaterThan(0);
      expect(step.clause).toBeDefined();
      expect(step.clause?.length).toBeGreaterThan(0);
    }
  });

  it('names only clauses that appear in the vjs_syntax crate', () => {
    const clauses = PRATT_PARSER_STEPS.map((step) => step.clause ?? '');
    // ECMA-262 sections quoted by browser/vjs-syntax/src.
    for (const clause of clauses) {
      expect(clause).toMatch(/ECMA-262 §|vjs_syntax/);
    }
    expect(clauses.some((clause) => clause.includes('§12 (Lexical Grammar)'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('§13.13'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('match_binary_op'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('parse_binary_expr'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('UnparenthesizedNullishAndLogicalMix'))).toBe(
      true,
    );
  });

  it('renders the real token kinds and binding powers from the crate', () => {
    // Render every step at full draw and read the markup back.
    const markup = PRATT_PARSER_STEPS.map((step) =>
      renderToStaticMarkup(<>{step.render(1)}</>),
    ).join('');
    expect(markup).toContain('TokenKind::Ident');
    expect(markup).toContain('Punctuator::PipePipe');
    expect(markup).toContain('Punctuator::AmpAmp');
    expect(markup).toContain('BinOp::LogicalOr');
    expect(markup).toContain('BinOp::LogicalAnd');
    expect(markup).toContain('ExprKind::Binary');
  });
});

describe('TriColorGcScene', () => {
  const html = renderToStaticMarkup(<TriColorGcScene />);

  it('renders a stepper over the real mark-sweep phases', () => {
    expect(html).toContain('data-testid="tri-color-gc-scene"');
    expect(html).toContain('data-step-index="0"');
    expect(html).toContain('data-step-count="8"');
  });

  it('renders the diagram as SVG, not WebGL', () => {
    expect(html).toContain('<svg');
    expect(html).toContain('role="img"');
    expect(html).not.toContain('<canvas');
  });

  it('gives every step a caption and a clause', () => {
    for (const step of TRICOLOR_GC_STEPS) {
      expect(step.caption.length).toBeGreaterThan(0);
      expect(step.clause).toBeDefined();
      expect(step.clause?.length).toBeGreaterThan(0);
    }
  });

  it('names the real crate and the real tricolor invariant', () => {
    const clauses = TRICOLOR_GC_STEPS.map((step) => step.clause ?? '');
    for (const clause of clauses) {
      expect(clause).toContain('vjs_gc J6');
    }
    expect(clauses.some((clause) => clause.includes('Dijkstra'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('no Black-to-White edge'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('roots_valid'))).toBe(true);
    expect(clauses.some((clause) => clause.includes('Phase 3'))).toBe(true);
  });

  it('renders the real arena slots and the violation edge', () => {
    const markup = TRICOLOR_GC_STEPS.map((step) =>
      renderToStaticMarkup(<>{step.render(1)}</>),
    ).join('');
    expect(markup).toContain('global');
    expect(markup).toContain('closure');
    expect(markup).toContain('orphan');
    // The tricolor step draws the grey-to-black pointer in the fail tone.
    expect(markup).toContain(BOARD.fail);
  });
});

describe('diagram framing', () => {
  it('keeps every label of every step inside the 720-wide frame', () => {
    const problems = [...PRATT_PARSER_STEPS, ...TRICOLOR_GC_STEPS].flatMap((step) =>
      overflowingLabels(renderToStaticMarkup(h('div', null, step.render(1)))),
    );
    expect(problems).toEqual([]);
  });
});
