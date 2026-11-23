import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { CountFigure } from './CountFigure';
import { DeltaChip } from './DeltaChip';
import { OdometerReels } from './OdometerReels';
import { RadialGauge } from './RadialGauge';
import { SplitBar } from './SplitBar';
import { StatTile } from './StatTile';

/** The visible text of a rendered tree, with markup and comments removed. */
const textOf = (html: string) => html.replace(/<!--[\s\S]*?-->/g, '').replace(/<[^>]*>/g, '');

describe('DeltaChip', () => {
  it('renders a negative delta with its sign and unit', () => {
    const html = renderToStaticMarkup(<DeltaChip delta={-44} unit="%" />);
    expect(textOf(html)).toBe('-44%');
  });

  it('renders a positive delta with an explicit plus', () => {
    const html = renderToStaticMarkup(<DeltaChip delta={12} />);
    expect(textOf(html)).toBe('+12');
  });

  it('renders zero with no sign', () => {
    const html = renderToStaticMarkup(<DeltaChip delta={0} />);
    expect(textOf(html)).toBe('0');
    expect(textOf(html)).not.toContain('+');
    expect(textOf(html)).not.toContain('-');
  });

  it('groups thousands', () => {
    expect(textOf(renderToStaticMarkup(<DeltaChip delta={12480} />))).toBe('+12,480');
  });

  it('lets the caller state the verdict instead of inferring it from the sign', () => {
    // A falling verification time is good news and must not read as a failure.
    const good = renderToStaticMarkup(<DeltaChip delta={-44} unit="%" tone="proved" />);
    expect(good).toContain('data-tone="proved"');
    expect(good).not.toContain('data-tone="fail"');

    // A rising trusted-item count is a failure even though the sign is positive.
    const bad = renderToStaticMarkup(<DeltaChip delta={12} tone="fail" />);
    expect(bad).toContain('data-tone="fail"');
  });
});

describe('RadialGauge', () => {
  it('renders an svg gauge', () => {
    const html = renderToStaticMarkup(<RadialGauge value={38} max={100} />);
    expect(html).toContain('<svg');
    expect(textOf(html)).toContain('38');
  });

  it('never emits NaN or Infinity for a non-positive maximum', () => {
    const html = renderToStaticMarkup(<RadialGauge value={38} max={0} />);
    expect(html).not.toContain('NaN');
    expect(html).not.toContain('Infinity');
  });

  it('clamps a value above the maximum to a full sweep', () => {
    const html = renderToStaticMarkup(<RadialGauge value={150} max={100} />);
    expect(html).toContain('data-ratio="1.0000"');
  });

  it('exposes the value to assistive technology, not the arc geometry', () => {
    const html = renderToStaticMarkup(<RadialGauge value={38} max={100} label="Pass rate" />);
    expect(html).toContain('aria-label="38 Pass rate"');
    expect(html).toContain('aria-hidden="true"');
  });

  it('reports its motion state so the sweep is verifiable', () => {
    expect(renderToStaticMarkup(<RadialGauge value={38} max={100} />)).toContain(
      'data-revealed="false"',
    );
  });
});

describe('SplitBar', () => {
  it('renders every segment with its value', () => {
    const html = renderToStaticMarkup(
      <SplitBar
        segments={[
          { id: 'proof', label: 'Proof', value: 644, tone: 'proved' },
          { id: 'spec', label: 'Spec', value: 503 },
        ]}
      />,
    );
    expect(textOf(html)).toContain('Proof');
    expect(textOf(html)).toContain('644');
    expect(textOf(html)).toContain('503');
  });

  it('reports the total', () => {
    const html = renderToStaticMarkup(
      <SplitBar
        segments={[
          { id: 'a', label: 'A', value: 1760 },
          { id: 'b', label: 'B', value: 503 },
        ]}
      />,
    );
    expect(html).toContain('data-total="2263"');
  });

  it('shows the total as a visible figure, not only as an attribute', () => {
    const html = renderToStaticMarkup(
      <SplitBar segments={[{ id: 'a', label: 'A', value: 1760 }]} />,
    );
    expect(textOf(html)).toContain('total');
    expect(textOf(html)).toContain('1,760');
  });

  it('reports its motion state so the sweep is verifiable', () => {
    const html = renderToStaticMarkup(
      <SplitBar segments={[{ id: 'a', label: 'A', value: 10 }]} />,
    );
    expect(html).toContain('data-revealed="false"');
  });
});

describe('StatTile', () => {
  it('renders the value, label and hint', () => {
    const html = renderToStaticMarkup(
      <StatTile value="4,102" label="Verified queries" hint="across 11 crates" tone="proved" />,
    );
    expect(textOf(html)).toContain('4,102');
    expect(textOf(html)).toContain('Verified queries');
    expect(textOf(html)).toContain('across 11 crates');
  });

  it('renders a not-recorded value verbatim', () => {
    const html = renderToStaticMarkup(<StatTile value="not recorded" label="Trusted items" />);
    expect(textOf(html)).toContain('not recorded');
  });

  it('reports its motion state so the reveal is verifiable', () => {
    const html = renderToStaticMarkup(<StatTile value="1" label="L" />);
    expect(html).toContain('data-revealed="false"');
  });
});

describe('OdometerReels', () => {
  it('renders one reel per digit', () => {
    const html = renderToStaticMarkup(<OdometerReels value={4102} />);
    expect(html).toContain('data-digits="4"');
    expect(html).toContain('data-reel="0"');
    expect(html).toContain('data-reel="3"');
  });

  it('honours an explicit reel count', () => {
    const html = renderToStaticMarkup(<OdometerReels value={42} digits={6} />);
    expect(html).toContain('data-digits="6"');
  });

  it('carries the full digit strip so a roll can pass through digits', () => {
    const html = renderToStaticMarkup(<OdometerReels value={1} />);
    expect(html).toContain('0123456789');
  });

  it('gives assistive technology the figure, not the digit strip', () => {
    const html = renderToStaticMarkup(<OdometerReels value={4102} />);
    expect(html).toContain('aria-label="4,102"');
    expect(html).toContain('role="img"');
    // The strip itself must not be announced.
    expect(html).toContain('data-reel="0" aria-hidden="true"');
  });
});

describe('CountFigure', () => {
  it('renders the target value with thousands separators', () => {
    const html = renderToStaticMarkup(<CountFigure value={12480} />);
    expect(textOf(html)).toBe('12,480');
  });

  it('renders the suffix and label', () => {
    const html = renderToStaticMarkup(<CountFigure value={122} suffix="ms" label="Verify time" />);
    expect(textOf(html)).toContain('122ms');
    expect(textOf(html)).toContain('Verify time');
  });

  it('reports the target and a settled state in the markup', () => {
    const html = renderToStaticMarkup(<CountFigure value={7} />);
    expect(html).toContain('data-target="7"');
    expect(html).toContain('data-settled="true"');
  });

  it('exposes the TRUE figure to assistive technology, not the rolling digit', () => {
    const html = renderToStaticMarkup(<CountFigure value={12480} label="Verified queries" />);
    expect(html).toContain('aria-label="12,480 Verified queries"');
    // The rolling digits must not be announced.
    expect(html).toContain('aria-hidden="true"');
  });
});
