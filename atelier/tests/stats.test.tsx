import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { CountFigure, RatchetCounter, StatTile } from '../src/viz/stats';
import { StatsSheet } from '../src/gallery/StatsSheet';
import { NOT_RECORDED, RATCHET, STATS, formatRecorded } from '../src/gallery/data';

describe('the stats components', () => {
  it('renders a real figure', () => {
    const html = renderToStaticMarkup(<CountFigure value={4102} label="verified queries" />);
    expect(html).toContain('4,102');
    expect(html).toContain('verified queries');
  });

  it('renders "not recorded" for a field the reports do not carry', () => {
    const html = renderToStaticMarkup(
      <StatTile value={NOT_RECORDED} label="trusted items (stats)" />,
    );
    expect(html).toContain(NOT_RECORDED);
  });

  it('holds the ratchet counter when no prior figure is known', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={0} testId="ratchet-counter" />);
    expect(html).toContain('data-testid="ratchet-counter"');
    expect(html).toContain('data-trusted="0"');
    expect(html).toContain('data-settled="true"');
    expect(html).toContain('data-violation="false"');
  });
});

describe('the stats sheet', () => {
  const html = renderToStaticMarkup(<StatsSheet />);

  it('renders on the sheet', () => {
    expect(html).toContain('data-testid="stats-sheet"');
  });

  it('shows the real verified-query count', () => {
    expect(RATCHET.verifiedQueries.recorded).toBe(true);
    expect(html).toContain(formatRecorded(RATCHET.verifiedQueries, (v) => v.toLocaleString('en-US')));
    expect(html).toContain('4,102');
  });

  it('shows the real crate count and vstd count', () => {
    expect(html).toContain(formatRecorded(RATCHET.crateCount));
    expect(html).toContain(formatRecorded(STATS.vstdVerified, (v) => v.toLocaleString('en-US')));
  });

  it('mounts the ratchet counter with the real trusted-item count', () => {
    expect(html).toContain('data-testid="ratchet-counter"');
    expect(html).toContain(`data-trusted="${RATCHET.trustedItemCount.value ?? 0}"`);
    expect(html).toContain('data-settled="true"');
  });

  it('renders "not recorded" for the field stats.json does not carry', () => {
    expect(STATS.trustedItemCount.recorded).toBe(false);
    expect(html).toContain(NOT_RECORDED);
  });

  it('lists the crates the ratchet verified', () => {
    expect(html).toContain('data-testid="ratchet-crates"');
    if (!RATCHET.crates.recorded) throw new Error('crates should be recorded');
    for (const crate of RATCHET.crates.value) {
      expect(html).toContain(`data-crate="${crate.name}"`);
    }
  });
});
