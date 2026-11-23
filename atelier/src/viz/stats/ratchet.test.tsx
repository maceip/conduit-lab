import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { RatchetCounter, planRatchet } from './RatchetCounter';

const textOf = (html: string) => html.replace(/<!--[\s\S]*?-->/g, '').replace(/<[^>]*>/g, '');

describe('planRatchet', () => {
  it('rolls down when the count fell', () => {
    expect(planRatchet(3, 7).motion).toBe('down');
    expect(planRatchet(3, 7).from).toBe(7);
  });

  it('holds when the count is unchanged', () => {
    expect(planRatchet(4, 4).motion).toBe('hold');
  });

  it('reports a violation when the count rose', () => {
    expect(planRatchet(9, 4).motion).toBe('violation');
  });

  it('holds when there is no previous release to compare against', () => {
    expect(planRatchet(2, undefined).motion).toBe('hold');
  });

  it('can never roll upward: the figure never starts below the target', () => {
    for (let trusted = 0; trusted <= 12; trusted += 1) {
      for (let previous = 0; previous <= 12; previous += 1) {
        const plan = planRatchet(trusted, previous);
        // Starting BELOW the target would make the figure climb to it.
        expect(plan.from).toBeGreaterThanOrEqual(trusted);
        expect(plan.motion).not.toBe('up');
      }
    }
  });

  it('never travels at all unless the count fell', () => {
    for (let trusted = 0; trusted <= 12; trusted += 1) {
      for (let previous = 0; previous <= 12; previous += 1) {
        const plan = planRatchet(trusted, previous);
        if (plan.motion === 'down') {
          expect(plan.from).toBeGreaterThan(trusted);
        } else {
          // Holding and violating both stay exactly on the target.
          expect(plan.from).toBe(trusted);
        }
      }
    }
  });
});

describe('RatchetCounter', () => {
  it('renders the trusted count', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={0} />);
    expect(textOf(html)).toContain('0');
    expect(html).toContain('data-trusted="0"');
  });

  it('shows a violation when the count rises above the previous release', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={12} previous={4} />);
    expect(html).toContain('data-violation="true"');
    expect(textOf(html)).toContain('ratchet broken');
  });

  it('shows no violation when the count holds or falls', () => {
    expect(renderToStaticMarkup(<RatchetCounter trusted={4} previous={4} />)).toContain(
      'data-violation="false"',
    );
    expect(renderToStaticMarkup(<RatchetCounter trusted={2} previous={4} />)).toContain(
      'data-violation="false"',
    );
  });

  it('holds the value still on a violation rather than animating it up', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={12} previous={4} />);
    expect(textOf(html)).toContain('12');
    expect(html).toContain('data-settled="true"');
  });

  it('records the previous count on the root', () => {
    const html = renderToStaticMarkup(<RatchetCounter trusted={0} previous={4} />);
    expect(html).toContain('data-previous="4"');
  });
});
