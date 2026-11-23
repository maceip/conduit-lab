import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { Stepper } from './stepper';

const steps = [
  { caption: 'Start', render: () => <span>A</span> },
  { caption: 'Next', render: () => <span>B</span> },
];

describe('Stepper', () => {
  it('exposes step position for tests', () => {
    const html = renderToStaticMarkup(<Stepper steps={steps} />);
    expect(html).toContain('data-step-index="0"');
    expect(html).toContain('data-step-count="2"');
  });

  it('renders the first step caption', () => {
    const html = renderToStaticMarkup(<Stepper steps={steps} />);
    expect(html).toContain('Start');
  });

  it('renders a scrubbable range input and the transport controls', () => {
    const html = renderToStaticMarkup(<Stepper steps={steps} />);
    expect(html).toContain('type="range"');
    // The play button carries the label of the action it performs, so it
    // reads "Play" while paused and "Pause" while running.
    expect(html).toContain('aria-label="Play"');
    expect(html).toContain('aria-label="Step forward"');
    expect(html).toContain('aria-label="Step back"');
    expect(html).toContain('aria-label="Reset"');
  });

  it('names the spec clause of the active step', () => {
    const html = renderToStaticMarkup(
      <Stepper
        steps={[{ caption: 'Start', clause: 'ECMA-262 §12', render: () => <span>A</span> }]}
      />,
    );
    expect(html).toContain('ECMA-262 §12');
  });

  it('survives an empty step list', () => {
    const html = renderToStaticMarkup(<Stepper steps={[]} />);
    expect(html).toContain('data-step-count="0"');
  });
});
