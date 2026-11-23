import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { BOARD } from '../contract/tokens';
import { BOARD_ROOT_CLASS, BOARD_STYLE, BOARD_VARS, BoardVars } from './theme';

describe('board theme', () => {
  it('derives every custom property from the contract tokens', () => {
    expect(BOARD_VARS['--board-page']).toBe(BOARD.page);
    expect(BOARD_VARS['--board-plate']).toBe(BOARD.plate);
    expect(BOARD_VARS['--board-rib']).toBe(BOARD.rib);
    expect(BOARD_VARS['--board-ink']).toBe(BOARD.ink);
    expect(BOARD_VARS['--board-ink-hi']).toBe(BOARD.inkHi);
    expect(BOARD_VARS['--board-accent']).toBe(BOARD.accent);
    expect(BOARD_VARS['--board-warn']).toBe(BOARD.warn);
    expect(BOARD_VARS['--board-fail']).toBe(BOARD.fail);
  });

  it('exposes the palette as inline custom properties for a root element', () => {
    expect(BOARD_STYLE['--board-page']).toBe(BOARD.page);
  });

  it('mounts the palette on the board root class', () => {
    const html = renderToStaticMarkup(<BoardVars />);
    expect(html).toContain(`data-atelier-board`);
    expect(html).toContain(`.${BOARD_ROOT_CLASS}`);
    expect(html).toContain('--board-page:');
    expect(html).toContain(BOARD.page);
    expect(html).toContain(BOARD.plate);
    expect(html).toContain(BOARD.rib);
  });
});
