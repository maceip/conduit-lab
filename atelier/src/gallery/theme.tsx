import type { CSSProperties, ReactElement } from 'react';
import { BOARD } from '../contract/tokens';

/**
 * The drafter board's root class.
 *
 * Chief's scaffold already ships `className="atelier"` on the app root, so the
 * board stylesheet and the palette rule below land on the same element.
 */
export const BOARD_ROOT_CLASS = 'atelier';

/**
 * The board palette expressed as CSS custom properties.
 *
 * Every value is taken from `contract/tokens.ts` at module scope — the single
 * source of truth — so `gallery.css` can never drift from the tokens and no
 * hex is hand-written in the stylesheet.
 */
export const BOARD_VARS = {
  '--board-page': BOARD.page,
  '--board-plate': BOARD.plate,
  '--board-raised': BOARD.raised,
  '--board-line': BOARD.line,
  '--board-rib': BOARD.rib,
  '--board-edge-hi': BOARD.edgeHi,
  '--board-ink': BOARD.ink,
  '--board-ink-hi': BOARD.inkHi,
  '--board-live': BOARD.live,
  '--board-accent': BOARD.accent,
  '--board-warn': BOARD.warn,
  '--board-fail': BOARD.fail,
} as const;

/** `CSSProperties` widened so custom properties can be set without a cast. */
export type CSSVarProperties = CSSProperties & Record<`--${string}`, string>;

/** The palette as inline custom properties for a root element. */
export const BOARD_STYLE: CSSVarProperties = BOARD_VARS;

/** The palette as a CSS rule scoped to the board root class. */
export const BOARD_VARS_CSS = `.${BOARD_ROOT_CLASS} {${Object.entries(BOARD_VARS)
  .map(([name, value]) => `${name}: ${value};`)
  .join(' ')}}`;

/**
 * Mounts the board palette.
 *
 * Rendered inside the React tree rather than injected into `document.head` by
 * hand, so the custom properties exist as soon as the gallery mounts and the
 * stylesheet stays in sync with `contract/tokens.ts`.
 */
export function BoardVars(): ReactElement {
  return <style data-atelier-board="">{BOARD_VARS_CSS}</style>;
}
