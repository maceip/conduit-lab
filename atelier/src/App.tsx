import { Gallery } from './gallery/Gallery';
import { BoardVars } from './gallery/theme';

/**
 * The atelier app.
 *
 * `BoardVars` mounts the board palette as CSS custom properties derived from
 * `contract/tokens.ts`, so the drafter board is themed before the gallery
 * paints. It is mounted here, once, at the app root.
 */
export function App() {
  return (
    <main className="atelier" data-testid="atelier-root">
      <BoardVars />
      <Gallery />
    </main>
  );
}
