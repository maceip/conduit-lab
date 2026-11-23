import { lazy, Suspense, useState, type ReactElement } from 'react';
import { GalleryNav, type GalleryTab } from './GalleryNav';
import { IconSheet } from './IconSheet';
import { PlateSheet } from './PlateSheet';
import { StatsSheet } from './StatsSheet';
import { RATCHET, formatRecorded } from './data';

/**
 * The scene sheet, loaded on demand.
 *
 * The tier-2 scene pulls in `three` — the heaviest thing in the atelier, and
 * the only thing the Scenes tab needs. Importing it lazily keeps that
 * payload out of the first load: the board comes up on the drawings, and the
 * WebGL scene arrives when the visitor asks for it.
 */
const SceneSheet = lazy(async () => {
  const module = await import('./SceneSheet');
  return { default: module.SceneSheet };
});

/** The four sections of the gallery. */
export type GallerySectionId = 'icons' | 'plates' | 'stats' | 'scenes';

const TABS: readonly GalleryTab[] = [
  { id: 'icons', label: 'Icons' },
  { id: 'plates', label: 'Plates' },
  { id: 'stats', label: 'Stats' },
  { id: 'scenes', label: 'Scenes' },
];

const SECTION_IDS: readonly GallerySectionId[] = ['icons', 'plates', 'stats', 'scenes'];

function isSectionId(id: string): id is GallerySectionId {
  return (SECTION_IDS as readonly string[]).includes(id);
}

/**
 * The board shown while the scene sheet's chunk is in flight.
 *
 * It carries the sheet's own heading so the panel does not jump when the
 * real sheet arrives, and it deliberately does NOT claim the `scene-sheet`
 * test id — that belongs to the loaded sheet.
 */
function SceneLoading(): ReactElement {
  return (
    <section className="atelier__sheet" data-testid="scene-loading">
      <div className="atelier__sheet-header">
        <h2 className="atelier__label">Scenes — tier 2 and tier 3</h2>
        <p className="atelier__meta">loading</p>
      </div>
      <div className="atelier__scene">
        <p className="atelier__note">
          The WebGL heap and the two algorithm traces are loaded on demand. They arrive in a
          moment.
        </p>
      </div>
    </section>
  );
}

/**
 * One tab panel.
 *
 * The element carries `gallery-panel-<id>` so the nav's `aria-controls`
 * points at something real, and it is labelled by the tab that selects it.
 */
function GalleryPanel({ id }: { id: GallerySectionId }): ReactElement {
  return (
    <section
      id={`gallery-panel-${id}`}
      role="tabpanel"
      aria-labelledby={`gallery-tab-${id}`}
      className="atelier__panel"
      data-testid={`panel-${id}`}
    >
      {id === 'icons' ? <IconSheet /> : null}
      {id === 'plates' ? <PlateSheet /> : null}
      {id === 'stats' ? <StatsSheet /> : null}
      {id === 'scenes' ? (
        <Suspense fallback={<SceneLoading />}>
          <SceneSheet />
        </Suspense>
      ) : null}
    </section>
  );
}

/**
 * The gallery shell.
 *
 * A tabbed board over the four sheets. Only the selected sheet is mounted:
 * the tier-2 WebGL scene creates a real GL context, and it has no business
 * running while the visitor is reading icons.
 */
export function Gallery(): ReactElement {
  const [active, setActive] = useState<GallerySectionId>('icons');

  const handleSelect = (tabId: string) => {
    if (isSectionId(tabId)) setActive(tabId);
  };

  return (
    <div className="atelier__gallery" data-testid="gallery-root">
      <header className="atelier__masthead">
        <h1 className="atelier__title">CONDUIT · Drafting Room</h1>
        <p className="atelier__subtitle">
          Exploded isometric icons, cutaway plates and tiered visualisation components
        </p>
        <p className="atelier__meta" data-testid="gallery-provenance">
          ratchet {formatRecorded(RATCHET.generatedAt)} · verus{' '}
          {formatRecorded(RATCHET.verusVersion)}
        </p>
      </header>

      <GalleryNav tabs={TABS} activeTab={active} onSelect={handleSelect} />

      <GalleryPanel id={active} />
    </div>
  );
}
