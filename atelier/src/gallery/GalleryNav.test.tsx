import { describe, expect, it } from 'vitest';
import { renderToStaticMarkup } from 'react-dom/server';
import { GalleryNav, type GalleryTab } from './GalleryNav';
import { BOARD } from '../contract/tokens';

const TABS: readonly GalleryTab[] = [
  { id: 'icons', label: 'Icons' },
  { id: 'plates', label: 'Plates' },
  { id: 'stats', label: 'Stats' },
  { id: 'scenes', label: 'Scenes' },
];

const render = (activeTab = 'icons') =>
  renderToStaticMarkup(<GalleryNav tabs={TABS} activeTab={activeTab} onSelect={() => {}} />);

describe('GalleryNav', () => {
  it('renders a tab list with an accessible name', () => {
    const html = render();
    expect(html).toContain('role="tablist"');
    expect(html).toContain('aria-label="Gallery sections"');
  });

  it('renders one tab per section, each with an accessible name', () => {
    const html = render();
    const tabs = [...html.matchAll(/role="tab"/g)];
    expect(tabs).toHaveLength(TABS.length);
    for (const tab of TABS) {
      expect(html).toContain(`>${tab.label}</button>`);
    }
  });

  it('marks the active tab as selected', () => {
    const html = render('stats');
    expect(html).toContain('aria-selected="true"');
    expect(html).toContain('data-tab-id="stats"');
  });

  it('keeps exactly one tab in the tab order', () => {
    const html = render('plates');
    const stops = [...html.matchAll(/tabindex="0"/g)];
    expect(stops).toHaveLength(1);
    expect(html).toContain('tabindex="-1"');
  });

  it('points every tab at its panel', () => {
    const html = render();
    for (const tab of TABS) {
      expect(html).toContain(`aria-controls="gallery-panel-${tab.id}"`);
    }
  });

  it('mounts the board palette from the contract tokens', () => {
    const html = render();
    expect(html).toContain('--board-page:');
    expect(html).toContain(BOARD.page);
    expect(html).toContain(BOARD.plate);
    expect(html).toContain(BOARD.rib);
  });
});
