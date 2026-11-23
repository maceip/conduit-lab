import { useRef, type KeyboardEvent } from 'react';
import './gallery.css';

/** One section of the gallery. */
export interface GalleryTab {
  /** Stable id. Also drives the tab/panel id pair (`gallery-tab-*` / `gallery-panel-*`). */
  readonly id: string;
  /** Visible label. The board stylesheet renders it uppercase with tracking. */
  readonly label: string;
}

export interface GalleryNavProps {
  /** The sections to offer, in order. */
  readonly tabs: readonly GalleryTab[];
  /** Id of the tab currently shown. */
  readonly activeTab: string;
  /** Called with the id of the tab the visitor picked. */
  readonly onSelect: (tabId: string) => void;
  /** Extra class names for the tab list. */
  readonly className?: string;
  /** Accessible name of the tab list. */
  readonly label?: string;
}

/**
 * The gallery's tab bar.
 *
 * Chrome only: the tab list comes in as props, so this component knows
 * nothing about icons, plates, stats or scenes. It follows the WAI-ARIA
 * tabs pattern — one tab stop, arrow keys to move, `Home`/`End` to jump — and
 * every tab carries an accessible name from its label.
 */
export function GalleryNav({
  tabs,
  activeTab,
  onSelect,
  className,
  label = 'Gallery sections',
}: GalleryNavProps) {
  const buttons = useRef<(HTMLButtonElement | null)[]>([]);

  const activeIndex = tabs.findIndex((tab) => tab.id === activeTab);
  // A tab list must always have exactly one tab stop, even if the caller
  // hands over an active id that is not in the list.
  const focusIndex = activeIndex >= 0 ? activeIndex : 0;

  function move(next: number): void {
    const tab = tabs[next];
    if (!tab) return;
    onSelect(tab.id);
    buttons.current[next]?.focus();
  }

  function handleKeyDown(event: KeyboardEvent<HTMLButtonElement>, index: number): void {
    if (tabs.length === 0) return;
    const last = tabs.length - 1;
    let next: number;
    switch (event.key) {
      case 'ArrowRight':
      case 'ArrowDown':
        next = index === last ? 0 : index + 1;
        break;
      case 'ArrowLeft':
      case 'ArrowUp':
        next = index === 0 ? last : index - 1;
        break;
      case 'Home':
        next = 0;
        break;
      case 'End':
        next = last;
        break;
      default:
        return;
    }
    event.preventDefault();
    move(next);
  }

  const navClass = className ? `atelier__nav ${className}` : 'atelier__nav';

  return (
    <div className={navClass} role="tablist" aria-label={label} data-testid="gallery-nav">
      {tabs.map((tab, index) => {
        const selected = tab.id === activeTab;
        return (
          <button
            key={tab.id}
            ref={(element) => {
              buttons.current[index] = element;
            }}
            type="button"
            role="tab"
            id={`gallery-tab-${tab.id}`}
            className="atelier__tab"
            aria-selected={selected}
            aria-controls={`gallery-panel-${tab.id}`}
            tabIndex={index === focusIndex ? 0 : -1}
            data-tab-id={tab.id}
            onClick={() => onSelect(tab.id)}
            onKeyDown={(event) => handleKeyDown(event, index)}
          >
            {tab.label}
          </button>
        );
      })}
    </div>
  );
}
