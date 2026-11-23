import type { ComponentType, ReactElement } from 'react';
import type { IconProps } from '../contract';
import {
  HiddenClassesIcon,
  IgnitionIcon,
  IsolateIcon,
  NewSpaceIcon,
  OldSpaceIcon,
  ParserIcon,
  PointerTaggingIcon,
  RatchetIcon,
} from '../illustration/icons';

/** One icon in the sheet. */
interface IconEntry {
  /** Stable slug; also the test id and the file stem. */
  readonly slug: string;
  /** What the machinery is. */
  readonly label: string;
  /** The subject it depicts, as the spec names it. */
  readonly subject: string;
  readonly Component: ComponentType<IconProps>;
}

const ICONS: readonly IconEntry[] = [
  {
    slug: 'isolate',
    label: 'v8::Isolate',
    subject: 'twin-silo process skid',
    Component: IsolateIcon,
  },
  {
    slug: 'pointer-tagging',
    label: 'Tagged pointer lattice',
    subject: 'pointer tagging lattice',
    Component: PointerTaggingIcon,
  },
  {
    slug: 'hidden-classes',
    label: 'Hidden-class transition tree',
    subject: 'hidden-class transitions',
    Component: HiddenClassesIcon,
  },
  {
    slug: 'parser',
    label: 'Lexer → Pratt parser',
    subject: 'lexer and Pratt parser pipeline',
    Component: ParserIcon,
  },
  {
    slug: 'ignition',
    label: 'Bytecode dispatch loop',
    subject: 'ignition loop',
    Component: IgnitionIcon,
  },
  {
    slug: 'old-space',
    label: 'GC old generation',
    subject: 'old-generation slab',
    Component: OldSpaceIcon,
  },
  {
    slug: 'new-space',
    label: 'Scavenger nursery',
    subject: 'new-space nursery',
    Component: NewSpaceIcon,
  },
  {
    slug: 'ratchet',
    label: 'The trusted-item ratchet',
    subject: 'trusted-item ratchet',
    Component: RatchetIcon,
  },
];

/** The size of the big, annotated reading. */
const LARGE_SIZE = 400;
/** The size of the small, unannotated reading. */
const SMALL_SIZE = 28;

/**
 * The eight exploded isometric icons.
 *
 * Each machinery is shown twice: once large and annotated, so the balloons,
 * leader lines and section hatching read; once small and unannotated, which is
 * how the icon is used inline. Every instance carries a `title`, so no SVG on
 * the sheet is left without an accessible name.
 */
export function IconSheet(): ReactElement {
  return (
    <section className="atelier__sheet" data-testid="icon-sheet">
      <div className="atelier__sheet-header">
        <h2 className="atelier__label">Icons — exploded isometric machinery</h2>
        <p className="atelier__meta">{ICONS.length} figures · az 42° el 30°</p>
      </div>

      <div className="atelier__grid atelier__grid--icons">
        {ICONS.map((icon) => (
          <figure key={icon.slug} className="atelier__card" data-testid={`icon-${icon.slug}`}>
            <div className="atelier__icon-pair">
              <div className="atelier__icon-large">
                <icon.Component
                  size={LARGE_SIZE}
                  annotated
                  title={`${icon.label} — ${icon.subject}, annotated`}
                />
              </div>
              <figure className="atelier__icon-small">
                <icon.Component
                  size={SMALL_SIZE}
                  annotated={false}
                  title={`${icon.label} — ${icon.subject}, inline`}
                />
                <figcaption>{SMALL_SIZE}px</figcaption>
              </figure>
            </div>
            <figcaption className="atelier__caption">{icon.label}</figcaption>
            <p className="atelier__note">{icon.subject}</p>
          </figure>
        ))}
      </div>
    </section>
  );
}
