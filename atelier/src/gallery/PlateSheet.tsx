import type { ReactElement } from 'react';
import { KernelRendererPlate, V8CorePlate } from '../illustration/plates';

/**
 * The two large cutaway plates.
 *
 * The hero plate is the eight core machines as one continuous exploded
 * assembly; the second is the strategy plate — proved kernel in front of
 * disposable per-site renderers, with the unproved parts hatched.
 */
export function PlateSheet(): ReactElement {
  return (
    <section className="atelier__sheet" data-testid="plate-sheet">
      <div className="atelier__sheet-header">
        <h2 className="atelier__label">Plates — cutaway assemblies</h2>
        <p className="atelier__meta">2 figures · shared isometric projection</p>
      </div>

      <div className="atelier__grid atelier__grid--wide">
        <figure className="atelier__plate" data-testid="plate-v8-core">
          <V8CorePlate title="V8 mandatory core — exploded" />
          <figcaption className="atelier__caption">V8 mandatory core — exploded</figcaption>
          <p className="atelier__note">
            The eight core machines as one continuous explode along a shared axis.
          </p>
        </figure>

        <figure className="atelier__plate" data-testid="plate-kernel-renderer">
          <KernelRendererPlate title="Verified kernel and sandboxed renderer" />
          <figcaption className="atelier__caption">
            Verified kernel and sandboxed renderer
          </figcaption>
          <p className="atelier__note">
            The proved kernel in front of disposable per-site renderers; the design-only parts
            are hatched because they are not yet proved.
          </p>
        </figure>
      </div>
    </section>
  );
}
