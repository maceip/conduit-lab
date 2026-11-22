import { useEffect } from 'react';
import { create } from 'zustand';

/** How to use the studio: opened from Guide in the top bar (or the masthead on phones). */
export const useGuide = create<{ open: boolean; set: (open: boolean) => void }>((set) => ({ open: false, set: (open) => set({ open }) }));

const SECTIONS: Array<{ title: string; en: string; items: Array<[string, string]> }> = [
  {
    title: 'Pick a machine', en: '',
    items: [
      ['Catalogue', 'Catalogue in the top bar opens every machine as a card; click a card to enter.'],
      ['Groups', 'The left column groups machines as Mechanisms / Everyday Objects / Powertrain / Large Equipment; on phones it is a swipeable row of names.'],
      ['Search', 'The search box finds any part in any machine at any level — a brake disc, a piston ring — and Enter jumps straight to it.'],
    ],
  },
  {
    title: 'See how it works', en: '',
    items: [
      ['Study steps', '01, 02, 03 … in the left column are study steps. Click one and the scene cuts to that state (sectioned, running, key part selected).'],
      ['Run / Pause', 'Run or stop the machine\'s motion.'],
      ['Machine controls', 'Some machines have their own switches — gearbox gears, helicopter flight states, 747 parked / take-off / cruise / landing — with a note explaining what you are looking at.'],
    ],
  },
  {
    title: 'Take it apart', en: '',
    items: [
      ['Explode slider', 'Drag 0% to 100% and parts fly apart in true teardown order, bolts backing out along their own axes.'],
      ['Step teardown', 'The \u2039 \u203a buttons under the slider remove one part at a time and name what came off.'],
      ['Local explode', 'Select a part and hit Explode-this to pull apart just it and its neighbours.'],
      ['Go deeper', 'Parts marked \u25b8 are sub-assemblies: select one and open it to keep tearing down; the breadcrumb steps back out. Expand-all pulls every sub-assembly aside and explodes the whole tree.'],
    ],
  },
  {
    title: 'Look inside', en: '',
    items: [
      ['Section', 'Section cuts the machine along its centre line with pale hatched cut faces. A Cut slider appears: left skims the skin, right cuts deeper, 50% is the centre line.'],
      ['Labels', 'Labels show or hide the numbered part balloons; hovering one shows the part name.'],
    ],
  },
  {
    title: 'Parts', en: '',
    items: [
      ['Select', 'Click a part in the scene, or a row in the parts list, to open its card: name, role, material and a short description.'],
      ['Hide / Solo', 'The card can hide a part or show it alone; greyed rows in the list come back on click.'],
      ['Aim & Size', 'Aim swings the camera onto the part; Size scales it up or down for detail.'],
      ['Move', 'Turn Move on and drag parts anywhere.'],
    ],
  },
  {
    title: 'Views', en: '',
    items: [
      ['3D', 'The default ink axonometric — drag to rotate, scroll to zoom.'],
      ['Drawing', 'First-angle sheet: front, top, left and isometric views. Hidden draws invisible outlines as thin dashes; Project draws the projection rules for the hovered part.'],
      ['Front / Top', 'Single orthographic views seen straight on.'],
    ],
  },
  {
    title: 'Reset, theme, export', en: '',
    items: [
      ['Reset', 'Closes every part, undoes moves, scales and hiding, and returns to step one in the current view.'],
      ['Blueprint', 'Switches between the paper ink look and the engineering blueprint (deep blue ground, pale lines); your choice is remembered.'],
      ['Export', 'Plate PNG (an A4 exploded sheet with balloons, parts list and title block), teardown animation (WebM), part data (JSON).'],
    ],
  },
  {
    title: 'Share', en: '',
    items: [
      ['Links', 'The URL follows the current assembly and selection, e.g. #b747/wheel/rotors — copy it and anyone opens the same view.'],
    ],
  },
];

const KEYS: Array<[string, string]> = [
  ['/', 'Search parts'],
  ['\u2190 \u2192', 'Previous / next teardown step'],
  ['F', 'Aim the camera at the selected part'],
  ['Esc', 'Deselect, close dialogs'],
  ['Drag', 'Rotate (one finger on phones)'],
  ['Scroll', 'Zoom (pinch on phones)'],
];

export function Guide() {
  const { open, set } = useGuide();
  useEffect(() => {
    if (!open) return;
    const onKey = (e: KeyboardEvent) => { if (e.key === 'Escape') set(false); };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [open, set]);
  if (!open) return null;
  return (
    <div className="catalogue guide" role="dialog" aria-label="Guide" onClick={() => set(false)}>
      <div className="catalogue-sheet" onClick={(e) => e.stopPropagation()}>
        <header className="catalogue-head">
          <div>
            <p className="catalogue-kicker">GUIDE</p>
            <h2>How to use Inkwork</h2>
          </div>
          <button type="button" className="catalogue-close" onClick={() => set(false)} aria-label="Close">×</button>
        </header>
        <p className="guide-lead">Every machine can be rotated, sectioned and torn down step by step, drilling into its sub-assemblies as deep as they go. What follows follows the order of use.</p>
        <div className="guide-grid">
          {SECTIONS.map((s, i) => (
            <section key={s.title} className="guide-section">
              <h3><span className="guide-num">{String(i + 1).padStart(2, '0')}</span>{s.title}<span className="guide-en">{s.en}</span></h3>
              <dl>
                {s.items.map(([term, text]) => (
                  <div key={term} className="guide-item"><dt>{term}</dt><dd>{text}</dd></div>
                ))}
              </dl>
            </section>
          ))}
        </div>
        <section className="guide-keys">
          <h3>Shortcuts & gestures</h3>
          <ul>
            {KEYS.map(([k, what]) => <li key={k}><kbd>{k}</kbd>{what}</li>)}
          </ul>
        </section>
        <p className="catalogue-foot">Esc or click away to close · return here anytime from Guide</p>
      </div>
    </div>
  );
}
