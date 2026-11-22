import { Fragment, useEffect, useMemo, useRef, useState } from 'react';
import { allMachines, GROUPS, lineage, MACHINES, machineById, useMachine } from '../machines';
import type { MachineDef } from '../machines/types';
import { useCatalogue } from './Catalogue';
import { useGuide } from './Guide';
import { useTree } from './Tree';
import { aimAt, clearEdits, editOf, partEdits, restoreAll, selectMachine, useStudio, type ViewMode } from '../state';
import { useTheme } from '../theme';

const pad = (n: number) => String(n).padStart(2, '0');

export function TitleColumn() {
  const machine = useMachine();
  const { step, explode, running, section, sectionDepth, labels, view, hiddenLines, projection, moveMode, deep, hidden, solo, set } = useStudio();
  const drawingMode = view === 'drawing';
  const { Controls, Toggles } = machine;
  const chain = lineage(machine);
  const root = chain[0];

  const goStep = (index: number) => {
    const { state, apply } = machine.steps[index];
    const { viewNonce } = useStudio.getState();
    apply?.();
    set({
      localExplode: null, step: index, explode: state.explode, section: state.section, running: state.running,
      selected: state.select, focus: state.focus, view: drawingMode ? 'drawing' : 'perspective', viewNonce: viewNonce + 1,
    });
  };

  return (
    <section className="title-column">
      <header className="masthead">
        <h1 className="mast-title">Inkwork</h1>
        <div className="mast-rule" />
        <p className="mast-en">INKWORK</p>
        <p className="mast-zh">Engineering Drawing · Interactive Teardown</p>
        <div className="fig-rule"><span>FIG. {pad(MACHINES.indexOf(root) + 1)}{chain.length > 1 ? `-${chain.length - 1}` : ''}</span><i /></div>
        <div className="mast-buttons">
          <button type="button" className="mast-catalogue" onClick={() => useGuide.getState().set(true)}>Guide</button>
          <button type="button" className="mast-catalogue" onClick={() => useCatalogue.getState().set(true)}>Catalogue</button>
          <button type="button" className="mast-catalogue" onClick={() => useTree.getState().set(!useTree.getState().open)}>Structure</button>
        </div>
      </header>

      <PartSearch />

      <MachineSwitcher rootId={root.id} />
      <MachineStrip rootId={root.id} />

      <div className="subject">
        {chain.length > 1 && (
          <nav className="crumbs" aria-label="Where am I">
            {chain.slice(0, -1).map((m) => (
              <button key={m.id} type="button" onClick={() => selectMachine(m.id)}>{m.name}</button>
            ))}
            <span>{machine.name}</span>
          </nav>
        )}
        <h2>{machine.name}</h2>
        <p>{machine.en} · {machine.subtitle}</p>
      </div>

      <ol className="steps">
        {machine.steps.map((item, index) => (
          <li key={item.title} className={index === step ? 'is-active' : ''}>
            <button type="button" onClick={() => goStep(index)}>
              <span className="step-num">{pad(index + 1)}</span>
              <span className="step-title">{item.title}</span>
              <span className="step-en">{item.en}</span>
            </button>
            {index === step && <p className="step-body">{item.body}</p>}
          </li>
        ))}
      </ol>

      <div className="controls">
        <label className="slider">
          <span>Explode</span>
          <input type="range" min={0} max={1} step={0.01} value={explode} onChange={(e) => set({ explode: Number(e.target.value) })} />
          <output>{Math.round(explode * 100)}%</output>
        </label>
        {section && (
          <label className="slider" title="Drag the cut plane: 0% skims the skin, 50% is the centre line, 100% leaves the last layer">
            <span>Cut</span>
            <input type="range" min={0} max={1} step={0.01} value={sectionDepth} onChange={(e) => set({ sectionDepth: Number(e.target.value) })} />
            <output>{Math.round(sectionDepth * 100)}%</output>
          </label>
        )}
        <Stepper machine={machine} explode={explode} />
        {Controls && <Controls />}
        <div className="toggles">
          <button type="button" className={running ? 'is-on' : ''} onClick={() => set({ running: !running })}>{running ? 'Pause' : 'Run'}</button>
          {Toggles && <Toggles />}
          <button type="button" className={section ? 'is-on' : ''} onClick={() => set({ section: !section })}>Section</button>
          {drawingMode ? (
            <>
              <button type="button" className={hiddenLines ? 'is-on' : ''} onClick={() => set({ hiddenLines: !hiddenLines })} title="Hidden outlines (thin dashed)">Hidden</button>
              <button type="button" className={projection ? 'is-on' : ''} onClick={() => set({ projection: !projection })} title="Length aligned · Height level · Width equal">Project</button>
            </>
          ) : (
            <>
              <button type="button" className={labels ? 'is-on' : ''} onClick={() => set({ labels: !labels })}>Labels</button>
              <button type="button" className={moveMode ? 'is-on' : ''} onClick={() => set({ moveMode: !moveMode })} title="Drag parts to move them (view rotation pauses)">Move</button>
              {(hidden.length > 0 || solo) && (
                <button type="button" className="is-on" onClick={() => set({ hidden: [], solo: null })} title="Show every hidden part">
                  Show all{hidden.length > 0 ? ` (${hidden.length})` : ''}
                </button>
              )}
              {machine.children && (
                <button
                  type="button"
                  className={deep ? 'is-on' : ''}
                  onClick={() => set(deep ? { deep: false } : { deep: true, explode: 1, localExplode: null })}
                  title="Explode the whole tree, pulling each sub-assembly aside too"
                >
                  Expand all
                </button>
              )}
            </>
          )}
        </div>
      </div>
    </section>
  );
}

const VIEWS: Array<[ViewMode, string]> = [['perspective', '3D'], ['drawing', 'Drawing'], ['elevation', 'Front'], ['plan', 'Top']];

type ExportKind = 'plate' | 'video' | 'json';

const EXPORTS: Array<[ExportKind, string, string]> = [
  ['plate', 'Plate PNG', 'A4 landscape exploded sheet: balloons, parts list, title block'],
  ['video', 'Teardown video', 'Assembled → exploded → closed, as a WebM video'],
  ['json', 'Part data', 'Parts list and study steps as JSON'],
];

/** Opens the structure tree beside the plate. */
function TreeToggle() {
  const { open, set } = useTree();
  return <button type="button" className={`meta-action meta-tree${open ? ' is-on' : ''}`} aria-pressed={open} onClick={() => set(!open)} title="Structure: every assembly and part at every level">Structure</button>;
}

export function PlateMeta({ onExport, busy, recording }: { onExport: (kind: ExportKind) => void; busy: boolean; recording: number | null }) {
  const { view, viewNonce, set } = useStudio();
  const machine = useMachine();
  return (
    <nav className="plate-meta" aria-label="Views">
      <button type="button" className="meta-catalogue" onClick={() => useCatalogue.getState().set(true)} title="All machines at a glance">Catalogue</button>
      <button type="button" className="meta-action meta-guide" onClick={() => useGuide.getState().set(true)} title="How to use this studio">Guide</button>
      <TreeToggle />
      <div className="views" role="group" aria-label="Views">
        {VIEWS.map(([id, label]) => (
          <button key={id} type="button" aria-pressed={view === id} className={view === id ? 'is-on' : ''} onClick={() => set({ view: id, focus: null, viewNonce: viewNonce + 1 })}>{label}</button>
        ))}
      </div>
      <button type="button" className="meta-action" onClick={() => restoreAll(machine.steps[0])} title="Close every part, undo moves, scales and hiding, turn off the section, and return to step one">
        Reset
      </button>
      <ThemeToggle />
      <ExportMenu onExport={onExport} busy={busy} recording={recording} />
    </nav>
  );
}

/** Paper or blueprint. */
function ThemeToggle() {
  const { theme, set } = useTheme();
  const blueprint = theme === 'blueprint';
  return (
    <button type="button" className={`meta-action meta-theme${blueprint ? ' is-on' : ''}`} aria-pressed={blueprint} onClick={() => set(blueprint ? 'paper' : 'blueprint')} title={blueprint ? 'Back to the paper ink look' : 'Blueprint: deep blue ground, white lines'}>
      <span className="theme-swatch" aria-hidden="true" />Blueprint
    </button>
  );
}

/** Plate, animation and data exports behind one button. */
function ExportMenu({ onExport, busy, recording }: { onExport: (kind: ExportKind) => void; busy: boolean; recording: number | null }) {
  const [open, setOpen] = useState(false);
  useEffect(() => {
    if (!open) return;
    const close = (e: Event) => {
      if (e instanceof KeyboardEvent ? e.key === 'Escape' : !(e.target as HTMLElement).closest('.export')) setOpen(false);
    };
    window.addEventListener('pointerdown', close);
    window.addEventListener('keydown', close);
    return () => {
      window.removeEventListener('pointerdown', close);
      window.removeEventListener('keydown', close);
    };
  }, [open]);
  return (
    <div className="export">
      <button
        type="button"
        className={`meta-action${recording !== null ? ' is-recording' : ''}`}
        disabled={busy}
        aria-haspopup="menu"
        aria-expanded={open}
        onClick={() => setOpen(!open)}
      >
        {recording !== null ? `Recording ${recording.toFixed(0)}s` : 'Export'} <span aria-hidden="true">▾</span>
      </button>
      {open && (
        <ul className="export-menu" role="menu">
          {EXPORTS.map(([kind, label, hint]) => (
            <li key={kind} role="none">
              <button type="button" role="menuitem" onClick={() => { setOpen(false); onExport(kind); }}>
                <span className="export-label">{label}</span>
                <span className="export-hint">{hint}</span>
              </button>
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}

/** Group tabs, and the machines of the open group. */
function MachineSwitcher({ rootId }: { rootId: string }) {
  const home = GROUPS.findIndex((g) => g.machines.some((m) => m.id === rootId));
  const [open, setOpen] = useState(home);
  useEffect(() => setOpen(home), [home]);
  const group = GROUPS[open] ?? GROUPS[0];
  return (
    <nav className="machines" aria-label="Choose a machine">
      <div className="machines-tabs" role="tablist">
        {GROUPS.map((g, i) => (
          <button key={g.name} type="button" role="tab" aria-selected={i === open} className={i === open ? 'is-open' : ''} onClick={() => setOpen(i)}>
            {g.name}<span className="machines-count">{g.machines.length}</span>
          </button>
        ))}
        <button type="button" className="machines-all" onClick={() => useCatalogue.getState().set(true)} title="All machines at a glance">All ↗</button>
      </div>
      <div className="machines-list" role="tabpanel">
        {group.machines.map((m) => (
          <button key={m.id} type="button" className={m.id === rootId ? 'is-on' : ''} onClick={() => selectMachine(m.id)} title={m.summary}>
            {m.name}
          </button>
        ))}
      </div>
    </nav>
  );
}

/** Narrow screens: every machine in one row that scrolls sideways, the open one kept in view. */
function MachineStrip({ rootId }: { rootId: string }) {
  const ref = useRef<HTMLElement>(null);
  useEffect(() => {
    const strip = ref.current;
    const on = strip?.querySelector<HTMLElement>('.is-on');
    if (strip && on) strip.scrollTo({ left: on.offsetLeft - (strip.clientWidth - on.offsetWidth) / 2, behavior: 'smooth' });
  }, [rootId]);
  return (
    <nav className="machine-strip" aria-label="Choose a machine" ref={ref}>
      {GROUPS.map((g) => (
        <Fragment key={g.name}>
          <span className="strip-group">{g.name}</span>
          {g.machines.map((m) => (
            <button key={m.id} type="button" className={m.id === rootId ? 'is-on' : ''} onClick={() => selectMachine(m.id)}>{m.name}</button>
          ))}
        </Fragment>
      ))}
    </nav>
  );
}

/** Find a part anywhere, in any machine or subassembly, and go straight to it. */
function PartSearch() {
  const [query, setQuery] = useState('');
  const [active, setActive] = useState(0);
  const results = useMemo(() => {
    const q = query.trim().toLowerCase();
    if (!q) return [];
    const found: Array<{ machine: MachineDef; part: MachineDef['parts'][number] }> = [];
    for (const machine of allMachines()) {
      for (const part of machine.parts) {
        if (part.name.toLowerCase().includes(q) || part.en.toLowerCase().includes(q) || machine.name.includes(q)) found.push({ machine, part });
      }
    }
    return found.slice(0, 8);
  }, [query]);
  useEffect(() => setActive(0), [query]);

  // Global keys: "/" to search, Esc to let go of the selection, F to aim at it.
  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      const typing = (e.target as HTMLElement).tagName === 'INPUT';
      if (e.key === '/' && !typing) {
        e.preventDefault();
        document.getElementById('part-search')?.focus();
      } else if (e.key === 'Escape' && !typing) {
        useStudio.getState().set({ selected: null });
      } else if ((e.key === 'f' || e.key === 'F') && !typing) {
        const { selected } = useStudio.getState();
        if (selected) aimAt(selected);
      }
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, []);

  const go = (hit: (typeof results)[number]) => {
    const switching = useStudio.getState().machineId !== hit.machine.id;
    selectMachine(hit.machine.id);
    useStudio.getState().set({ selected: hit.part.id });
    // Let a newly opened assembly put itself together before swinging the camera in.
    window.setTimeout(() => aimAt(hit.part.id), switching ? 2200 : 0);
    setQuery('');
    (document.activeElement as HTMLElement | null)?.blur();
  };

  return (
    <div className="search">
      <input
        id="part-search"
        type="search"
        placeholder="Search parts — a piston ring, an injector… (press /)"
        value={query}
        autoComplete="off"
        onChange={(e) => setQuery(e.target.value)}
        onKeyDown={(e) => {
          if (e.key === 'ArrowDown') { e.preventDefault(); setActive((a) => Math.min(results.length - 1, a + 1)); }
          if (e.key === 'ArrowUp') { e.preventDefault(); setActive((a) => Math.max(0, a - 1)); }
          if (e.key === 'Enter' && results[active]) go(results[active]);
          if (e.key === 'Escape') { setQuery(''); e.currentTarget.blur(); }
        }}
      />
      {results.length > 0 && (
        <ul className="search-results" role="listbox">
          {results.map((hit, i) => (
            <li key={`${hit.machine.id}:${hit.part.id}`} role="option" aria-selected={i === active}>
              <button type="button" className={i === active ? 'is-active' : ''} onMouseEnter={() => setActive(i)} onClick={() => go(hit)}>
                <span className="search-name">{hit.part.name}</span>
                <span className="search-path">{lineage(hit.machine).map((m) => m.name).join(' › ')}</span>
              </button>
            </li>
          ))}
        </ul>
      )}
    </div>
  );
}

/** The teardown as discrete steps: each step ends where some part (or set of screws) is off. */
function teardownStops(machine: MachineDef) {
  const stops = new Map<number, { at: number; ids: string[]; labels: string[] }>();
  const add = (end: number, label: string, id?: string) => {
    const key = Math.round(end * 1000);
    const stop = stops.get(key) ?? { at: end, ids: [], labels: [] };
    stop.labels.push(label);
    if (id) stop.ids.push(id);
    stops.set(key, stop);
  };
  for (const [id, set] of Object.entries(machine.boltSets)) {
    if (set.stage[1] > set.stage[0]) add(set.stage[1], `Screws of ${machine.parts.find((p) => p.id === set.owner)?.name ?? ''}`);
  }
  for (const p of machine.parts) if (p.stage[1] > p.stage[0]) add(p.stage[1], p.name, p.id);
  return [...stops.values()].sort((a, b) => a.at - b.at);
}

/** Step through the teardown one part at a time. */
function Stepper({ machine, explode }: { machine: MachineDef; explode: number }) {
  const set = useStudio((s) => s.set);
  const stops = useMemo(() => teardownStops(machine), [machine]);
  if (stops.length === 0) return null;
  const done = stops.filter((s) => s.at <= explode + 1e-4).length;
  const go = (n: number) => {
    const target = n <= 0 ? 0 : stops[Math.min(n, stops.length) - 1].at;
    const next = stops[n - 1];
    set({ explode: target, localExplode: null, deep: false, selected: next?.ids[0] ?? null });
  };
  const current = done > 0 ? stops[done - 1] : null;
  return (
    <div className="stepper" title="Arrow keys work too">
      <StepKeys onPrev={() => done > 0 && go(done - 1)} onNext={() => done < stops.length && go(done + 1)} />
      <button type="button" disabled={done === 0} onClick={() => go(done - 1)} aria-label="Previous step">‹</button>
      <p>
        <span className="stepper-count">{pad(done)} / {pad(stops.length)}</span>
        {current ? `Remove ${current.labels.join(', ')}` : 'Fully assembled · press › to take it apart'}
      </p>
      <button type="button" disabled={done === stops.length} onClick={() => go(done + 1)} aria-label="Next step">›</button>
    </div>
  );
}

/** Left and right arrow keys step through the teardown (when not typing). */
function StepKeys({ onPrev, onNext }: { onPrev: () => void; onNext: () => void }) {
  useEffect(() => {
    const onKey = (e: KeyboardEvent) => {
      if ((e.target as HTMLElement).tagName === 'INPUT') return;
      if (e.key === 'ArrowRight') onNext();
      if (e.key === 'ArrowLeft') onPrev();
    };
    window.addEventListener('keydown', onKey);
    return () => window.removeEventListener('keydown', onKey);
  }, [onPrev, onNext]);
  return null;
}

/** Size slider for the selected part, plus a button to undo its moves and resizing. */
function PartSize({ id }: { id: string }) {
  const nonce = useStudio((s) => s.editNonce);
  const [scale, setScale] = useState(() => partEdits.get(id)?.scale ?? 1);
  useEffect(() => setScale(partEdits.get(id)?.scale ?? 1), [id, nonce]);
  return (
    <div className="part-size">
      <label className="slider">
        <span>Size</span>
        <input
          type="range"
          min={0.5}
          max={3}
          step={0.05}
          value={scale}
          onChange={(e) => {
            const value = Number(e.target.value);
            editOf(id).scale = value;
            setScale(value);
          }}
        />
        <output>{scale.toFixed(2)}×</output>
      </label>
      <button type="button" className="caption-action" onClick={() => clearEdits(id)}>Revert</button>
    </div>
  );
}

export function PartsLegend() {
  const machine = useMachine();
  const { selected, hovered, localExplode, view, hidden, solo, set } = useStudio();
  const focus = selected ?? hovered;
  const part = focus ? machine.parts.find((p) => p.id === focus) : undefined;
  const child = part && machine.children?.[part.id];
  // A local explode follows the selection, and folds away when nothing is selected.
  useEffect(() => {
    const { localExplode: current } = useStudio.getState();
    if (current && current !== selected) set({ localExplode: selected });
  }, [selected, set]);
  return (
    <aside className="legend">
      {part && (
        <div className="caption">
          <div className="caption-head">
            <span className="caption-num">{pad(part.index)}</span>
            <div>
              <h3>{part.name}</h3>
              <p className="caption-en">{part.en} · {part.role}</p>
            </div>
            {selected && <button type="button" className="caption-close" onClick={() => set({ selected: null })} aria-label="Deselect">×</button>}
          </div>
          <p className="caption-body">{part.description}</p>
          {selected && view !== 'drawing' && <PartSize id={selected} />}
          {selected && view !== 'drawing' && (
            <div className="caption-tools">
              <button type="button" className="caption-action" onClick={() => set({ hidden: [...hidden, selected], selected: null, solo: solo === selected ? null : solo })}>Hide</button>
              <button type="button" className="caption-action" onClick={() => set({ solo: solo === selected ? null : selected })}>{solo === selected ? 'Show all' : 'Solo'}</button>
              <button type="button" className="caption-action" onClick={() => aimAt(selected)} title="Aim the camera at this part (key F)">Aim</button>
            </div>
          )}
          {child && (
            <button type="button" className="caption-open" onClick={() => selectMachine(child)}>
              Open this sub-assembly: {machineById(child).summary} <span aria-hidden="true">↘</span>
            </button>
          )}
          <div className="caption-foot">
            <p className="caption-mat">{part.material}</p>
            {selected && (
              <button type="button" className="caption-action" onClick={() => set({ localExplode: localExplode === selected ? null : selected, explode: 0 })}>
                {localExplode === selected ? 'Collapse' : 'Explode this'} <span aria-hidden="true">{localExplode === selected ? '↙' : '↗'}</span>
              </button>
            )}
          </div>
        </div>
      )}
      <table className={`parts${machine.parts.length > 15 ? ' is-long' : ''}`}>
        <caption>PARTS LIST</caption>
        <tbody>
          {machine.parts.map((item) => (
            <tr
              key={item.id}
              className={`${selected === item.id ? 'is-selected' : ''}${hovered === item.id ? ' is-hovered' : ''}${hidden.includes(item.id) || (solo && solo !== item.id) ? ' is-hidden' : ''}`}
              onClick={() => hidden.includes(item.id)
                ? set({ hidden: hidden.filter((h) => h !== item.id), selected: item.id })
                : set({ selected: selected === item.id ? null : item.id })}
              onPointerEnter={() => set({ hovered: item.id })}
              onPointerLeave={() => set({ hovered: null })}
            >
              <td className="num">{pad(item.index)}</td>
              <td>{item.name}{machine.children?.[item.id] && <span className="has-child" title="opens further"> ▸</span>}</td>
              <td className="en">{item.en}</td>
            </tr>
          ))}
        </tbody>
      </table>
      <div className="title-block">
        <span>Dwg No {machine.drawingNo}</span>
        <span>Scale {machine.scale}</span>
        <span>Sheet 1 of 1</span>
      </div>
    </aside>
  );
}
