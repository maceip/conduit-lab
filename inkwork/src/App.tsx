import { useEffect, useState } from 'react';
import { Canvas, useThree } from '@react-three/fiber';
import { OrbitControls } from '@react-three/drei';
import * as THREE from 'three';
import { Catalogue } from './components/Catalogue';
import { Guide } from './components/Guide';
import { Tree } from './components/Tree';
import { PartsLegend, PlateMeta, TitleColumn } from './components/Plate';
import { currentMachine, hasMachine, lineage, machineById, useMachine } from './machines';
import { CameraRig, Guides, InkRenderer, MotionDriver } from './scene';
import { isEmbed, restoreAll, selectMachine, useStudio } from './state';
import './theme';
import { bridge, exportPlate, recordTeardown } from './export';
import { DrawingRig } from './drawing/DrawingRig';
import { DrawingSheet } from './drawing/Sheet';
import './styles/fonts.css';
import './styles/theme.css';

function download(name: string, href: string) {
  const link = document.createElement('a');
  link.href = href;
  link.download = name;
  link.click();
}

function exportJson() {
  const m = currentMachine();
  const data = { id: m.id, name: m.name, en: m.en, drawingNo: m.drawingNo, scale: m.scale, parts: m.parts, steps: m.steps.map(({ apply: _apply, ...step }) => step) };
  const url = URL.createObjectURL(new Blob([JSON.stringify(data, null, 2)], { type: 'application/json' }));
  download(`gewu-${m.id}.json`, url);
  URL.revokeObjectURL(url);
}

/** Lets the exporters change the render resolution from outside the canvas. */
function ExportBridge() {
  const setDpr = useThree((s) => s.setDpr);
  const gl = useThree((s) => s.gl);
  useEffect(() => {
    bridge.setDpr = setDpr;
    bridge.getDpr = () => gl.getPixelRatio();
  }, [setDpr, gl]);
  return null;
}

/**
 * The address bar follows the assembly and the selected part (#turboprop/prop-hub),
 * so a view can be shared; opening such a link goes straight there.
 */
function useDeepLink() {
  useEffect(() => {
    const open = () => {
      const parts = decodeURIComponent(window.location.hash.slice(1)).split('/');
      for (let n = parts.length; n > 0; n -= 1) {
        const id = parts.slice(0, n).join('/');
        if (hasMachine(id)) {
          selectMachine(id);
          const part = parts[n];
          if (part && currentMachine().parts.some((p) => p.id === part)) useStudio.getState().set({ selected: part });
          return;
        }
      }
    };
    open();
    window.addEventListener('hashchange', open);
    const unsubscribe = useStudio.subscribe((s, prev) => {
      if (s.machineId === prev.machineId && s.selected === prev.selected) return;
      const hash = `#${s.machineId}${s.selected ? `/${s.selected}` : ''}`;
      if (window.location.hash !== hash) window.history.replaceState(null, '', hash);
    });
    return () => {
      window.removeEventListener('hashchange', open);
      unsubscribe();
    };
  }, []);
}

/** Opening an assembly puts it in its first study step (cut open, running, …). */
function useFirstStep() {
  const machine = useMachine();
  useEffect(() => {
    const first = machine.steps[0];
    if (!first) return;
    first.apply?.();
    const { selected, set } = useStudio.getState();
    set({
      section: first.state.section,
      running: first.state.running,
      focus: first.state.focus,
      selected: isEmbed ? null : (selected ?? first.state.select),
    });
  }, [machine]);
}

/** Horizontal offset (px) of the projection centre, so the machine clears the text column in full studio mode. */
function useStageShift() {
  const [shift, setShift] = useState(0);
  useEffect(() => {
    if (isEmbed) {
      setShift(0);
      return;
    }
    const measure = () => setShift(window.innerWidth >= 1100 ? Math.min(60, window.innerWidth * 0.025) : 0);
    measure();
    window.addEventListener('resize', measure);
    return () => window.removeEventListener('resize', measure);
  }, []);
  return shift;
}

/** Minimal single-bar HUD used when embedded inside the CONDUIT specification site (?embed=1). */
function EmbedHud() {
  const machine = useMachine();
  const { view, viewNonce, section, explode, selected, hovered, set } = useStudio();
  const chain = lineage(machine);
  const focusId = selected ?? hovered;
  const part = focusId ? machine.parts.find((p) => p.id === focusId) : undefined;
  const anno = focusId ? machine.annotations?.[focusId] : undefined;
  const childId = part ? machine.children?.[part.id] : undefined;
  const exploded = explode > 0.35;

  return (
    <>
      <nav className="embed-bar" aria-label="Plate controls" data-testid="embed-toolbar">
        {chain.length > 1 && (
          <button
            type="button"
            className="embed-btn"
            onClick={() => selectMachine(chain[chain.length - 2].id)}
            title="Return to parent assembly"
          >
            ‹ {chain[chain.length - 2].name}
          </button>
        )}
        <div className="embed-seg" role="group" aria-label="View mode">
          <button
            type="button"
            className={view === 'perspective' ? 'is-on' : ''}
            aria-pressed={view === 'perspective'}
            data-testid="embed-view-3d"
            onClick={() => set({ view: 'perspective', focus: null, viewNonce: viewNonce + 1 })}
          >
            3D
          </button>
          <button
            type="button"
            className={view === 'drawing' ? 'is-on' : ''}
            aria-pressed={view === 'drawing'}
            data-testid="embed-view-drawing"
            onClick={() => set({ view: 'drawing', focus: null, viewNonce: viewNonce + 1 })}
          >
            Drawing
          </button>
        </div>

        <button
          type="button"
          className={`embed-btn${section ? ' is-on' : ''}`}
          aria-pressed={section}
          data-testid="embed-toggle-section"
          onClick={() => set({ section: !section })}
        >
          Section
        </button>

        <button
          type="button"
          className={`embed-btn${exploded ? ' is-on' : ''}`}
          aria-pressed={exploded}
          data-testid="embed-toggle-explode"
          onClick={() => set({ explode: exploded ? 0 : 1, localExplode: null, deep: false })}
        >
          Explode
        </button>

        {(exploded || section || selected) && (
          <button
            type="button"
            className="embed-btn"
            onClick={() => {
              restoreAll(machine.steps[0]);
              useStudio.setState({ selected: null });
            }}
          >
            Reset
          </button>
        )}

        <a
          className="embed-link"
          href={`index.html#${machine.id}`}
          target="_blank"
          rel="noreferrer"
          title="Open full interactive studio"
        >
          Studio ↗
        </a>
      </nav>

      {part && (
        <div className="embed-readout" data-testid="embed-readout">
          <span>
            <strong>{String(part.index).padStart(2, '0')} {part.name}</strong>
            {anno ? ` · ${anno.label}` : ` · ${part.role}`}
            {childId && (
              <>
                {' · '}
                <button
                  type="button"
                  className="embed-sub-link"
                  onClick={() => selectMachine(childId)}
                >
                  Open {machineById(childId).name} ↘
                </button>
              </>
            )}
          </span>
        </div>
      )}
    </>
  );
}

export default function App() {
  const shift = useStageShift();
  useDeepLink();
  useFirstStep();
  const clear = useStudio((s) => s.set);
  const machine = useMachine();
  const { Model, Driver, Backdrop } = machine;
  const drawingMode = useStudio((s) => s.view === 'drawing');
  const moveMode = useStudio((s) => s.moveMode);
  const [recording, setRecording] = useState<number | null>(null);
  const [busy, setBusy] = useState(false);
  const onExport = async (kind: 'plate' | 'video' | 'json') => {
    if (busy) return;
    if (kind === 'json') return exportJson();
    setBusy(true);
    try {
      if (kind === 'plate') await exportPlate();
      else await recordTeardown(setRecording);
    } finally {
      setBusy(false);
      setRecording(null);
    }
  };
  return (
    <div className={`studio${drawingMode ? ' is-drawing' : ''}${isEmbed ? ' is-embed' : ''}`}>
      {!isEmbed && (
        <div className="paper-drawings" aria-hidden="true">
          {Backdrop && <Backdrop />}
        </div>
      )}
      <div className="stage">
        <Canvas
          camera={{ position: [5.5, 6.45, 11.85], fov: 30, near: 0.5, far: 200 }}
          dpr={[1, 2]}
          gl={{ antialias: false, alpha: true, preserveDrawingBuffer: true, toneMapping: THREE.NoToneMapping }}
          linear
          flat
          onPointerMissed={() => { if (useStudio.getState().view !== 'drawing') clear({ selected: null }); }}
        >
          <MotionDriver />
          {Driver && <Driver key={`driver-${machine.id}`} />}
          <group key={machine.id} name="machine-root" scale={machine.unit ?? 1}>
            <Model />
          </group>
          <Guides />
          <OrbitControls makeDefault enabled={!drawingMode} enablePan={false} minDistance={3} maxDistance={160} maxPolarAngle={Math.PI * 0.49} enableDamping dampingFactor={0.08} />
          <CameraRig shift={shift} />
          <InkRenderer />
          <ExportBridge />
          <DrawingRig />
        </Canvas>
        <DrawingSheet />
      </div>
      {isEmbed ? (
        <EmbedHud />
      ) : (
        <>
          <TitleColumn />
          <PlateMeta onExport={onExport} busy={busy} recording={recording} />
          <PartsLegend />
          <Catalogue />
          <Guide />
          <Tree />
          <p className="stage-hint">{drawingMode ? 'First-angle projection · hover or click a part to see its projections' : moveMode ? 'Drag a part to move it · drag empty space to rotate · resize once selected' : 'Drag to rotate · scroll to zoom · click a part'}</p>
        </>
      )}
    </div>
  );
}
