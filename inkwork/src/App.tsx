import { useEffect, useRef, useState } from 'react';
import { Canvas, useFrame, useThree } from '@react-three/fiber';
import { OrbitControls } from '@react-three/drei';
import * as THREE from 'three';
import { Catalogue } from './components/Catalogue';
import { Guide } from './components/Guide';
import { Tree } from './components/Tree';
import { PartsLegend, PlateMeta, TitleColumn } from './components/Plate';
import { currentMachine, hasMachine, lineage, machineById, useMachine } from './machines';
import { CameraRig, Guides, InkRenderer, MotionDriver } from './scene';
import { AmbientWorld } from './scene/AmbientWorld';
import { SECTION_PLANE } from './scene/Part';
import { TP } from './machines/turboprop/data';
import { isAmbient, isEmbed, restoreAll, selectMachine, useStudio } from './state';
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
    // Support initial ?preset=section|exploded|drawing on embedded plates
    const preset = isEmbed ? new URLSearchParams(window.location.search).get('preset') : null;
    set({
      section: preset === 'assembled' || preset === 'exploded' ? false : preset === 'section' || preset === 'drawing' ? true : first.state.section,
      explode: preset === 'exploded' ? 1 : 0,
      view: preset === 'drawing' ? 'drawing' : 'perspective',
      running: first.state.running,
      focus: first.state.focus,
      selected: isEmbed ? null : (selected ?? first.state.select),
    });
  }, [machine]);
}

/** Listen to parent CONDUIT plate header & legend controls via postMessage, and broadcast active part back. */
function useParentPlateControl() {
  useEffect(() => {
    if (!isEmbed) return;
    const onMsg = (ev: MessageEvent) => {
      const data = ev.data as { type?: string; preset?: string; partId?: string | null } | null;
      if (!data) return;
      if (data.type === 'conduit-plate-state') {
        const machine = currentMachine();
        const { viewNonce, set } = useStudio.getState();
        if (data.preset === 'assembled') {
          restoreAll(machine.steps[0]);
          useStudio.setState({ selected: null, view: 'perspective', section: false, explode: 0, viewNonce: viewNonce + 1 });
        } else if (data.preset === 'section') {
          set({ view: 'perspective', section: true, explode: 0, localExplode: null, deep: false, focus: null, viewNonce: viewNonce + 1 });
        } else if (data.preset === 'exploded') {
          set({ view: 'perspective', section: false, explode: 1, localExplode: null, deep: false, focus: null, viewNonce: viewNonce + 1 });
        } else if (data.preset === 'drawing') {
          set({ view: 'drawing', section: true, explode: 0, localExplode: null, deep: false, focus: null, viewNonce: viewNonce + 1 });
        }
      } else if (data.type === 'conduit-select-part') {
        const cur = useStudio.getState().selected;
        const next = data.partId && cur !== data.partId ? data.partId : null;
        useStudio.getState().set({ selected: next });
      } else if (data.type === 'conduit-hover-part') {
        useStudio.getState().set({ hovered: data.partId ?? null });
      }
    };
    window.addEventListener('message', onMsg);

    const unsub = useStudio.subscribe((s, prev) => {
      const activeId = s.hovered ?? s.selected;
      const prevId = prev.hovered ?? prev.selected;
      if (activeId === prevId && s.machineId === prev.machineId) return;
      const m = currentMachine();
      const part = activeId ? m.parts.find((p) => p.id === activeId) : undefined;
      const anno = activeId ? m.annotations?.[activeId] : undefined;
      window.parent?.postMessage(
        {
          type: 'conduit-active-part',
          machineId: m.id,
          partId: activeId ?? null,
          selectedId: s.selected ?? null,
          index: part?.index ?? null,
          name: part?.name ?? null,
          role: part?.role ?? null,
          material: part?.material ?? null,
          counterpart: anno?.label ?? null,
        },
        '*',
      );
    });

    return () => {
      window.removeEventListener('message', onMsg);
      unsub();
    };
  }, []);
}

const VIA_P0 = new THREE.Vector3(-24.9, 0, -7.7);
const VIA_NORMAL = new THREE.Vector3(0.979, 0, 0.201).normalize();
const ambientLayout = { modalRightRatio: null as number | null };
const ambHubWorld = new THREE.Vector3();
const ambRayPerZ = new THREE.Vector3();
const ambScratch = new THREE.Vector3();

function fallbackModalRightPx(w: number): number {
  if (w < 680) return w - 16;
  const pad = w <= 760 ? 16 : 28;
  const innerLeft = pad + Math.max(0, (w - pad * 2 - 1420) * 0.5);
  const glassW = Math.min(575, w - pad * 2 - 235);
  return innerLeft + Math.max(240, glassW);
}

/**
 * Anchors `machine-root` in ambient hero mode so the propeller (TP.hubX, TP.AY)
 * always sits horizontally in the open gap between `.ch-hero-glass`'s right edge
 * and the right edge of the page, while staying strictly behind the diagonal Maglev rail.
 */
function AmbientTurbopropRig({ rootRef }: { rootRef: React.RefObject<THREE.Group | null> }) {
  const { camera, size } = useThree() as unknown as {
    camera: THREE.PerspectiveCamera;
    size: { width: number; height: number };
  };

  useEffect(() => {
    const onMsg = (ev: MessageEvent) => {
      const data = ev.data as { type?: string; modalRightRatio?: number } | null;
      if (data?.type === 'conduit-hero-layout' && typeof data.modalRightRatio === 'number') {
        ambientLayout.modalRightRatio = data.modalRightRatio;
      }
    };
    window.addEventListener('message', onMsg);
    return () => window.removeEventListener('message', onMsg);
  }, []);

  useFrame(() => {
    const root = rootRef.current;
    if (!root || size.width <= 0 || size.height <= 0) return;

    camera.updateMatrixWorld();
    const w = size.width;
    const h = size.height;
    const modalRightPx =
      ambientLayout.modalRightRatio !== null
        ? ambientLayout.modalRightRatio * w
        : fallbackModalRightPx(w);
    const gapPx = w - modalRightPx;

    let targetPropPx: number;
    let targetDiamPx: number;
    if (gapPx >= 110) {
      // Place propeller hub squarely inside [modalRightPx, w] so the entire spinning
      // propeller stays between the modal edge and page edge while the aft core blurs under the modal.
      targetDiamPx = THREE.MathUtils.clamp(gapPx * 0.86, 150, 278);
      const rightReachPx = 0.34 * targetDiamPx;
      const leftClearPx = 0.33 * targetDiamPx;
      const minHubPx = modalRightPx + leftClearPx + 14;
      const maxHubPx = w - rightReachPx - 16;
      const idealHubPx = modalRightPx + Math.min(192, gapPx * 0.54);
      targetPropPx = maxHubPx >= minHubPx ? THREE.MathUtils.clamp(idealHubPx, minHubPx, maxHubPx) : modalRightPx + gapPx * 0.53;
    } else {
      // Narrow phone fallback where modal spans full width
      targetDiamPx = Math.min(h * 0.48, 210);
      targetPropPx = w * 0.72;
    }

    const targetPropPy = h * 0.55;
    const ndcX = (targetPropPx / w) * 2 - 1;
    const ndcY = 1 - (targetPropPy / h) * 2;
    const tanHalfFov = Math.tan(THREE.MathUtils.degToRad(camera.fov * 0.5));
    const aspect = w / h;

    // Direction vector in world space per +1 unit of view-space depth Z_view
    ambRayPerZ
      .set(ndcX * tanHalfFov * aspect, ndcY * tanHalfFov, -1)
      .transformDirection(camera.matrixWorld)
      .multiplyScalar(Math.hypot(ndcX * tanHalfFov * aspect, ndcY * tanHalfFov, 1));

    // Exact Z_view of the Maglev viaduct plane along this pixel ray, plus +7.6 clearance behind the rail
    const numer = ambScratch.copy(VIA_P0).sub(camera.position).dot(VIA_NORMAL);
    const denom = ambRayPerZ.dot(VIA_NORMAL);
    const railZView = Math.abs(denom) > 1e-4 ? numer / denom : 46;
    const zView = THREE.MathUtils.clamp(railZView + 7.6, 36, 76);

    // Exact 3D world point projecting to (targetPropPx, targetPropPy) at depth zView
    ambHubWorld
      .set(ndcX * zView * tanHalfFov * aspect, ndcY * zView * tanHalfFov, -zView)
      .applyMatrix4(camera.matrixWorld);

    // Scale S (world units per mm) so 2 * TP.propR (2160 mm) spans targetDiamPx vertically
    const scalePerMm = ((targetDiamPx / h) * (2 * zView * tanHalfFov)) / (2 * TP.propR);
    root.scale.setScalar(scalePerMm);
    root.position.set(
      ambHubWorld.x - TP.hubX * scalePerMm,
      ambHubWorld.y - TP.AY * scalePerMm,
      ambHubWorld.z,
    );
    root.updateMatrixWorld();

    if (useStudio.getState().section) {
      SECTION_PLANE.constant = root.position.z;
    }

    (window as unknown as { __conduitPropDebug?: unknown }).__conduitPropDebug = {
      modalRightPx,
      targetPropPx,
      pageWidth: w,
      targetDiamPx,
      railZView,
      zView,
    };
  }, 0);

  return null;
}

/** Horizontal offset (px) of the projection centre: shifts standalone studio machine beside its text column. */
function useStageShift() {
  const [shift, setShift] = useState(0);
  useEffect(() => {
    if (isAmbient) {
      document.documentElement.dataset.ambient = '1';
      setShift(0);
      return;
    }
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

/** Sub-assembly navigation pill in embedded plates (active part specs live in parent PlateFrame footer). */
function EmbedHud() {
  const machine = useMachine();
  const { selected } = useStudio();
  const chain = lineage(machine);
  const part = selected ? machine.parts.find((p) => p.id === selected) : undefined;
  const childId = part ? machine.children?.[part.id] : undefined;

  if (chain.length <= 1 && !childId) return null;

  return (
    <div className="embed-readout" data-testid="embed-readout">
      <span>
        {chain.length > 1 && (
          <button
            type="button"
            className="embed-sub-link"
            onClick={() => selectMachine(chain[chain.length - 2].id)}
          >
            ‹ Back to {chain[chain.length - 2].name}
          </button>
        )}
        {chain.length > 1 && childId ? ' · ' : ''}
        {childId && (
          <button
            type="button"
            className="embed-sub-link"
            onClick={() => selectMachine(childId)}
          >
            Inspect {machineById(childId).name} sub-assembly ↘
          </button>
        )}
      </span>
    </div>
  );
}

export default function App() {
  const shift = useStageShift();
  useDeepLink();
  useFirstStep();
  useParentPlateControl();
  const clear = useStudio((s) => s.set);
  const machine = useMachine();
  const { Model, Driver, Backdrop } = machine;
  const drawingMode = useStudio((s) => s.view === 'drawing');
  const moveMode = useStudio((s) => s.moveMode);
  const rootRef = useRef<THREE.Group>(null);
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
    <div className={`studio${drawingMode ? ' is-drawing' : ''}${isEmbed ? ' is-embed' : ''}${isAmbient ? ' is-ambient' : ''}`}>
      {!isEmbed && (
        <div className="paper-drawings" aria-hidden="true">
          {Backdrop && <Backdrop />}
        </div>
      )}
      <div className="stage">
        <Canvas
          camera={{ position: [5.5, 6.45, 11.85], fov: 30, near: 0.5, far: 320 }}
          dpr={[1, 2]}
          gl={{ antialias: false, alpha: true, preserveDrawingBuffer: true, toneMapping: THREE.NoToneMapping }}
          linear
          flat
          onPointerMissed={() => { if (useStudio.getState().view !== 'drawing') clear({ selected: null }); }}
        >
          <MotionDriver />
          {Driver && <Driver key={`driver-${machine.id}`} />}
          <group
            ref={rootRef}
            key={machine.id}
            name="machine-root"
            scale={machine.unit ?? 1}
          >
            <Model />
          </group>
          {isAmbient && <AmbientWorld />}
          {!isAmbient && <Guides />}
          <OrbitControls makeDefault enabled={!drawingMode && !isAmbient} enablePan={false} minDistance={3} maxDistance={160} maxPolarAngle={Math.PI * 0.49} enableDamping dampingFactor={0.08} />
          <CameraRig shift={shift} />
          {isAmbient && <AmbientTurbopropRig rootRef={rootRef} />}
          <InkRenderer />
          <ExportBridge />
          <DrawingRig />
        </Canvas>
        <DrawingSheet />
      </div>
      {isAmbient ? null : isEmbed ? (
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
