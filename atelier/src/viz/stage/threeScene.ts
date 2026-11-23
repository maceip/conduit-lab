import * as THREE from 'three';
import { OrbitControls } from 'three/examples/jsm/controls/OrbitControls.js';
import { BOARD } from '../../contract/tokens';
import { TRI_COLOR_FILL, type GcHeapEdge, type GcHeapObject, type TriColor } from './triColor';

/**
 * Tier 2 — plain-`three` tri-color GC heap.
 *
 * Why raw `three` and not `@react-three/fiber`: R3F v8 pins React 18 and the
 * atelier app is React 19 (spec 6.4). `three` is the only new runtime
 * dependency Phase 1 permits, and `OrbitControls` ships inside it at
 * `three/examples/jsm/controls/OrbitControls.js` — so orbit/pan/zoom costs
 * no extra dependency.
 *
 * The module owns no DOM outside the canvas it is handed. Everything it
 * creates — geometries, materials, the renderer, the controls, the window
 * resize listener — is released by `dispose()`.
 */

/** Edge length of one heap object box. */
const BOX_SIZE = 0.9;

/** Half the box edge, used when emitting the hairline box outline. */
const BOX_HALF = BOX_SIZE / 2;

export interface GcHeapSceneOptions {
  /**
   * Render one static frame and never start an animation loop. Set when the
   * visitor asked for reduced motion (spec 7).
   */
  reducedMotion?: boolean;
  /**
   * Optional DOM layer that receives the projected mono object labels. The
   * layer must be positioned over the canvas by the caller.
   */
  labelLayer?: HTMLElement | null;
}

export interface GcHeapSceneHandle {
  /**
   * Rebuild the heap. `violation` is the pointer to draw in `--fail`; pass
   * `null` when the heap respects the barrier.
   */
  update(objects: readonly GcHeapObject[], edges: readonly GcHeapEdge[], violation: { from: string; to: string } | null): void;
  /** Re-measure the canvas and re-render. */
  resize(): void;
  /** Release the renderer, the controls, every geometry, and every listener. */
  dispose(): void;
}

/** The twelve edge pairs of a unit box, as index pairs into the corner list. */
const BOX_EDGE_INDEX: ReadonlyArray<readonly [number, number]> = [
  [0, 1], [1, 2], [2, 3], [3, 0],
  [4, 5], [5, 6], [6, 7], [7, 4],
  [0, 4], [1, 5], [2, 6], [3, 7],
];

/** The eight corners of a box, in unit space. */
const BOX_CORNERS: ReadonlyArray<readonly [number, number, number]> = [
  [-1, -1, -1], [1, -1, -1], [1, 1, -1], [-1, 1, -1],
  [-1, -1, 1], [1, -1, 1], [1, 1, 1], [-1, 1, 1],
];

/**
 * Emit the twelve hairline edges of one box, centred on `centre`.
 * Returns a flat `[x0,y0,z0, x1,y1,z1, ...]` position list.
 */
function boxEdgePositions(
  centre: readonly [number, number, number],
  half: number,
): number[] {
  const positions: number[] = [];
  for (const pair of BOX_EDGE_INDEX) {
    const a = BOX_CORNERS[pair[0]];
    const b = BOX_CORNERS[pair[1]];
    if (!a || !b) continue;
    positions.push(
      a[0] * half + centre[0], a[1] * half + centre[1], a[2] * half + centre[2],
      b[0] * half + centre[0], b[1] * half + centre[1], b[2] * half + centre[2],
    );
  }
  return positions;
}

/**
 * Create the WebGL scene.
 *
 * Client-side only — the caller must not call this during SSR. `dispose()`
 * must be called on unmount.
 */
export function createGcHeapScene(
  canvas: HTMLCanvasElement,
  options: GcHeapSceneOptions = {},
): GcHeapSceneHandle {
  const reducedMotion = options.reducedMotion ?? false;
  const labelLayer = options.labelLayer ?? null;

  const renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: false });
  renderer.setPixelRatio(Math.min(globalThis.devicePixelRatio ?? 1, 2));
  renderer.setClearColor(BOARD.page, 1);
  // The drafting standard forbids drop shadows. Depth is carried by the face
  // shading ramp and the hairline outlines only.
  renderer.shadowMap.enabled = false;

  const scene = new THREE.Scene();
  scene.background = new THREE.Color(BOARD.page);

  const camera = new THREE.PerspectiveCamera(45, 1, 0.1, 500);
  camera.position.set(7.5, 6, 9.5);

  const controls = new OrbitControls(camera, canvas);
  controls.enableDamping = !reducedMotion;
  controls.dampingFactor = 0.08;
  controls.enablePan = true;
  controls.minDistance = 4;
  controls.maxDistance = 60;
  controls.target.set(0, 0.5, 0);
  controls.update();

  // Three lights only, no shadow casting: a cool ambient wash, a key from
  // above, and a cold rim so the silhouette of a black object still reads
  // against the `--page` ground.
  const ambient = new THREE.AmbientLight(BOARD.ink, 0.55);
  const key = new THREE.DirectionalLight(BOARD.inkHi, 1.15);
  key.position.set(6, 9, 7);
  const rim = new THREE.DirectionalLight(BOARD.edgeHi, 0.4);
  rim.position.set(-7, 3.5, -6);
  scene.add(ambient, key, rim);

  // A hairline floor grid gives the orbit a sense of place without adding
  // any fill that could read as a shadow.
  const grid = new THREE.GridHelper(26, 26, BOARD.rib, BOARD.rib);
  grid.material.transparent = true;
  grid.material.opacity = 0.5;
  scene.add(grid);

  const boxGeometry = new THREE.BoxGeometry(BOX_SIZE, BOX_SIZE, BOX_SIZE);
  const materials = new Map<TriColor, THREE.MeshStandardMaterial>();
  for (const color of ['white', 'grey', 'black'] as const) {
    materials.set(
      color,
      new THREE.MeshStandardMaterial({
        color: TRI_COLOR_FILL[color],
        roughness: 0.55,
        metalness: 0.05,
      }),
    );
  }

  const objectGroup = new THREE.Group();
  scene.add(objectGroup);

  const pointerMaterial = new THREE.LineBasicMaterial({ color: BOARD.line });
  const outlineMaterial = new THREE.LineBasicMaterial({ color: BOARD.rib });
  const violationMaterial = new THREE.LineBasicMaterial({ color: BOARD.fail });

  let objectMeshes: THREE.Mesh[] = [];
  let objectOutline: THREE.LineSegments | null = null;
  let pointerLines: THREE.LineSegments | null = null;
  let violationLines: THREE.LineSegments | null = null;

  const meshById = new Map<string, THREE.Mesh>();
  const labelById = new Map<string, HTMLSpanElement>();
  const projected = new THREE.Vector3();

  function clearLabels(): void {
    for (const element of labelById.values()) element.remove();
    labelById.clear();
  }

  function buildLabels(objects: readonly GcHeapObject[]): void {
    clearLabels();
    if (!labelLayer) return;
    for (const object of objects) {
      const element = document.createElement('span');
      element.className = 'stage-heap-label';
      element.textContent = object.id;
      // The scene owns the element's transform, so centring must use the
      // separate `translate` property. The label owns its own placement —
      // it must not depend on a stylesheet the component cannot see.
      element.style.position = 'absolute';
      element.style.top = '0';
      element.style.left = '0';
      element.style.translate = '-50% -50%';
      element.style.color = BOARD.ink;
      element.style.fontSize = '9px';
      element.style.letterSpacing = '0.06em';
      element.style.whiteSpace = 'nowrap';
      element.style.pointerEvents = 'none';
      labelLayer.appendChild(element);
      labelById.set(object.id, element);
    }
  }

  /** Project every object label onto the canvas and place it in the layer. */
  function updateLabels(): void {
    if (!labelLayer || labelById.size === 0) return;
    const canvasRect = canvas.getBoundingClientRect();
    const layerRect = labelLayer.getBoundingClientRect();
    const width = canvasRect.width;
    const height = canvasRect.height;
    if (width === 0 || height === 0) return;

    for (const [id, element] of labelById) {
      const mesh = meshById.get(id);
      if (!mesh) continue;
      projected.set(mesh.position.x, mesh.position.y + BOX_SIZE * 0.75, mesh.position.z);
      projected.project(camera);
      const x = layerRect.left - canvasRect.left + (projected.x * 0.5 + 0.5) * width;
      const y = layerRect.top - canvasRect.top + (-projected.y * 0.5 + 0.5) * height;
      // `project` puts anything behind the camera beyond the far plane.
      const behind = projected.z > 1;
      element.style.transform = `translate(${x.toFixed(1)}px, ${y.toFixed(1)}px)`;
      element.style.opacity = behind ? '0' : '1';
    }
  }

  function renderFrame(): void {
    controls.update();
    renderer.render(scene, camera);
    updateLabels();
  }

  function disposeGeometries(): void {
    if (objectOutline) {
      scene.remove(objectOutline);
      objectOutline.geometry.dispose();
    }
    if (pointerLines) {
      scene.remove(pointerLines);
      pointerLines.geometry.dispose();
    }
    if (violationLines) {
      scene.remove(violationLines);
      violationLines.geometry.dispose();
    }
    objectOutline = null;
    pointerLines = null;
    violationLines = null;
  }

  function update(
    objects: readonly GcHeapObject[],
    edges: readonly GcHeapEdge[],
    violation: { from: string; to: string } | null,
  ): void {
    // Rebuild the object set. The scene is designed for 10–40 objects, so a
    // full rebuild is cheaper to reason about than an incremental diff.
    for (const mesh of objectMeshes) objectGroup.remove(mesh);
    objectMeshes = [];
    meshById.clear();
    disposeGeometries();

    const outlinePositions: number[] = [];
    for (const object of objects) {
      const material = materials.get(object.color);
      if (!material) continue;
      const mesh = new THREE.Mesh(boxGeometry, material);
      mesh.position.set(object.position[0], object.position[1], object.position[2]);
      objectGroup.add(mesh);
      objectMeshes.push(mesh);
      meshById.set(object.id, mesh);
      outlinePositions.push(...boxEdgePositions(object.position, BOX_HALF));
    }

    if (outlinePositions.length > 0) {
      const geometry = new THREE.BufferGeometry();
      geometry.setAttribute(
        'position',
        new THREE.Float32BufferAttribute(outlinePositions, 3),
      );
      objectOutline = new THREE.LineSegments(geometry, outlineMaterial);
      scene.add(objectOutline);
    }

    const pointerPositions: number[] = [];
    const violationPositions: number[] = [];
    let violationDrawn = false;
    for (const edge of edges) {
      const from = meshById.get(edge.from);
      const to = meshById.get(edge.to);
      if (!from || !to) continue;
      const segment = [
        from.position.x, from.position.y, from.position.z,
        to.position.x, to.position.y, to.position.z,
      ];
      const isViolation =
        violation !== null && violation.from === edge.from && violation.to === edge.to;
      if (isViolation) {
        violationPositions.push(...segment);
        violationDrawn = true;
      } else {
        pointerPositions.push(...segment);
      }
    }

    // A violation reported for a pointer that is not in the edge list still
    // has to be visible, so it is drawn on its own.
    if (violation !== null && !violationDrawn) {
      const from = meshById.get(violation.from);
      const to = meshById.get(violation.to);
      if (from && to) {
        violationPositions.push(
          from.position.x, from.position.y, from.position.z,
          to.position.x, to.position.y, to.position.z,
        );
      }
    }

    if (pointerPositions.length > 0) {
      const geometry = new THREE.BufferGeometry();
      geometry.setAttribute('position', new THREE.Float32BufferAttribute(pointerPositions, 3));
      pointerLines = new THREE.LineSegments(geometry, pointerMaterial);
      scene.add(pointerLines);
    }

    if (violationPositions.length > 0) {
      const geometry = new THREE.BufferGeometry();
      geometry.setAttribute(
        'position',
        new THREE.Float32BufferAttribute(violationPositions, 3),
      );
      violationLines = new THREE.LineSegments(geometry, violationMaterial);
      scene.add(violationLines);
    }

    buildLabels(objects);
    renderFrame();
  }

  function resize(): void {
    const width = canvas.clientWidth || canvas.width || 1;
    const height = canvas.clientHeight || canvas.height || 1;
    renderer.setSize(width, height, false);
    camera.aspect = width / height;
    camera.updateProjectionMatrix();
    renderFrame();
  }

  function onWindowResize(): void {
    resize();
  }

  window.addEventListener('resize', onWindowResize);

  if (reducedMotion) {
    // One static frame. No animation loop is ever started.
    resize();
  } else {
    renderer.setAnimationLoop(renderFrame);
    resize();
  }

  function dispose(): void {
    window.removeEventListener('resize', onWindowResize);
    renderer.setAnimationLoop(null);
    controls.dispose();
    for (const mesh of objectMeshes) objectGroup.remove(mesh);
    objectMeshes = [];
    meshById.clear();
    disposeGeometries();
    clearLabels();
    boxGeometry.dispose();
    for (const material of materials.values()) material.dispose();
    pointerMaterial.dispose();
    outlineMaterial.dispose();
    violationMaterial.dispose();
    grid.geometry.dispose();
    grid.material.dispose();
    renderer.dispose();
  }

  return { update, resize, dispose };
}
