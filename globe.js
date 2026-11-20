/* CONDUIT Lab — Nanvix × Verus verification topology */
(function () {
  'use strict';

  var stage = document.getElementById('stage');
  var canvas = document.getElementById('globe');
  var leaders = document.getElementById('leaders');
  var ringsSvg = document.getElementById('rings');
  var calloutLayer = document.getElementById('callouts');

  var COMPONENTS = [
    { name: 'Microkernel / HAL', status: 'verified', lat: 25, lon: 20,
      desc: 'Guest-side thin kernel and hardware abstraction. Address-frame proofs live here.',
      path: 'src/kernel/src/hal/mem/types/address/frame.proof.rs' },
    { name: 'Memory Manager', status: 'verified', lat: -15, lon: 65,
      desc: 'Kernel heap and physical frame management with Verus-checked invariants.',
      path: 'src/kernel/src/mm/kheap.proof.rs' },
    { name: 'Bitmap Allocator', status: 'verified', lat: 50, lon: -25,
      desc: 'Bitmap primitive with machine-checked specification and proof.',
      path: 'src/libs/bitmap/src/lib.proof.rs' },
    { name: 'Slab Allocator', status: 'verified', lat: -40, lon: -70,
      desc: 'Fixed-size object allocator carrying a Verus proof of its core operations.',
      path: 'src/libs/slab/src/lib.proof.rs' },
    { name: 'x86 Paging', status: 'verified', lat: 65, lon: -120,
      desc: 'Frame-number arithmetic in the x86 paging path, formally verified.',
      path: 'src/libs/arch/src/x86/mem/paging/frame/number.proof.rs' },
    { name: 'Irrigation Controller', status: 'verified', lat: 5, lon: 150,
      desc: 'CONDUIT guest with a Verus-verified core, carried on the conduit-irrigation branch.',
      path: 'src/user/irrigation-controller' },
    { name: 'IPC / Rendezvous', status: 'spec', lat: -55, lon: 110,
      desc: 'Guest and host message channels. Specification present, proofs pending.',
      path: 'src/kernel/src/ipc/rendezvous.rs' },
    { name: 'Process Manager', status: 'spec', lat: 35, lon: -165,
      desc: 'Thread and process lifecycle. Core subsystem, not yet under formal specification.',
      path: 'src/kernel/src/pm/mod.rs' },
    { name: 'raw-array', status: 'spec', lat: -10, lon: -110,
      desc: 'Low-level array abstraction with a Verus specification only.',
      path: 'src/libs/raw-array/src/lib.spec.rs' },
    { name: 'Browser Engine', status: 'active', lat: -30, lon: 180,
      desc: 'Parawing browser core being brought into the Nanvix sandbox. Active verification frontier.',
      path: 'maceip/parawing · packages/core' }
  ];

  var STATUS = {
    verified: { hex: 0x45e0ff, css: '#45e0ff', label: 'VERIFIED' },
    spec: { hex: 0xf0a63c, css: '#f0a63c', label: 'SPECIFIED' },
    active: { hex: 0xb14dff, css: '#b14dff', label: 'IN PROGRESS' }
  };

  var R = 1.22;
  var scene, camera, renderer, globeGroup, islands = [], activeHalo;
  var dragging = false, lastX = 0, lastY = 0, velX = 0.0009, velY = 0;
  var selected = 9;
  var W = 0, H = 0, CX = 0, CY = 0;
  var raycaster = new THREE.Raycaster();
  var pointer = new THREE.Vector2();

  function latLonToVec3(lat, lon, r) {
    var phi = (90 - lat) * Math.PI / 180;
    var theta = (lon + 180) * Math.PI / 180;
    return new THREE.Vector3(
      -r * Math.sin(phi) * Math.cos(theta),
      r * Math.cos(phi),
      r * Math.sin(phi) * Math.sin(theta)
    );
  }

  function islandShape(seed, radius) {
    var shape = new THREE.Shape();
    var n = 11;
    for (var i = 0; i < n; i++) {
      var a = i / n * Math.PI * 2;
      var wobble = 0.70 + 0.34 * Math.abs(Math.sin(seed * 4.13 + i * 2.37));
      var rr = radius * wobble;
      var x = Math.cos(a) * rr;
      var y = Math.sin(a) * rr * 0.72;
      if (i === 0) shape.moveTo(x, y); else shape.lineTo(x, y);
    }
    shape.closePath();
    return shape;
  }

  function buildScene() {
    scene = new THREE.Scene();
    camera = new THREE.PerspectiveCamera(42, W / H, 0.1, 100);
    camera.position.set(0, 0, 4.35);

    renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true, alpha: true });
    renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
    renderer.setClearColor(0x000000, 0);

    scene.add(new THREE.AmbientLight(0x6688bb, 1.5));
    var key = new THREE.DirectionalLight(0x9fd8ff, 1.5);
    key.position.set(3, 2, 4);
    scene.add(key);

    globeGroup = new THREE.Group();
    globeGroup.rotation.x = 0.18;
    globeGroup.rotation.y = 0.32;
    scene.add(globeGroup);

    var globe = new THREE.Mesh(
      new THREE.SphereGeometry(R, 64, 48),
      new THREE.MeshPhongMaterial({ color: 0x0b1730, emissive: 0x050b18, shininess: 22, specular: 0x244a72 })
    );
    globeGroup.add(globe);

    var grid = new THREE.LineSegments(
      new THREE.WireframeGeometry(new THREE.SphereGeometry(R * 1.003, 32, 20)),
      new THREE.LineBasicMaterial({ color: 0x24456b, transparent: true, opacity: 0.24 })
    );
    globeGroup.add(grid);

    var atmosphere = new THREE.Mesh(
      new THREE.SphereGeometry(R * 1.18, 48, 32),
      new THREE.MeshBasicMaterial({ color: 0x6a35a8, side: THREE.BackSide, transparent: true,
        opacity: 0.085, blending: THREE.AdditiveBlending, depthWrite: false })
    );
    scene.add(atmosphere);

    COMPONENTS.forEach(function (c, idx) {
      var normal = latLonToVec3(c.lat, c.lon, 1).normalize();
      var radius = c.status === 'active' ? 0.17 : 0.125;
      var shape = islandShape(idx + 1, radius);
      var geo = new THREE.ShapeGeometry(shape, 18);
      var color = STATUS[c.status].hex;
      var mesh = new THREE.Mesh(geo, new THREE.MeshBasicMaterial({
        color: color, transparent: true, opacity: c.status === 'active' ? 0.42 : 0.60,
        side: THREE.DoubleSide, depthWrite: false
      }));
      mesh.position.copy(normal.clone().multiplyScalar(R * 1.014));
      mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 0, 1), normal);
      mesh.userData.index = idx;
      globeGroup.add(mesh);

      var pts = shape.getPoints(40).map(function (p) { return new THREE.Vector3(p.x, p.y, 0.002); });
      var outline = new THREE.LineLoop(
        new THREE.BufferGeometry().setFromPoints(pts),
        new THREE.LineBasicMaterial({ color: color, transparent: true,
          opacity: c.status === 'active' ? 1 : 0.85 })
      );
      outline.position.copy(mesh.position);
      outline.quaternion.copy(mesh.quaternion);
      globeGroup.add(outline);

      if (c.status === 'active') {
        var halo = new THREE.Mesh(
          new THREE.RingGeometry(radius * 1.22, radius * 1.38, 64),
          new THREE.MeshBasicMaterial({ color: 0xb14dff, side: THREE.DoubleSide,
            transparent: true, opacity: 0.9, blending: THREE.AdditiveBlending, depthWrite: false })
        );
        halo.position.copy(mesh.position);
        halo.quaternion.copy(mesh.quaternion);
        globeGroup.add(halo);
        activeHalo = halo;
      }

      islands.push({ mesh: mesh, outline: outline, normal: normal, component: c });
    });

    // Bring the active frontier island (browser engine) to the camera on load.
    var activeNormal = islands[9].normal;
    globeGroup.rotation.y = -Math.atan2(activeNormal.x, activeNormal.z);
  }

  function buildRings() {
    ringsSvg.innerHTML = '';
    var cx = W / 2, cy = H / 2;
    var base = Math.min(W, H);
    var ns = 'http://www.w3.org/2000/svg';
    var group = document.createElementNS(ns, 'g');

    [0.30, 0.365, 0.43, 0.485].forEach(function (frac, i) {
      var circle = document.createElementNS(ns, 'circle');
      circle.setAttribute('cx', cx); circle.setAttribute('cy', cy);
      circle.setAttribute('r', base * frac);
      circle.setAttribute('fill', 'none');
      circle.setAttribute('stroke', i === 2 ? '#6d3aa8' : '#1c3352');
      circle.setAttribute('stroke-width', i === 2 ? '1.2' : '0.8');
      circle.setAttribute('stroke-dasharray', i % 2 ? '2 7' : '1 5');
      circle.setAttribute('opacity', i === 2 ? '0.75' : '0.75');
      group.appendChild(circle);
    });

    var sweep = document.createElementNS(ns, 'circle');
    sweep.setAttribute('cx', cx); sweep.setAttribute('cy', cy);
    sweep.setAttribute('r', base * 0.43);
    sweep.setAttribute('fill', 'none');
    sweep.setAttribute('stroke', '#b14dff');
    sweep.setAttribute('stroke-width', '1.6');
    sweep.setAttribute('stroke-dasharray', '54 620');
    sweep.setAttribute('opacity', '0.85');
    sweep.style.transformOrigin = cx + 'px ' + cy + 'px';
    sweep.style.animation = 'spin 22s linear infinite';
    group.appendChild(sweep);

    for (var i = 0; i < 120; i++) {
      var a = i / 120 * Math.PI * 2;
      var inner = base * 0.485, outer = inner + (i % 10 === 0 ? 9 : 4);
      var tick = document.createElementNS(ns, 'line');
      tick.setAttribute('x1', cx + Math.cos(a) * inner);
      tick.setAttribute('y1', cy + Math.sin(a) * inner);
      tick.setAttribute('x2', cx + Math.cos(a) * outer);
      tick.setAttribute('y2', cy + Math.sin(a) * outer);
      tick.setAttribute('stroke', i % 10 === 0 ? '#3976a0' : '#1e3b5a');
      tick.setAttribute('stroke-width', i % 10 === 0 ? '1.2' : '0.7');
      group.appendChild(tick);
    }

    for (var k = 0; k < 18; k++) {
      var ang = k / 18 * Math.PI * 2;
      var node = document.createElementNS(ns, 'circle');
      node.setAttribute('cx', cx + Math.cos(ang) * base * 0.365);
      node.setAttribute('cy', cy + Math.sin(ang) * base * 0.365);
      node.setAttribute('r', k % 3 === 0 ? 2.4 : 1.4);
      node.setAttribute('fill', k % 3 === 0 ? '#45e0ff' : '#5886b5');
      node.setAttribute('opacity', '0.8');
      node.style.animation = 'pulse ' + (2 + (k % 5) * 0.6) + 's ease-in-out infinite';
      group.appendChild(node);
    }

    ringsSvg.appendChild(group);
  }

  var CALLOUT_ANGLES = [100, 128, 156, 183, 211, 239, 267, 294, 322, 350];

  function buildCallouts() {
    calloutLayer.innerHTML = '';
    leaders.innerHTML = '';
    COMPONENTS.forEach(function (c, i) {
      var el = document.createElement('div');
      el.className = 'callout ' + c.status + (i === selected ? ' selected' : '');
      el.innerHTML = '<b>' + c.name + '</b><small>' + STATUS[c.status].label + '</small>';
      el.addEventListener('click', function () { select(i); });
      calloutLayer.appendChild(el);
      c.el = el;

      var line = document.createElementNS('http://www.w3.org/2000/svg', 'line');
      line.setAttribute('stroke', STATUS[c.status].css);
      line.setAttribute('stroke-width', '0.8');
      line.setAttribute('opacity', '0.55');
      leaders.appendChild(line);
      c.line = line;

      var dot = document.createElementNS('http://www.w3.org/2000/svg', 'circle');
      dot.setAttribute('r', '2.6');
      dot.setAttribute('fill', STATUS[c.status].css);
      leaders.appendChild(dot);
      c.dot = dot;
    });
  }

  function select(i) {
    selected = i;
    var c = COMPONENTS[i];
    COMPONENTS.forEach(function (x, j) { x.el.classList.toggle('selected', j === i); });
    document.getElementById('dKicker').textContent = c.status === 'active' ? 'ACTIVE FRONTIER'
      : c.status === 'verified' ? 'VERIFIED TERRITORY' : 'SPECIFIED TERRITORY';
    document.getElementById('dName').textContent = c.name;
    var st = document.getElementById('dStatus');
    st.textContent = STATUS[c.status].label;
    st.className = 'detail-status ' + (c.status === 'verified' ? 'verified' : c.status === 'spec' ? 'spec' : '');
    st.style.borderColor = STATUS[c.status].css;
    st.style.color = STATUS[c.status].css;
    document.getElementById('dDesc').textContent = c.desc;
    document.getElementById('dPath').textContent = c.path;
  }

  function updateOverlay() {
    var base = Math.min(W, H);
    var radius = base * 0.345;
    var camDir = new THREE.Vector3(0, 0, 1);

    islands.forEach(function (item, i) {
      var a = CALLOUT_ANGLES[i] * Math.PI / 180;
      var lx = W / 2 + Math.cos(a) * radius;
      var ly = H / 2 + Math.sin(a) * radius;
      item.component.el.style.left = lx + 'px';
      item.component.el.style.top = ly + 'px';

      var world = item.normal.clone().applyQuaternion(globeGroup.quaternion);
      var facing = world.dot(camDir);
      var proj = item.normal.clone().applyQuaternion(globeGroup.quaternion)
        .multiplyScalar(R * 1.02).project(camera);
      var px = (proj.x * 0.5 + 0.5) * W;
      var py = (-proj.y * 0.5 + 0.5) * H;

      var c = item.component;
      var vis = facing > 0 ? 1 : 0.18;
      c.el.style.opacity = 0.35 + 0.65 * vis;
      c.line.setAttribute('x1', lx); c.line.setAttribute('y1', ly);
      c.line.setAttribute('x2', px); c.line.setAttribute('y2', py);
      c.line.setAttribute('opacity', (facing > 0 ? 0.5 : 0.045).toString());
      c.dot.setAttribute('cx', px); c.dot.setAttribute('cy', py);
      c.dot.setAttribute('opacity', (facing > 0 ? 1 : 0.05).toString());
    });
  }

  function resize() {
    var rect = stage.getBoundingClientRect();
    W = stage.clientWidth;
    H = Math.min(stage.clientHeight, canvas.clientHeight || stage.clientHeight);
    if (window.innerWidth <= 900) H = canvas.clientHeight || 560;
    CX = W / 2; CY = H / 2;
    renderer.setSize(W, H, false);
    camera.aspect = W / H;
    camera.updateProjectionMatrix();
    ringsSvg.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    leaders.setAttribute('viewBox', '0 0 ' + W + ' ' + H);
    buildRings();
  }

  function animate(t) {
    requestAnimationFrame(animate);
    if (!dragging) {
      globeGroup.rotation.y += velX;
      velX += (0.0022 - velX) * 0.02;
      globeGroup.rotation.x += velY;
      velY *= 0.94;
      globeGroup.rotation.x = Math.max(-0.7, Math.min(0.7, globeGroup.rotation.x));
    }
    if (activeHalo) {
      var s = 1 + 0.10 * Math.sin(t * 0.003);
      activeHalo.scale.set(s, s, s);
      activeHalo.material.opacity = 0.55 + 0.45 * Math.abs(Math.sin(t * 0.002));
    }
    renderer.render(scene, camera);
    updateOverlay();
  }

  canvas.addEventListener('pointerdown', function (e) {
    dragging = true; lastX = e.clientX; lastY = e.clientY;
    canvas.setPointerCapture(e.pointerId);
  });
  canvas.addEventListener('pointermove', function (e) {
    if (!dragging) return;
    var dx = e.clientX - lastX, dy = e.clientY - lastY;
    velX = dx * 0.005; velY = dy * 0.004;
    globeGroup.rotation.y += velX;
    globeGroup.rotation.x += velY;
    globeGroup.rotation.x = Math.max(-0.7, Math.min(0.7, globeGroup.rotation.x));
    lastX = e.clientX; lastY = e.clientY;
  });
  canvas.addEventListener('pointerup', function (e) {
    dragging = false;
    if (Math.abs(velX) + Math.abs(velY) < 0.001) { velX = 0.0022; }
    try { canvas.releasePointerCapture(e.pointerId); } catch (err) {}
  });
  canvas.addEventListener('click', function (e) {
    var rect = canvas.getBoundingClientRect();
    pointer.x = ((e.clientX - rect.left) / rect.width) * 2 - 1;
    pointer.y = -((e.clientY - rect.top) / rect.height) * 2 + 1;
    raycaster.setFromCamera(pointer, camera);
    var hits = raycaster.intersectObjects(islands.map(function (i) { return i.mesh; }));
    if (hits.length) select(hits[0].object.userData.index);
  });

  window.addEventListener('resize', resize);

  buildScene();
  resize();
  buildCallouts();
  select(selected);
  requestAnimationFrame(animate);
})();
