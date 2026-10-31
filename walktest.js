// "Walk as Schiffy" + automatic door walk test for viewer.html (three.js r128).
// Uses the viewer's globals: THREE, scene, camera, controls, renderer, sun, root, inkMat, matCache, grad, info.
// Collision: per-geometry triangle grids (local space, xz columns, built lazily and shared by every instance of a mesh)
// + a world grid of mesh boxes. The body is one sphere (r 0.35) whose bottom sits at the step height (0.3 m), so
// anything lower is a step (ground rays snap up onto it) and anything taller is a wall.
(function () {
'use strict';
const V3 = THREE.Vector3;
const P = { r: 0.35, h: 0.9, speed: 5, jump: 7, g: 24, step: 0.3, slopeCos: Math.cos(35 * Math.PI / 180), dt: 1 / 60, cell: 24 };
const SKIP_NAME = /canopy|spore|weeds|grass|flower|fairyring|reed|lilypad/i;   // leaf crowns, floaty bits, tiny decor
const W = window.walk = { active: false, P };

// ---------------------------------------------------------------- triangle grid per geometry (local space)
const geoCache = new Map();
function denorm(a) {
  if (a instanceof Int8Array) return 1 / 127; if (a instanceof Uint8Array) return 1 / 255;
  if (a instanceof Int16Array) return 1 / 32767; if (a instanceof Uint16Array) return 1 / 65535; return 1;
}
function geoGrid(geo) {
  let G = geoCache.get(geo.uuid); if (G) return G;
  const pa = geo.attributes.position, n = pa.count;
  const k = pa.normalized ? denorm(pa.isInterleavedBufferAttribute ? pa.data.array : pa.array) : 1;   // r128 getX() does not dequantize
  const pos = new Float32Array(n * 3);
  let minx = Infinity, minz = Infinity, maxx = -Infinity, maxz = -Infinity;
  for (let i = 0; i < n; i++) {
    const x = pa.getX(i) * k, y = pa.getY(i) * k, z = pa.getZ(i) * k;
    pos[i * 3] = x; pos[i * 3 + 1] = y; pos[i * 3 + 2] = z;
    if (x < minx) minx = x; if (x > maxx) maxx = x; if (z < minz) minz = z; if (z > maxz) maxz = z;
  }
  const idx = geo.index ? geo.index.array : null, tc = idx ? (idx.length / 3) | 0 : (n / 3) | 0;
  const tri = new Uint32Array(tc * 3);
  for (let i = 0; i < tc * 3; i++) tri[i] = idx ? idx[i] : i;
  let cs = Math.max(0.5, Math.sqrt(Math.max(1e-6, (maxx - minx) * (maxz - minz)) / Math.max(1, tc / 6)));
  let nx, nz;
  for (;;) { nx = Math.floor((maxx - minx) / cs) + 1; nz = Math.floor((maxz - minz) / cs) + 1; if (nx * nz <= 262144) break; cs *= 1.5; }
  const cnt = new Uint32Array(nx * nz + 1), rng = new Int32Array(tc * 4);
  for (let t = 0; t < tc; t++) {
    const a = tri[t * 3] * 3, b = tri[t * 3 + 1] * 3, c = tri[t * 3 + 2] * 3;
    const x0 = Math.min(pos[a], pos[b], pos[c]), x1 = Math.max(pos[a], pos[b], pos[c]);
    const z0 = Math.min(pos[a + 2], pos[b + 2], pos[c + 2]), z1 = Math.max(pos[a + 2], pos[b + 2], pos[c + 2]);
    const i0 = Math.floor((x0 - minx) / cs), i1 = Math.floor((x1 - minx) / cs), j0 = Math.floor((z0 - minz) / cs), j1 = Math.floor((z1 - minz) / cs);
    rng[t * 4] = i0; rng[t * 4 + 1] = i1; rng[t * 4 + 2] = j0; rng[t * 4 + 3] = j1;
    for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) cnt[j * nx + i + 1]++;
  }
  for (let i = 1; i <= nx * nz; i++) cnt[i] += cnt[i - 1];
  const items = new Uint32Array(cnt[nx * nz]), fill = cnt.slice(0, nx * nz);
  for (let t = 0; t < tc; t++) {
    for (let j = rng[t * 4 + 2]; j <= rng[t * 4 + 3]; j++) for (let i = rng[t * 4]; i <= rng[t * 4 + 1]; i++) items[fill[j * nx + i]++] = t;
  }
  G = { pos, tri, tc, minx, minz, maxx, maxz, cs, nx, nz, start: cnt, items, stamp: new Uint32Array(tc), sid: 0 };
  geoCache.set(geo.uuid, G); W.gridTris = (W.gridTris || 0) + tc;
  return G;
}
function cellRange(G, x0, x1, z0, z1) {
  if (x1 < G.minx || x0 > G.maxx || z1 < G.minz || z0 > G.maxz) return null;
  const c = v => Math.max(0, v);
  return [c(Math.floor((x0 - G.minx) / G.cs)), Math.min(G.nx - 1, Math.floor((x1 - G.minx) / G.cs)),
          c(Math.floor((z0 - G.minz) / G.cs)), Math.min(G.nz - 1, Math.floor((z1 - G.minz) / G.cs))];
}
function nextSid(G) { if (++G.sid > 4e9) { G.stamp.fill(0); G.sid = 1; } return G.sid; }

// ray in local space, returns {t, tri} of the nearest hit with t < tmax (t is in WORLD metres: affine maps keep t)
function geoRay(G, ox, oy, oz, dx, dy, dz, tmax) {
  const x1 = ox + dx * tmax, z1 = oz + dz * tmax;
  const R = cellRange(G, Math.min(ox, x1), Math.max(ox, x1), Math.min(oz, z1), Math.max(oz, z1)); if (!R) return null;
  const sid = nextSid(G), { pos, tri, stamp, items, start, nx } = G;
  let best = tmax, bt = -1;
  for (let j = R[2]; j <= R[3]; j++) for (let i = R[0]; i <= R[1]; i++) {
    const cell = j * nx + i;
    for (let q = start[cell], e = start[cell + 1]; q < e; q++) {
      const t = items[q]; if (stamp[t] === sid) continue; stamp[t] = sid;
      const a = tri[t * 3] * 3, b = tri[t * 3 + 1] * 3, c = tri[t * 3 + 2] * 3;
      const ax = pos[a], ay = pos[a + 1], az = pos[a + 2];
      const e1x = pos[b] - ax, e1y = pos[b + 1] - ay, e1z = pos[b + 2] - az;
      const e2x = pos[c] - ax, e2y = pos[c + 1] - ay, e2z = pos[c + 2] - az;
      const px = dy * e2z - dz * e2y, py = dz * e2x - dx * e2z, pz = dx * e2y - dy * e2x;
      const det = e1x * px + e1y * py + e1z * pz; if (Math.abs(det) < 1e-12) continue;
      const inv = 1 / det, sx = ox - ax, sy = oy - ay, sz = oz - az;
      const u = (sx * px + sy * py + sz * pz) * inv; if (u < 0 || u > 1) continue;
      const qx = sy * e1z - sz * e1y, qy = sz * e1x - sx * e1z, qz = sx * e1y - sy * e1x;
      const v = (dx * qx + dy * qy + dz * qz) * inv; if (v < 0 || u + v > 1) continue;
      const tt = (e2x * qx + e2y * qy + e2z * qz) * inv;
      if (tt > 1e-5 && tt < best) { best = tt; bt = t; }
    }
  }
  return bt < 0 ? null : { t: best, tri: bt };
}
// sphere in local space: calls cb(tri, qx, qy, qz) for each triangle closer than rl (q = closest point)
const _q = [0, 0, 0];
function closest(px, py, pz, ax, ay, az, bx, by, bz, cx, cy, cz) {   // Ericson, Real-Time Collision Detection 5.1.5
  const abx = bx - ax, aby = by - ay, abz = bz - az, acx = cx - ax, acy = cy - ay, acz = cz - az;
  const apx = px - ax, apy = py - ay, apz = pz - az;
  const d1 = abx * apx + aby * apy + abz * apz, d2 = acx * apx + acy * apy + acz * apz;
  if (d1 <= 0 && d2 <= 0) { _q[0] = ax; _q[1] = ay; _q[2] = az; return; }
  const bpx = px - bx, bpy = py - by, bpz = pz - bz;
  const d3 = abx * bpx + aby * bpy + abz * bpz, d4 = acx * bpx + acy * bpy + acz * bpz;
  if (d3 >= 0 && d4 <= d3) { _q[0] = bx; _q[1] = by; _q[2] = bz; return; }
  const vc = d1 * d4 - d3 * d2;
  if (vc <= 0 && d1 >= 0 && d3 <= 0) { const v = d1 / (d1 - d3); _q[0] = ax + abx * v; _q[1] = ay + aby * v; _q[2] = az + abz * v; return; }
  const cpx = px - cx, cpy = py - cy, cpz = pz - cz;
  const d5 = abx * cpx + aby * cpy + abz * cpz, d6 = acx * cpx + acy * cpy + acz * cpz;
  if (d6 >= 0 && d5 <= d6) { _q[0] = cx; _q[1] = cy; _q[2] = cz; return; }
  const vb = d5 * d2 - d1 * d6;
  if (vb <= 0 && d2 >= 0 && d6 <= 0) { const w = d2 / (d2 - d6); _q[0] = ax + acx * w; _q[1] = ay + acy * w; _q[2] = az + acz * w; return; }
  const va = d3 * d6 - d5 * d4;
  if (va <= 0 && d4 - d3 >= 0 && d5 - d6 >= 0) {
    const w = (d4 - d3) / ((d4 - d3) + (d5 - d6)); _q[0] = bx + (cx - bx) * w; _q[1] = by + (cy - by) * w; _q[2] = bz + (cz - bz) * w; return;
  }
  const dn = 1 / (va + vb + vc), v = vb * dn, w = vc * dn;
  _q[0] = ax + abx * v + acx * w; _q[1] = ay + aby * v + acy * w; _q[2] = az + abz * v + acz * w;
}
function geoSphere(G, cx, cy, cz, rl, cb) {
  const R = cellRange(G, cx - rl, cx + rl, cz - rl, cz + rl); if (!R) return;
  const sid = nextSid(G), { pos, tri, stamp, items, start, nx } = G, r2 = rl * rl;
  for (let j = R[2]; j <= R[3]; j++) for (let i = R[0]; i <= R[1]; i++) {
    const cell = j * nx + i;
    for (let q = start[cell], e = start[cell + 1]; q < e; q++) {
      const t = items[q]; if (stamp[t] === sid) continue; stamp[t] = sid;
      const a = tri[t * 3] * 3, b = tri[t * 3 + 1] * 3, c = tri[t * 3 + 2] * 3;
      if (Math.min(pos[a + 1], pos[b + 1], pos[c + 1]) > cy + rl || Math.max(pos[a + 1], pos[b + 1], pos[c + 1]) < cy - rl) continue;
      closest(cx, cy, cz, pos[a], pos[a + 1], pos[a + 2], pos[b], pos[b + 1], pos[b + 2], pos[c], pos[c + 1], pos[c + 2]);
      const ex = cx - _q[0], ey = cy - _q[1], ez = cz - _q[2];
      if (ex * ex + ey * ey + ez * ez < r2) cb(t, _q[0], _q[1], _q[2]);
    }
  }
}
function triNormalWorld(rec, t, out) {
  const { pos, tri } = rec.G, a = tri[t * 3] * 3, b = tri[t * 3 + 1] * 3, c = tri[t * 3 + 2] * 3;
  const e1 = new V3(pos[b] - pos[a], pos[b + 1] - pos[a + 1], pos[b + 2] - pos[a + 2]);
  const e2 = new V3(pos[c] - pos[a], pos[c + 1] - pos[a + 1], pos[c + 2] - pos[a + 2]);
  return out.crossVectors(e1, e2).applyMatrix3(rec.nrm).normalize();
}

// ---------------------------------------------------------------- world colliders
let C = null;
function buildColliders() {
  const t0 = performance.now(), nameOf = new Map(Object.entries(matCache).map(([k, m]) => [m, k]));
  const recs = [], grid = new Map(); let skipped = 0;
  root.updateMatrixWorld(true);
  root.traverse(o => {
    if (!o.isMesh || o.material === inkMat || o === W.pup) return;
    const mn = nameOf.get(Array.isArray(o.material) ? o.material[0] : o.material) || '';
    if (/^Water/.test(mn)) { skipped++; return; }
    let piece = o, skip = false;
    for (let a = o; a && a !== root; a = a.parent) { if (SKIP_NAME.test(a.name)) skip = true; piece = a; }
    const camOnly = skip || /^Glow/.test(mn);              // glow veins, canopies: walk through them, but the camera stops
    const geo = o.geometry; if (!geo.boundingBox) geo.computeBoundingBox();   // GLTFLoader sets a dequantized box
    const box = geo.boundingBox.clone().applyMatrix4(o.matrixWorld);
    if (box.getSize(new V3()).length() < 0.8) { skipped++; return; }          // tiny decor
    const M = o.matrixWorld.clone(), inv = M.clone().invert();
    if (camOnly) skipped++;
    const rec = { o, name: o.name, piece: piece.name, mat: mn, camOnly, M, inv, invL: new THREE.Matrix3().setFromMatrix4(inv),
      nrm: new THREE.Matrix3().getNormalMatrix(M), s: M.getMaxScaleOnAxis(), box, geo, G: null, q: 0 };
    recs.push(rec);
    const i0 = Math.floor(box.min.x / P.cell), i1 = Math.floor(box.max.x / P.cell), j0 = Math.floor(box.min.z / P.cell), j1 = Math.floor(box.max.z / P.cell);
    for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) { const key = i * 65536 + j; let a = grid.get(key); if (!a) grid.set(key, a = []); a.push(rec); }
  });
  C = { recs, grid, q: 0 };
  console.log(`[walk] colliders: ${recs.length} meshes (${skipped} skipped: Glow/Water/canopy/tiny) in ${(performance.now() - t0).toFixed(0)} ms`);
}
function query(x0, z0, x1, z1) {
  if (!C) buildColliders();
  const q = ++C.q, out = [];
  for (let i = Math.floor(x0 / P.cell); i <= Math.floor(x1 / P.cell); i++) for (let j = Math.floor(z0 / P.cell); j <= Math.floor(z1 / P.cell); j++) {
    const a = C.grid.get(i * 65536 + j); if (!a) continue;
    for (const r of a) if (r.q !== q) { r.q = q; out.push(r); }
  }
  return out;
}
const _o = new V3(), _d = new V3(), _sb = new THREE.Box3();
function raycast(o, d, far, cands, camToo) {
  const ex = o.clone().addScaledVector(d, far);
  _sb.min.set(Math.min(o.x, ex.x) - 0.01, Math.min(o.y, ex.y) - 0.01, Math.min(o.z, ex.z) - 0.01);
  _sb.max.set(Math.max(o.x, ex.x) + 0.01, Math.max(o.y, ex.y) + 0.01, Math.max(o.z, ex.z) + 0.01);
  cands = cands || query(_sb.min.x, _sb.min.z, _sb.max.x, _sb.max.z);
  let best = null;
  for (const rec of cands) {
    if ((rec.camOnly && !camToo) || !rec.box.intersectsBox(_sb)) continue;
    const G = rec.G || (rec.G = geoGrid(rec.geo));
    _o.copy(o).applyMatrix4(rec.inv); _d.copy(d).applyMatrix3(rec.invL);
    const h = geoRay(G, _o.x, _o.y, _o.z, _d.x, _d.y, _d.z, best ? best.t : far);
    if (h) best = { t: h.t, tri: h.tri, rec };
  }
  if (!best) return null;
  best.point = o.clone().addScaledVector(d, best.t);
  best.normal = triNormalWorld(best.rec, best.tri, new V3()); if (best.normal.dot(d) > 0) best.normal.negate();
  return best;
}
const DOWN = new V3(0, -1, 0), UP = new V3(0, 1, 0);
function groundAt(x, yTop, z, len, cands) {   // highest walkable surface below (x, yTop, z) within len
  const o = new V3(x, yTop, z);
  for (let k = 0; k < 6 && len > 0; k++) {
    const h = raycast(o, DOWN, len, cands); if (!h) return null;
    if (h.normal.y >= P.slopeCos) return h;
    o.y -= h.t + 0.01; len -= h.t + 0.01;
  }
  return null;
}
function spheres(c, r, cands, cb) {
  for (const rec of cands) {
    if (rec.camOnly) continue;
    const b = rec.box;
    if (c.x + r < b.min.x || c.x - r > b.max.x || c.y + r < b.min.y || c.y - r > b.max.y || c.z + r < b.min.z || c.z - r > b.max.z) continue;
    const G = rec.G || (rec.G = geoGrid(rec.geo));
    _o.copy(c).applyMatrix4(rec.inv);
    geoSphere(G, _o.x, _o.y, _o.z, r / rec.s, (t, qx, qy, qz) => cb(rec, t, new V3(qx, qy, qz).applyMatrix4(rec.M)));
  }
}

// ---------------------------------------------------------------- character
function newChar(p) { return { pos: p.clone(), vel: new V3(), grounded: false, air: 0, maxStep: 0, block: null, wantJump: false }; }
const _n = new V3();
function step(ch, ix, iz, dt) {
  const p = ch.pos, v = ch.vel;
  const k = Math.min(1, dt * (ch.grounded ? 20 : 6));
  v.x += (ix * P.speed - v.x) * k; v.z += (iz * P.speed - v.z) * k;
  if (ch.wantJump && ch.grounded) { v.y = P.jump; ch.grounded = false; }
  ch.wantJump = false;
  v.y -= P.g * dt;
  p.addScaledVector(v, dt);
  const cands = query(p.x - 2, p.z - 2, p.x + 2, p.z + 2);
  // walls: body sphere, bottom at the step height
  ch.block = null; let deepest = 0;
  for (let it = 0; it < 4; it++) {
    const c = new V3(p.x, p.y + P.step + P.r, p.z); let moved = false;
    spheres(c, P.r, cands, (rec, t, q) => {
      const n = triNormalWorld(rec, t, _n); const push = c.clone().sub(q);
      if (n.dot(push) < 0) n.negate();
      if (n.y >= P.slopeCos) return;                       // walkable: the ground rays own it
      const depth = P.r - push.length();
      if (n.y < -0.5) {                                    // ceiling
        if (!ch.grounded) { p.y -= depth; c.y -= depth; if (v.y > 0) v.y = 0; moved = true; }
        return;
      }
      push.y = 0; if (push.lengthSq() < 1e-10) { push.set(n.x, 0, n.z); }
      if (push.lengthSq() < 1e-10) return;
      push.normalize(); p.addScaledVector(push, depth); c.addScaledVector(push, depth); moved = true;
      const into = v.x * push.x + v.z * push.z; if (into < 0) { v.x -= push.x * into; v.z -= push.z * into; }
      if (depth > deepest) { deepest = depth; ch.block = rec.piece + ' / ' + rec.name + ' (' + rec.mat + ')'; }
    });
    if (!moved) break;
  }
  // ground: 5 rays from the step height down; snap up (steps) or down (when grounded)
  let gy = -Infinity, gh = null;
  if (v.y <= 0) {
    const len = P.step + 0.05 + (ch.grounded ? P.step : 0), o = P.r * 0.6;
    for (const [dx, dz] of [[0, 0], [o, 0], [-o, 0], [0, o], [0, -o]]) {
      const h = groundAt(p.x + dx, p.y + P.step + 0.05, p.z + dz, len, cands);
      if (h && h.point.y > gy) { gy = h.point.y; gh = h; }
    }
  }
  if (gh) {
    const rise = gy - p.y; if (rise > ch.maxStep) ch.maxStep = rise;
    p.y = gy; v.y = 0; ch.grounded = true; ch.air = 0; ch.ground = gh.rec.piece + ' / ' + gh.rec.name;
  } else { ch.grounded = false; ch.air += dt; }
}

// ---------------------------------------------------------------- doors
function listDoors() {
  const out = []; if (!root) return out;
  root.updateMatrixWorld(true);
  root.traverse(o => {
    const ds = o.userData && o.userData.doors; if (!Array.isArray(ds)) return;
    ds.forEach((d, j) => {
      const [x, y, z, yaw] = d;                            // Blender Z-up on the piece root -> glTF Y-up -> world
      const p = new V3(x, z, -y).applyMatrix4(o.matrixWorld);
      const a = yaw * Math.PI / 180, out_ = new V3(Math.cos(a), 0, -Math.sin(a)).transformDirection(o.matrixWorld);
      out_.y = 0; out_.normalize();
      out.push({ piece: o.name, j, p, out: out_, floor: z, label: `${o.name} #${j}${z > 1 ? ' (floor ' + z.toFixed(1) + ' m)' : ''}` });
    });
  });
  return out.sort((a, b) => a.piece.localeCompare(b.piece) || a.j - b.j);
}

// ---------------------------------------------------------------- walk test
function testDoor(D, out, approaches = [3, 2, 1.5, 1]) {
    const inn = out.clone().negate();
    const r = { piece: D.piece, door: D.j, floor: D.floor, approach: 0, reached: 0, maxStep: 0, head: null, pass: false, reason: '', blockerName: '' };
    // approach from 3 m out; raised / balcony doors with no floor that far out fall back to 2, 1.5, 1 m (flagged)
    let s, g0 = null;
    for (const a of approaches) {
      s = D.p.clone().addScaledVector(out, a); g0 = groundAt(s.x, D.p.y + 1.0, s.z, 2.5);
      if (g0) { r.approach = a; break; }
    }
    const ch = newChar(new V3(s.x, g0 ? g0.point.y : D.p.y, s.z)); ch.grounded = !!g0;
    const blk = {}; let best = -1e9, stall = 0, fell = false;
    for (let i = 0; i < 240; i++) {                       // up to 4 s at 5 m/s (6 m needs 1.2 s)
      step(ch, inn.x, inn.z, P.dt);
      if (ch.block) blk[ch.block] = (blk[ch.block] || 0) + 1;
      if (ch.air > 0.4) { fell = true; break; }           // ~2 m of free fall
      const d = ch.pos.clone().sub(D.p).dot(inn);
      if (d > best + 0.005) { best = d; stall = 0; } else if (++stall > 30) break;
      if (d >= 3) break;
    }
    r.reached = +best.toFixed(2); r.maxStep = +ch.maxStep.toFixed(2);
    const top = Object.entries(blk).sort((a, b) => b[1] - a[1])[0];
    // head clearance: 0.3 m inside the threshold, ray up from the floor
    const hp = D.p.clone().addScaledVector(inn, 0.3), gf = groundAt(hp.x, D.p.y + 0.6, hp.z, 1.5);
    const fy = gf ? gf.point.y : D.p.y, hu = raycast(new V3(hp.x, fy + 0.05, hp.z), UP, 3);
    r.head = hu ? +(hu.t + 0.05).toFixed(2) : 3;
    if (!g0) r.reason = 'no ground outside (none within 1.5 m below the floor, 1-3 m out)';
    else if (fell) r.reason = `fell at ${best.toFixed(1)} m (no floor)`;
    else if (best < 3) { r.reason = `blocked at ${best.toFixed(2)} m`; r.blockerName = top ? top[0] : '(no wall contact: stuck)'; }
    if (r.head < 1.0) { r.reason = (r.reason ? r.reason + '; ' : '') + `head clearance ${r.head} m`; r.blockerName = r.blockerName || (hu.rec.piece + ' / ' + hu.rec.name); }
    r.pass = !r.reason;
    return r;
}
async function walkTest() {
  const doors = W.doors = listDoors(); const rows = [], fails = []; const t0 = performance.now();
  for (let n = 0; n < doors.length; n++) {
    if (n % 6 === 0) { info.textContent = `walk test ${n}/${doors.length} ...`; await new Promise(r => setTimeout(r, 0)); }
    const D = doors[n], r = testDoor(D, D.out);
    if (!r.pass && r.reached < 0) {                       // never reached the threshold: approach problem or the door itself?
      const n1 = testDoor(D, D.out, [1, 0.7]);
      if (n1.pass) { r.reason += ' (approach only: door itself passes from 1 m out)'; r.doorOk = true; }
      else {
        const f = testDoor(D, D.out.clone().negate());
        if (f.pass) { r.reason += ' (PASSES with yaw flipped 180: door yaw likely points inward)'; r.flipped = true; }
      }
    }
    rows.push(r); if (!r.pass) fails.push({ piece: r.piece, door: r.door, reason: r.reason, blockerName: r.blockerName });
  }
  const short = rows.filter(r => r.approach && r.approach < 3).map(r => `${r.piece}#${r.door}@${r.approach}m`);
  const sum = { total: rows.length, pass: rows.length - fails.length, fail: fails.length, failApproachOnly: rows.filter(r => r.doorOk).length, fails, shortApproach: short, ms: Math.round(performance.now() - t0) };
  console.log(`[walk] door walk test: ${sum.pass}/${sum.total} pass, ${sum.fail} fail (${sum.ms} ms, ${W.gridTris | 0} tris gridded)`);
  console.table(rows.map(r => ({ piece: r.piece, door: r.door, floor: r.floor, pass: r.pass ? 'PASS' : 'FAIL', approach: r.approach, reached: r.reached, maxStep: r.maxStep, head: r.head, reason: r.reason, blocker: r.blockerName })));
  const pad = (s, n) => String(s).padEnd(n).slice(0, n);
  console.log(['piece                         door floor  result approach reached step  head  reason / blocker']
    .concat(rows.map(r => `${pad(r.piece, 30)}${pad(r.door, 5)}${pad(r.floor, 6)} ${pad(r.pass ? 'PASS' : 'FAIL', 7)}${pad(r.approach, 9)}${pad(r.reached, 8)}${pad(r.maxStep, 6)}${pad(r.head, 6)}${r.reason}${r.blockerName ? ' | ' + r.blockerName : ''}`)).join('\n'));
  info.textContent = `Door walk test: ${sum.pass}/${sum.total} pass, ${sum.fail} fail (table in console)`;
  W.lastTest = { sum, rows };
  return sum;
}
window.__walkTest = walkTest;

// ---------------------------------------------------------------- the pup + play mode
function makePup() {
  const g = new THREE.Group(), m = c => new THREE.MeshToonMaterial({ color: new THREE.Color(c).convertSRGBToLinear(), gradientMap: grad });
  const orange = m(0xf2a65a), cream = m(0xfff1d6), dark = m(0x2a1a22);
  const pupInk = new THREE.MeshBasicMaterial({ color: 0x2a1a22, side: THREE.BackSide });   // thinner than the map's ink
  pupInk.onBeforeCompile = s => { s.vertexShader = s.vertexShader.replace('#include <begin_vertex>', 'vec3 transformed = position * 1.06;'); };
  const add = (geo, mat, x, y, z, sx = 1, sy = 1, sz = 1, ink = true) => {
    const o = new THREE.Mesh(geo, mat); o.position.set(x, y, z); o.scale.set(sx, sy, sz); o.castShadow = true; g.add(o);
    if (ink) { const h = new THREE.Mesh(geo, pupInk); o.add(h); } return o;
  };
  add(new THREE.SphereGeometry(0.28, 20, 14), orange, 0, 0.36, -0.02, 1, 0.9, 1.3);
  add(new THREE.SphereGeometry(0.22, 20, 14), orange, 0, 0.66, 0.24);
  add(new THREE.SphereGeometry(0.1, 12, 8), cream, 0, 0.6, 0.43, 1, 0.8, 1);
  add(new THREE.SphereGeometry(0.035, 8, 6), dark, 0, 0.63, 0.52, 1, 1, 1, false);
  for (const sx of [-1, 1]) {
    add(new THREE.SphereGeometry(0.03, 8, 6), dark, sx * 0.09, 0.71, 0.42, 1, 1, 1, false);
    const ear = add(new THREE.ConeGeometry(0.08, 0.2, 10), orange, sx * 0.13, 0.84, 0.2); ear.rotation.z = -sx * 0.35;
    for (const z of [0.18, -0.2]) add(new THREE.CylinderGeometry(0.06, 0.06, 0.18, 10), cream, sx * 0.14, 0.09, z, 1, 1, 1, false);
  }
  const tail = add(new THREE.ConeGeometry(0.06, 0.28, 8), orange, 0, 0.5, -0.38); tail.rotation.x = -0.9;
  g.visible = false; return g;
}
W.pup = makePup(); scene.add(W.pup);
const keys = new Set(); let saved = null, cam = { yaw: 0, pitch: 0.35, dist: 4.5 }, drag = null, ch = null, spawnDoor = null;
const ft = []; let hiddenInk = new Set();

function spawn(D) {
  spawnDoor = D; const inn = D.out.clone().negate(), s = D.p.clone().addScaledVector(D.out, 2.5);
  const g = groundAt(s.x, D.p.y + 1.5, s.z, 4);
  ch = newChar(new V3(s.x, g ? g.point.y : D.p.y + 0.5, s.z)); ch.facing = Math.atan2(inn.x, inn.z);
  cam.yaw = Math.atan2(-inn.x, -inn.z);
}
W.enter = function (D) {
  if (!root) return;
  if (!W.active) {
    saved = { pos: camera.position.clone(), target: controls.target.clone(), near: camera.near, sun: sun.position.clone(), st: sun.target.position.clone(),
      sc: ['left', 'right', 'top', 'bottom', 'near', 'far'].map(k => sun.shadow.camera[k]) };
    W.active = true; controls.enabled = false; camera.near = 0.1; camera.updateProjectionMatrix();
    W.pup.visible = true; hint.style.display = 'block'; touchUI.style.display = 'flex';
  }
  spawn(D || W.doors[0]); W.last = performance.now(); W.acc = 0;
  if (document.activeElement) document.activeElement.blur();
};
W.exit = function () {
  if (!W.active) return;
  for (const h of hiddenInk) h.visible = inkOn; hiddenInk = new Set();
  W.active = false; W.pup.visible = false; hint.style.display = 'none'; touchUI.style.display = 'none'; controls.enabled = true; info.textContent = 'Orbit view';
  stick.id = null; stick.fx = stick.rx = 0; stickEl.style.display = 'none'; drag = null;
  camera.position.copy(saved.pos); controls.target.copy(saved.target); camera.near = saved.near; camera.updateProjectionMatrix();
  sun.position.copy(saved.sun); sun.target.position.copy(saved.st);
  ['left', 'right', 'top', 'bottom', 'near', 'far'].forEach((k, i) => sun.shadow.camera[k] = saved.sc[i]); sun.shadow.camera.updateProjectionMatrix();
};
W.frame = function () {
  const now = performance.now(), dt = Math.min(0.1, (now - W.last) / 1000); W.last = now;
  ft.push(dt * 1000); if (ft.length > 120) ft.shift();
  let fx = stick.fx, rx = stick.rx;   // touch stick is analog (0..1), keys are full speed
  if (keys.has('KeyW') || keys.has('ArrowUp')) fx++; if (keys.has('KeyS') || keys.has('ArrowDown')) fx--;
  if (keys.has('KeyD') || keys.has('ArrowRight')) rx++; if (keys.has('KeyA') || keys.has('ArrowLeft')) rx--;
  const sy = Math.sin(cam.yaw), cy = Math.cos(cam.yaw);
  let ix = -sy * fx + cy * rx, iz = -cy * fx - sy * rx; const il = Math.hypot(ix, iz); if (il > 1) { ix /= il; iz /= il; }
  W.acc += dt; let n = 0;
  while (W.acc >= P.dt && n < 6) { step(ch, ix, iz, P.dt); W.acc -= P.dt; n++; }
  if (n === 6) W.acc = 0;
  if (ch.pos.y < W.minY) spawn(spawnDoor);
  if (Math.hypot(ch.vel.x, ch.vel.z) > 0.3) ch.facing = Math.atan2(ch.vel.x, ch.vel.z);
  W.pup.position.copy(ch.pos); W.pup.rotation.y = ch.facing;
  W.pup.children.forEach((o, i) => { if (i === 0) o.position.y = 0.36 + (ch.grounded ? Math.abs(Math.sin(now * 0.02)) * 0.03 * Math.min(1, Math.hypot(ch.vel.x, ch.vel.z) / 3) : 0); });
  // follow camera, pulled in when something is between it and the pup
  const tgt = ch.pos.clone().add(new V3(0, 0.7, 0));
  const dir = new V3(Math.sin(cam.yaw) * Math.cos(cam.pitch), Math.sin(cam.pitch), Math.cos(cam.yaw) * Math.cos(cam.pitch));
  const hit = raycast(tgt, dir, cam.dist + 0.4, null, true); const d = hit ? Math.max(0.6, Math.min(cam.dist, hit.t - 0.4)) : cam.dist;
  camera.position.copy(tgt).addScaledVector(dir, d); camera.lookAt(tgt);
  // ink hulls are back faces: from inside a shell (a house, the tree) they cover the screen, so hide the ink of
  // every mesh whose box holds the camera
  const cp = camera.position, now_ = new Set();
  for (const r of query(cp.x - 1, cp.z - 1, cp.x + 1, cp.z + 1)) {
    const b = r.box; if (cp.x < b.min.x - 0.5 || cp.x > b.max.x + 0.5 || cp.y < b.min.y - 0.5 || cp.y > b.max.y + 0.5 || cp.z < b.min.z - 0.5 || cp.z > b.max.z + 0.5) continue;
    for (const h of r.o.children) if (h.material === inkMat) now_.add(h);
  }
  for (const h of hiddenInk) if (!now_.has(h)) h.visible = inkOn;
  for (const h of now_) h.visible = false;
  hiddenInk = now_;
  // tight shadow box around the pup
  const sc = sun.shadow.camera;
  sun.target.position.copy(ch.pos); sun.position.copy(ch.pos).add(new V3(-0.5, 1, 0.35).normalize().multiplyScalar(200));
  if (sc.right !== 45) { Object.assign(sc, { left: -45, right: 45, top: 45, bottom: -45, near: 10, far: 450 }); sc.updateProjectionMatrix(); }
  if ((W.hud = (W.hud || 0) + dt) > 0.5) {
    W.hud = 0; const avg = ft.reduce((a, b) => a + b, 0) / ft.length; W.fps = Math.round(1000 / avg); W.frameMs = +avg.toFixed(1);
    info.textContent = `Walking: ${W.fps} fps (${W.frameMs} ms)  y ${ch.pos.y.toFixed(1)}  ${ch.grounded ? 'on ' + (ch.ground || '') : 'in the air'}`;
  }
};
W.raycast = raycast; W.groundAt = groundAt;
W.teleport = (x, y, z) => { ch.pos.set(x, y, z); ch.vel.set(0, 0, 0); ch.grounded = false; ch.maxStep = 0; return W.state(); };
W.state = () => ch && { pos: ch.pos.toArray().map(v => +v.toFixed(2)), grounded: ch.grounded, ground: ch.ground, block: ch.block, maxStep: ch.maxStep };
// drive the real movement code from scripts: walk.drive(seconds, {f:1, r:0, jump:false})
W.drive = function (sec, inp = {}) {
  const sy = Math.sin(cam.yaw), cy = Math.cos(cam.yaw), f = inp.f || 0, r = inp.r || 0;
  let ix = -sy * f + cy * r, iz = -cy * f - sy * r; const il = Math.hypot(ix, iz); if (il > 0) { ix /= il; iz /= il; }
  if (inp.jump) ch.wantJump = true;
  for (let i = 0; i < Math.round(sec / P.dt); i++) step(ch, ix, iz, P.dt);
  return W.state();
};
W.cam = cam;

addEventListener('keydown', e => {
  if (!W.active) return;
  if (e.code === 'Escape') { W.exit(); return; }
  if (e.code === 'Space') { ch.wantJump = true; e.preventDefault(); }
  if (e.code === 'KeyR') spawn(spawnDoor);
  if (/^(Key[WASD]|Arrow)/.test(e.code)) e.preventDefault();
  keys.add(e.code);
});
addEventListener('keyup', e => keys.delete(e.code));
addEventListener('blur', () => keys.clear());
// phones: a touch on the left 45% of the screen is a floating move stick, anywhere else drags the camera
const stick = { id: null, x0: 0, y0: 0, fx: 0, rx: 0 }, STICK_R = 55;
renderer.domElement.addEventListener('pointerdown', e => {
  if (!W.active) return;
  if (e.pointerType === 'touch' && e.clientX < innerWidth * 0.45 && stick.id === null) {
    Object.assign(stick, { id: e.pointerId, x0: e.clientX, y0: e.clientY, fx: 0, rx: 0 });
    stickEl.style.display = 'block'; stickEl.style.left = (e.clientX - STICK_R) + 'px'; stickEl.style.top = (e.clientY - STICK_R) + 'px';
    knobEl.style.transform = 'translate(0px, 0px)'; return;
  }
  if (!drag) drag = { id: e.pointerId, x: e.clientX, y: e.clientY };
});
function pointerEnd(e) {
  if (e.pointerId === stick.id) { stick.id = null; stick.fx = stick.rx = 0; stickEl.style.display = 'none'; }
  if (drag && drag.id === e.pointerId) drag = null;
}
addEventListener('pointerup', pointerEnd); addEventListener('pointercancel', pointerEnd);
addEventListener('pointermove', e => {
  if (!W.active) return;
  if (e.pointerId === stick.id) {
    let dx = e.clientX - stick.x0, dy = e.clientY - stick.y0; const l = Math.hypot(dx, dy);
    if (l > STICK_R) { dx *= STICK_R / l; dy *= STICK_R / l; }
    knobEl.style.transform = `translate(${dx}px, ${dy}px)`;
    const m = Math.hypot(dx, dy) < 8 ? 0 : 1 / STICK_R; stick.rx = dx * m; stick.fx = -dy * m;
    return;
  }
  if (!drag || drag.id !== e.pointerId) return;
  cam.yaw -= (e.clientX - drag.x) * 0.006; cam.pitch = Math.max(0.02,Math.min(1.3, cam.pitch + (e.clientY - drag.y) * 0.005));
  drag.x = e.clientX; drag.y = e.clientY;
});
const stickEl = document.createElement('div'), knobEl = document.createElement('div');
stickEl.style.cssText = `position:fixed;display:none;width:${2 * STICK_R}px;height:${2 * STICK_R}px;border-radius:50%;border:3px solid var(--ink);background:rgba(255,255,255,0.35);pointer-events:none`;
knobEl.style.cssText = `position:absolute;left:${STICK_R - 24}px;top:${STICK_R - 24}px;width:48px;height:48px;border-radius:50%;background:var(--panel);border:3px solid var(--ink)`;
stickEl.appendChild(knobEl); document.body.appendChild(stickEl);
jumpBtn.onpointerdown = e => { e.preventDefault(); if (W.active) ch.wantJump = true; };
backBtn.onclick = () => W.exit();
renderer.domElement.addEventListener('wheel', e => { if (W.active) cam.dist = Math.max(1.5, Math.min(12, cam.dist * (e.deltaY > 0 ? 1.1 : 0.9))); }, { passive: true });

// ---------------------------------------------------------------- UI hookup (called by viewer.html after each load)
W.onLoad = function () {
  W.exit(); C = null; geoCache.clear(); W.gridTris = 0;
  W.doors = listDoors(); W.minY = new THREE.Box3().setFromObject(root).min.y - 40;
  doorSel.innerHTML = '';
  W.doors.forEach((D, i) => { const o = document.createElement('option'); o.value = i; o.textContent = D.label; doorSel.appendChild(o); });
  const eld = W.doors.findIndex(D => /ElderTree/.test(D.piece)); if (eld >= 0) doorSel.value = eld;
  const has = W.doors.length > 0; [walkBtn, doorSel, testBtn].forEach(b => b.style.display = has ? '' : 'none');
};
walkBtn.onclick = () => W.enter(W.doors[+doorSel.value]);
doorSel.onchange = () => W.enter(W.doors[+doorSel.value]);
testBtn.onclick = () => { W.exit(); walkTest(); };
})();
