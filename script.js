/* -------------------------
   In-browser marbling engine (extended with tools)
   (Updated: awl = localized circular drag, much bigger, sharper, stronger)
   ------------------------- */

/* Parameters */
const NX = 400, NY = 300;            // grid resolution (raster algorithm)
const DPR = Math.min(window.devicePixelRatio || 1, 2);
const dropDefaultRadius = 18.0;
const seedRadius = 2.0;
let growTime = 0.22;                // seconds
const minDistEps = 1e-6;
let mode = 'contour';               // 'contour' or 'raster'
const colorList = [ [1.0,0.2,0.2], [0.15,1.0,0.25], [0.2,0.5,1.0] ];
let selectedColor = 0;
let mouseAddRadius = dropDefaultRadius;
let flow = 0.8; // global flow (0..1)
let awlRadius = 40; // DEFAULT INCREASED: user adjustable (in grid units)
let pullStrength = 1.0; // MODIFIED: Increased from 0.75 for a stronger pull
// Adjusted: global pull attenuation (closer to 1.0 means less attenuation across radius)
let pullU = 0.99;       // MODIFIED: Increased from 0.98 for longer paint carry

/* Drops container */
let drops = []; // {C:[x,y], r, r_target, color:[r,g,b], created (sec), grow_time, alpha?}

/* Undo / Redo stacks */
let undoStack = [];
let redoStack = [];

/* Current tool */
let currentTool = 'drop'; // 'drop'|'awl'|'comb'|'pull'

/* Comb parameters (user adjustable) */
let combSpacing = 16; // pixels between tines (grid units)
let combWidth = 120;  // overall comb width (radius around pointer)
let combTineRadius = 8; // radius of each tine's influence
let combStrength = 0.24; // how strongly comb moves paint

/* Pull (directional awl) parameters */
let pullRadius = 90; // This parameter is now deprecated, awlRadius is used for pull size

/* Brush parameters */
let brushScatter = 48; // scatter radius for brush
let brushCount = 12;   // drops per brush stroke
let brushAlpha = 0.28; // opacity for brush drops (per-drop), 0..1
let brushSizeMin = 6.0, brushSizeMax = 12.0;

/* ---------------------------
   NEW: Raster paint buffer state
   - paintBuffer holds an NX×NY RGBA snapshot that awl/comb warp
   - paintBufferInitialized: whether it contains data consistent with drops
   - paintBufferDirty: marks that drops changed and buffer must be rasterized again
   --------------------------- */
let paintBuffer = new Uint8ClampedArray(NX * NY * 4);
let paintBufferInitialized = false;
let paintBufferDirty = true;

/* ---------------------------
   NEW: Vector stroke composition (homeomorphisms)
   - strokes: array of stroke objects to apply to contours and raster
   - Each stroke : { A:{x,y}, M:{x,y}, N:{x,y}, z, u, scale }
   --------------------------- */
let strokes = [];

/* Utility: deep clone of drops */
function cloneDrops(arr) {
  return arr.map(d => ({...d, C:[d.C[0], d.C[1]]}));
}

/* Push current state to undo stack
   NOTE: unchanged behavior — still pushing only vector drops (keeps small) */
function saveState() {
  undoStack.push(cloneDrops(drops));
  // limit stack size to prevent memory issues
  if (undoStack.length > 50) undoStack.shift();
  redoStack = [];
  updateUndoRedoUI();
}

/* Update Undo/Redo button enabled state */
function updateUndoRedoUI(){
  const u = document.getElementById('undo'), r = document.getElementById('redo');
  if (u) u.disabled = (undoStack.length === 0);
  if (r) r.disabled = (redoStack.length === 0);
  if (u) { u.classList.toggle('disabled', undoStack.length === 0); }
  if (r) { r.classList.toggle('disabled', redoStack.length === 0); }
}

/* Canvas setup */
const displayCanvas = document.getElementById('displayCanvas');
const displayCtx = displayCanvas.getContext('2d', {alpha:false});
// offscreen (raster) canvas at NXxNY
const offCanvas = document.createElement('canvas');
offCanvas.width = NX; offCanvas.height = NY;
const offCtx = offCanvas.getContext('2d', {alpha:false});

/* Utility: time */
function nowSeconds(){ return performance.now() / 1000.0; }

/* --- Vector math helpers --- */
const V = {
  add: (a,b) => ({x: a.x + b.x, y: a.y + b.y}),
  sub: (a,b) => ({x: a.x - b.x, y: a.y - b.y}),
  mul: (a,s) => ({x: a.x * s, y: a.y * s}),
  dot: (a,b) => a.x*b.x + a.y*b.y,
  len: a => Math.hypot(a.x, a.y),
  norm: a => {
    const L = Math.hypot(a.x, a.y) || 1;
    return {x: a.x / L, y: a.y / L};
  },
  perp: a => ({x: -a.y, y: a.x})
};

/* --- transforms & renderers (same as original but use per-drop alpha if present) --- */
function forwardDropTransform(Px, Py, Cx, Cy, r){
  const dx = Px - Cx, dy = Py - Cy;
  const dist2 = dx*dx + dy*dy;
  const factor = Math.sqrt(1.0 + (r*r) / Math.max(dist2, minDistEps));
  return [ Cx + dx * factor, Cy + dy * factor ];
}

function inverseDropTransform(QxArr, QyArr, Cx, Cy, r){
  const n = QxArr.length;
  const X = new Float32Array(n);
  const Y = new Float32Array(n);
  const inside = new Uint8Array(n);
  for(let i=0;i<n;i++){
    const dx = QxArr[i] - Cx, dy = QyArr[i] - Cy;
    const d = Math.hypot(dx, dy);
    if (d < r){
      inside[i] = 1;
      X[i] = QxArr[i];
      Y[i] = QyArr[i];
    } else {
      inside[i] = 0;
      const denom = Math.max(dx*dx + dy*dy, minDistEps);
      const invFactor = Math.sqrt(Math.max(0.0, 1.0 - (r*r)/denom));
      X[i] = Cx + dx * invFactor;
      Y[i] = Cy + dy * invFactor;
    }
  }
  return [X, Y, inside];
}

function makeCirclePoints(cx, cy, r, npoints){
  const pts = new Array(npoints);
  for(let i=0;i<npoints;i++){
    const t = (i / npoints) * Math.PI * 2;
    pts[i] = [ cx + r * Math.cos(t), cy + r * Math.sin(t) ];
  }
  return pts;
}
function forwardMapContour(pts, subsequentDrops){
  let mapped = pts.map(p=>[p[0],p[1]]);
  for(const d of subsequentDrops){
    const Cx = d.C[0], Cy = d.C[1], r = d.r;
    mapped = mapped.map(p=>{
      const [nx, ny] = forwardDropTransform(p[0], p[1], Cx, Cy, r);
      return [nx, ny];
    });
  }
  return mapped;
}

/* ---------------------
   Stroke factory & application (homeomorphism)
   Each stroke maps P -> P + z * u^{|(P - A)·N|/scale} * M
   - A: a point on the tine-line (we'll use start point)
   - M: unit vector along tine line (direction of movement)
   - N: unit normal perpendicular to M
   - z: maximum displacement (positive; inverse is same with -z)
   - u: attenuation factor (0<u<1)
   - scale: distance normalization for exponent exponent
   --------------------- */
function makeStrokeFromLine(Ax, Ay, Bx, By, params){
  const A = {x: Ax, y: Ay};
  const dir = V.norm({x: Bx - Ax, y: By - Ay});
  const M = dir;
  const N = V.perp(M);
  return {
    A,
    M,
    N,
    z: params.z,
    u: params.u,
    scale: params.scale,
    // Store the END point (B) for use in circular falloff
    B: {x: Bx, y: By} 
  };
}

/* Apply a single stroke to an array of points (in-place style: returns mapped array) */
function applyStrokeToPoints(pts, stroke){
  const mapped = new Array(pts.length);
  for(let i=0;i<pts.length;i++){
    const p = pts[i];
    const P = {x: p[0], y: p[1]};
    
    // Calculate distance from point P to the END point B (circular basis)
    const BP = V.sub(P, stroke.B);
    const d_radial = V.len(BP);
    
    // The previous implementation used linear falloff (dperp), now using radial distance
    // This is for contour rendering, and should match raster behavior.
    const falloffParam = d_radial / (awlRadius * stroke.scale); 
    const disp = stroke.z * Math.pow(stroke.u, falloffParam);
    
    const newP = V.add(P, V.mul(stroke.M, disp));
    mapped[i] = [newP.x, newP.y];
  }
  return mapped;
}

/* Compose multiple strokes on a point list: F = Fn ∘ ... ∘ F1 */
function applyStrokesToPoints(pts, strokesList){
  let mapped = pts.map(p => [p[0], p[1]]);
  for(const s of strokesList){
    mapped = applyStrokeToPoints(mapped, s);
  }
  return mapped;
}

/* Apply a single stroke to the raster paintBuffer (in place)
   - Uses inverse mapping and now depends on radial distance from stroke.B
*/
function applyStrokeToPaintBuffer(stroke, influenceRadius = null){
  if (!paintBufferInitialized || paintBuffer.length === 0) return;

  // Use the strict Awl Radius as the influence circle
  const radius = awlRadius; 
  // Bounding box centered on the stroke's END point (B)
  const minX = Math.max(0, Math.floor(stroke.B.x - radius - 2));
  const maxX = Math.min(NX-1, Math.ceil(stroke.B.x + radius + 2));
  const minY = Math.max(0, Math.floor(stroke.B.y - radius - 2));
  const maxY = Math.min(NY-1, Math.ceil(stroke.B.y + radius - 2));

  // copy current buffer into newFrame so we can write into it
  const newFrame = new Uint8ClampedArray(paintBuffer);

  for (let y = minY; y <= maxY; y++){
    for (let x = minX; x <= maxX; x++){
      const P = {x: x, y: y};
      
      // *** THE CORE CHANGE ***
      // Calculate radial distance from the END point (B) of the mouse drag
      const BP = V.sub(P, stroke.B);
      const d_radial = V.len(BP); 
      
      // Strict circular cut-off: must be inside the awlRadius
      if (d_radial > radius) continue; 

      // Displacement magnitude (forward mapping) based on radial distance
      // We divide d_radial by (radius * stroke.scale) to control sharpness.
      // A smaller 'stroke.scale' makes the falloff sharper.
      const falloffParam = d_radial / (radius * stroke.scale); 
      const disp = stroke.z * Math.pow(stroke.u, falloffParam);
      
      // Source coordinate (inverse mapping)
      const srcX = x - stroke.M.x * disp;
      const srcY = y - stroke.M.y * disp;

      // sample source (bilinear)
      const samp = samplePaintBufferBilinear(paintBuffer, srcX, srcY); // returns [r,g,b,a] in 0..255

      // alpha blend source over destination
      const dstIdx = (y * NX + x) * 4;
      const dstR = newFrame[dstIdx    ];
      const dstG = newFrame[dstIdx + 1];
      const dstB = newFrame[dstIdx + 2];
      const dstA = newFrame[dstIdx + 3] / 255.0;

      const srcA = samp[3] / 255.0;
      const outA = srcA + dstA * (1 - srcA);
      if (outA <= 0) continue;
      const outR = Math.round((samp[0] * srcA + dstR * dstA * (1 - srcA)) / Math.max(1e-9, outA));
      const outG = Math.round((samp[1] * srcA + dstG * dstA * (1 - srcA)) / Math.max(1e-9, outA));
      const outB = Math.round((samp[2] * srcA + dstB * dstA * (1 - srcA)) / Math.max(1e-9, outA));
      newFrame[dstIdx    ] = outR;
      newFrame[dstIdx + 1] = outG;
      newFrame[dstIdx + 2] = outB;
      newFrame[dstIdx + 3] = Math.round(outA * 255);
    }
  }

  // commit back
  paintBuffer.set(newFrame);
  paintBufferInitialized = true;
  paintBufferDirty = false;
}

/* --------------------- End stroke helpers --------------------- */

function rasterRender(dropsList){
  const img = offCtx.createImageData(NX, NY);
  const outData = img.data;
  const filled = new Uint8Array(NX * NY);

  let activeIndices = new Uint32Array(NX*NY);
  let activeCount = 0;
  for(let y=0;y<NY;y++){
    for(let x=0;x<NX;x++){
      activeIndices[activeCount++] = (y<<16) | x;
    }
  }
  let Qx = new Float32Array(activeCount);
  let Qy = new Float32Array(activeCount);
  for(let i=0;i<activeCount;i++){
    const pack = activeIndices[i];
    const x = pack & 0xFFFF;
    const y = pack >>> 16;
    Qx[i] = x;
    Qy[i] = y;
  }

  for(let di = dropsList.length - 1; di >= 0; di--){
    if (activeCount === 0) break;
    const d = dropsList[di];
    const Cx = d.C[0], Cy = d.C[1], r = d.r;
    const color = d.color;
    const alpha = (typeof d.alpha === 'number') ? d.alpha : flow;

    const qx_sub = Qx.subarray(0, activeCount);
    const qy_sub = Qy.subarray(0, activeCount);
    const [Xnew, Ynew, insideMask] = inverseDropTransform(qx_sub, qy_sub, Cx, Cy, r);

    let newActivePos = 0;
    for(let i=0;i<activeCount;i++){
      if (insideMask[i]){
        const pack = activeIndices[i];
        const x = pack & 0xFFFF;
        const y = pack >>> 16;
        const idx = (y * NX + x) * 4;
        outData[idx  ] = Math.round(color[0]*255);
        outData[idx+1] = Math.round(color[1]*255);
        outData[idx+2] = Math.round(color[2]*255);
        outData[idx+3] = Math.round(alpha*255);
        filled[(y * NX + x)] = 1;
      } else {
        activeIndices[newActivePos] = activeIndices[i];
        Qx[newActivePos] = Xnew[i];
        Qy[newActivePos] = Ynew[i];
        newActivePos++;
      }
    }
    activeCount = newActivePos;
  }

  for(let i=0;i<NX*NY;i++){
    if (!filled[i]){
      const y = Math.floor(i / NX);
      const x = i - y*NX;
      const idx = (y * NX + x) * 4;
      outData[idx  ] = 255;
      outData[idx+1] = 255;
      outData[idx+2] = 255;
      outData[idx+3] = 255;
    } else {
      const idx = i*4;
      if (outData[idx+3] === 0) outData[idx+3] = 255;
    }
  }

  return img;
}

function contourRender(dropsList, ctx, scale){
  ctx.save();
  ctx.clearRect(0,0,ctx.canvas.width, ctx.canvas.height);
  ctx.fillStyle = '#ffffff';
  ctx.fillRect(0,0,ctx.canvas.width, ctx.canvas.height);

  const n = dropsList.length;
  for(let i=0;i<n;i++){
    const d = dropsList[i];
    const power = Math.max(0, n - 1 - i);
    const base_points = 160;
    const contour_increase_factor = 1.8;
    let npts = Math.round(base_points * Math.pow(contour_increase_factor, power));
    npts = Math.max(32, Math.min(2048, npts));
    const cx = d.C[0], cy = d.C[1], r = d.r;
    let pts = makeCirclePoints(cx, cy, r, npts);
    const subsequent = dropsList.slice(i+1);
    if (subsequent.length > 0){
      pts = forwardMapContour(pts, subsequent);
    }

    // Apply composed strokes (homeomorphisms) so comb/pull deform contours (vector-only)
    if (strokes.length > 0){
      pts = applyStrokesToPoints(pts, strokes);
    }

    ctx.beginPath();
    if (pts.length === 0) continue;
    ctx.moveTo(pts[0][0]*scale, pts[0][1]*scale);
    for(let p=1;p<pts.length;p++){
      ctx.lineTo(pts[p][0]*scale, pts[p][1]*scale);
    }
    ctx.closePath();
    const col = d.color.map(v => Math.round(v*255));
    const alpha = (typeof d.alpha === 'number') ? d.alpha : flow;
    ctx.fillStyle = `rgba(${col[0]},${col[1]},${col[2]},${alpha})`;
    ctx.fill();
  }
  ctx.restore();
}

/* Drop expansion */
function updateDropExpansion(now){
  let changed = false;
  for(const d of drops){
    const age = now - d.created;
    const target = d.r_target;
    const gtime = Math.max(0.0001, d.grow_time);
    let newr;
    if (age <= 0) newr = seedRadius;
    else {
      const frac = Math.min(1.0, age / gtime);
      newr = seedRadius + frac * (target - seedRadius);
    }
    if (Math.abs(newr - d.r) > 1e-3){ d.r = newr; changed = true; }
  }
  return changed;
}

/* Add drop */
function addDropAt(x,y,r = null, colorIdx = null, alpha = null){
  // addDropAt itself pushes state in original code — keep state responsibility outside
  const r_target = (r === null) ? dropDefaultRadius : r;
  const ci = (colorIdx === null) ? selectedColor : colorIdx;
  const drop = {
    C: [x, y],
    r: seedRadius,
    r_target: r_target,
    color: colorList[ci],
    created: nowSeconds(),
    grow_time: growTime
  };
  if (typeof alpha === 'number') drop.alpha = alpha;
  drops.push(drop);

  // Mark raster buffer dirty so it will be re-generated from drops before next warp/render
  paintBufferDirty = true;
  paintBufferInitialized = false;
}

/* --- Helpers: bilinear sampling from paintBuffer & rasterize drops into paintBuffer --- */

function samplePaintBufferBilinear(buf, sx, sy) {
  // returns array [r,g,b,a] floats in 0..255 range
  if (sx < 0) sx = 0; if (sy < 0) sy = 0;
  if (sx > NX-1) sx = NX-1; if (sy > NY-1) sy = NY-1;
  const x0 = Math.floor(sx), y0 = Math.floor(sy);
  const x1 = Math.min(NX-1, x0+1), y1 = Math.min(NY-1, y0+1);
  const tx = sx - x0, ty = sy - y0;

  const idx00 = (y0 * NX + x0) * 4;
  const idx10 = (y0 * NX + x1) * 4;
  const idx01 = (y1 * NX + x0) * 4;
  const idx11 = (y1 * NX + x1) * 4;

  const out = [0,0,0,0];
  for(let c=0;c<4;c++){
    const v00 = buf[idx00 + c], v10 = buf[idx10 + c], v01 = buf[idx01 + c], v11 = buf[idx11 + c];
    const v0 = v00 * (1-tx) + v10 * tx;
    const v1 = v01 * (1-tx) + v11 * ty;
    out[c] = v0 * (1-ty) + v1 * ty;
  }
  return out;
}

function rasterizeDropsToPaintBuffer(){
  // produce an ImageData from drops and copy into paintBuffer
  const img = rasterRender(drops);
  // copy image data into paintBuffer
  paintBuffer.set(img.data);
  paintBufferInitialized = true;
  paintBufferDirty = false;
  // also update offCtx so animate can draw it immediately
  offCtx.putImageData(img, 0, 0);
}

/* --- Comb stroke: move drops near the comb tines along the drag vector --- */
function applyCombStroke(x0, y0, dx, dy){
  // direction unit
  const len = Math.hypot(dx, dy);
  if (len < 1e-6) return;
  const ux = dx / len, uy = dy / len;
  // perpendicular vector (across which tines are spaced)
  const px = -uy, py = ux;
  // We'll consider drops within combWidth / 2 orthogonally from the pointer
  const halfW = combWidth * 0.5;

  // For each drop, compute its relative vector to the stroke line (origin at x0,y0)
  for(const d of drops){
    const rx = d.C[0] - x0, ry = d.C[1] - y0;
    // projection along movement (t coordinate) and across movement (s coordinate)
    const tcoord = rx * ux + ry * uy;
    const scoord = rx * px + ry * py;
    if (Math.abs(scoord) > halfW + combTineRadius) continue; // outside comb influence zone

    // find nearest tine by mapping scoord to spacing grid
    // tines are lines spaced every combSpacing along the perpendicular axis; find distance to nearest tine
    // shift such that centerline corresponds to 0
    const nearestIndex = Math.round(scoord / combSpacing);
    const tineCenter = nearestIndex * combSpacing;
    const distToTine = Math.abs(scoord - tineCenter);

    if (distToTine <= combTineRadius + 0.0001){
      // compute falloff (0..1) where 1 at center of tine
      const falloff = 1.0 - (distToTine / (combTineRadius + 1e-6));
      // apply movement proportional to combStrength, falloff, and stroke length
      const moveFactor = combStrength * falloff;
      d.C[0] += ux * len * moveFactor;
      d.C[1] += uy * len * moveFactor;

      // slight shear/stretch: optionally nudge r_target a bit for visual feel
      d.r_target = Math.max(1.0, d.r_target * (1.0 - 0.02 * falloff));

      // ensure the raster buffer is re-generated from modified drops
      paintBufferDirty = true;
    }
  }
}

// ----------------------------------------------------------------------
// MODIFIED: The pull stroke is now a path-based drag that is
//           tightly constrained by radial distance from the current mouse position.
/* --- Warp-based directional awl (vector strokes + raster warp + blending) --- */
function applyDirectionalAwl(x_start, y_start, x_end, y_end, radius = 20, strength = 0.25) {
  // x_start, y_start is the starting point (lx, ly)
  // x_end, y_end is the current point (x, y)

  const dx = x_end - x_start, dy = y_end - y_start;
  const len = Math.hypot(dx, dy);
  
  // Only apply a stroke if movement is non-negligible
  if (len < 0.0001) return;

  // --- VISCOSITY DAMPING (Kept) ---
  const dropCount = drops.length;
  // Strength decays with the amount of paint
  const viscosityFactor = 1.0 / (1.0 + Math.pow(dropCount, 0.4) * 0.08); 
  const dampedStrength = strength * viscosityFactor;
  // --- END VISCOSITY DAMPING ---
  
  // --- LOCALIZED CIRCULAR DRAG (Key Adjustments) ---
  
  // Max Displacement (z): proportional to path length for smooth drag
  const pathFactor = 1.0; 
  const z = dampedStrength * len * pathFactor; 
  
  // Falloff Scale: used as a sharpness factor *relative to the radius* in applyStrokeToPaintBuffer
  // Significantly reduced for sharper falloff.
  const scale = 0.005; // Remains 0.005 for sharper falloff

  // The stroke is still defined by the path (start, end) and the direction (M)
  // but the *spatial influence* will be circular (radius) and centered at 'B' (x_end, y_end).
  const stroke = makeStrokeFromLine(x_start, y_start, x_end, y_end, { z: z, u: pullU, scale: scale });

  // push stroke into composed strokes (order matters)
  strokes.push(stroke);

  // If raster buffer is stale, re-rasterize first, then warp it
  if (paintBufferDirty || !paintBufferInitialized) {
    rasterizeDropsToPaintBuffer();
  }

  // Apply stroke to paintBuffer (warp + blend)
  // The 'radius' argument is crucial here for the tight circular constraint
  applyStrokeToPaintBuffer(stroke, radius); 

  // commit warp to offscreen canvas
  const img = new ImageData(new Uint8ClampedArray(paintBuffer), NX, NY);
  offCtx.putImageData(img, 0, 0);

  // redraw display immediately (so pull is visible in both modes)
  updateCanvasPixelSizeIfNeeded();
  displayCtx.save();
  displayCtx.setTransform(1,0,0,1,0,0);
  displayCtx.clearRect(0,0,displayCanvas.width, displayCanvas.height);
  displayCtx.imageSmoothingEnabled = true;
  displayCtx.drawImage(offCanvas, 0, 0, displayCanvas.width, displayCanvas.height);
  displayCtx.restore();

  // After applying the stroke we mark buffer as the authoritative raster state
  paintBufferInitialized = true;
  paintBufferDirty = false;
}

/* applyPullStroke: adapter used by pointer handlers (uses awlRadius & pullStrength) */
function applyPullStroke(x_current, y_current) {
  if (!lastMouse) return; 
  
  const [x_start, y_start] = lastMouse; 

  const strength = pullStrength;
  const radius = awlRadius;
  // Call with start and end points of the stroke path
  applyDirectionalAwl(x_start, y_start, x_current, y_current, radius, strength);
}
// ----------------------------------------------------------------------

/* --- Animation loop --- */
function animate(){
  // ensure CSS size fits and pixel size is up to date
  fitCanvasCSS();
  updateCanvasPixelSizeIfNeeded();

  const t = nowSeconds();
  updateDropExpansion(t);

  if (mode === 'raster'){
    // ensure paintBuffer reflects drops unless we've intentionally warped it
    if (paintBufferDirty || !paintBufferInitialized){
      rasterizeDropsToPaintBuffer();
    } else {
      // paintBuffer already has current pixels (may have been warped)
      const img = new ImageData(new Uint8ClampedArray(paintBuffer), NX, NY);
      offCtx.putImageData(img, 0, 0);
    }

    // draw offCanvas into display canvas stretched to pixel size
    displayCtx.clearRect(0,0,displayCanvas.width, displayCanvas.height);
    displayCtx.imageSmoothingEnabled = true;
    displayCtx.drawImage(offCanvas, 0, 0, displayCanvas.width, displayCanvas.height);
  } else {
    // draw contour: scale the context so that NXxNY coords map to canvas pixels
    displayCtx.clearRect(0,0,displayCanvas.width, displayCanvas.height);
    displayCtx.save();
    const sx = displayCanvas.width / NX;
    const sy = displayCanvas.height / NY;
    displayCtx.scale(sx, sy);
    contourRender(drops, displayCtx, 1.0);
    displayCtx.restore();
  }

  requestAnimationFrame(animate);
}

/* --- Sizing, mapping & UI plumbing (unchanged with a few small additions) --- */

/* Fit display canvas CSS size to its container while preserving NX/NY aspect */
function fitCanvasCSS() {
  const container = displayCanvas.parentElement;
  const rect = container.getBoundingClientRect();
  const aspect = NX/NY;
  let w = rect.width - 24; if (w < 200) w = rect.width;
  let h = Math.round(w / aspect);
  if (h > rect.height) { h = rect.height; w = Math.round(h * aspect); }
  displayCanvas.style.width = w + 'px';
  displayCanvas.style.height = h + 'px';
}

/* Update actual canvas pixel size (only when CSS size changes) */
let lastRect = null;
function updateCanvasPixelSizeIfNeeded(){
  const rect = displayCanvas.getBoundingClientRect();
  if (!lastRect || lastRect.width !== rect.width || lastRect.height !== rect.height){
    lastRect = { width: rect.width, height: rect.height };
    const pw = Math.max(1, Math.round(rect.width * DPR));
    const ph = Math.max(1, Math.round(rect.height * DPR));
    displayCanvas.width = pw;
    displayCanvas.height = ph;
    // keep CSS size tied
    displayCanvas.style.width = rect.width + 'px';
    displayCanvas.style.height = rect.height + 'px';
    // reset any transform so drawImage uses pixel coords
    displayCtx.setTransform(1,0,0,1,0,0);
  }
}

/* Map mouse client coords -> NX/NY grid coords (CSS-aware) */
function toGridCoords(clientX, clientY){
  const rect = displayCanvas.getBoundingClientRect();
  const cssX = clientX - rect.left;
  const cssY = clientY - rect.top;
  const x = cssX * (NX / rect.width);
  const y = cssY * (NY / rect.height);
  return [x, y];
}

/* Mouse/interaction handling */
let mouseDown=false, lastMouse=null, autoInjectOnDrag=true;

/* Tool UI wiring */
const toolEls = Array.from(document.querySelectorAll('.tool'));
function setActiveTool(toolName){
  currentTool = toolName;
  toolEls.forEach(el => {
    el.classList.toggle('active', el.dataset.tool === toolName);
  });
  // show/hide comb controls
  const combPanel = document.getElementById('combControls');
  if (combPanel) combPanel.style.display = (toolName === 'comb') ? 'block' : 'none';
  const awlPanel = document.getElementById('awlControls');
  if (awlPanel) awlPanel.style.display = (toolName === 'awl' || toolName === 'pull') ? 'block' : 'none';
}
toolEls.forEach(el => {
  el.addEventListener('click', ()=>{
    setActiveTool(el.dataset.tool);
  });
});
// initialize tool UI
setActiveTool('drop');

/* Create comb controls in the left panel dynamically (and awl controls) */
(function createToolControlsUI(){
  const leftPanel = document.querySelector('.panel');
  if (!leftPanel) return;
  // create container and insert after controls-group
  const cg = document.querySelector('.controls-group');

  // Comb controls
  const combWrapper = document.createElement('div');
  combWrapper.id = 'combControls';
  combWrapper.style.marginTop = '12px';
  combWrapper.style.display = 'none';
  combWrapper.innerHTML = `
    <div style="font-weight:600;margin-bottom:8px">Comb Controls</div>
    <div class="control"><label>Comb Width</label><input id="combWidth" type="range" min="20" max="300" value="${combWidth}"></div>
    <div class="control"><label>Tine Spacing</label><input id="combSpacing" type="range" min="4" max="80" value="${combSpacing}"></div>
    <div class="control"><label>Tine Radius</label><input id="combTineRadius" type="range" min="2" max="32" value="${combTineRadius}"></div>
  `;
  if (cg && cg.parentNode) cg.parentNode.insertBefore(combWrapper, cg.nextSibling);

  // Awl / Pull controls
  const awlWrapper = document.createElement('div');
  awlWrapper.id = 'awlControls';
  awlWrapper.style.marginTop = '12px';
  awlWrapper.style.display = 'none';
  awlWrapper.innerHTML = `
    <div style="font-weight:600;margin-bottom:8px">Awl / Pull Controls</div>
    <div class="control"><label>Awl Radius</label><input id="awlRadius" type="range" min="4" max="200" value="${awlRadius}"></div>
    <div class="control"><label>Pull Strength</label><input id="pullStrength" type="range" min="1" max="100" value="${Math.round(pullStrength*100)}"></div>
  `;
  if (combWrapper && combWrapper.parentNode) combWrapper.parentNode.insertBefore(awlWrapper, combWrapper.nextSibling);

  // wire inputs
  const cw = document.getElementById('combWidth'), cs = document.getElementById('combSpacing'), ctr = document.getElementById('combTineRadius');
  if (cw) cw.addEventListener('input', (e)=>{ combWidth = +e.target.value; });
  if (cs) cs.addEventListener('input', (e)=>{ combSpacing = +e.target.value; });
  if (ctr) ctr.addEventListener('input', (e)=>{ combTineRadius = +e.target.value; });

  const aw = document.getElementById('awlRadius'), ps = document.getElementById('pullStrength');
  if (aw) aw.addEventListener('input', (e)=>{ awlRadius = +e.target.value; });
  if (ps) ps.addEventListener('input', (e)=>{ pullStrength = (+e.target.value) / 100.0; });
})();

/* Add pointer handlers (adapted per tool) */
displayCanvas.addEventListener('mousedown', (ev)=>{
  if (ev.button !== 0) return;
  mouseDown = true;
  updateCanvasPixelSizeIfNeeded();
  const [x,y] = toGridCoords(ev.clientX, ev.clientY);

  // Save state for any tool action that mutates drops
  saveState();

  if (currentTool === 'drop'){
    // brush-like scatter
    performBrushHit(x,y);
    lastMouse = [x,y];
  } else if (currentTool === 'awl'){
    // AWL as PAINT DROPPER: add a single drop at click
    addDropAt(x, y, mouseAddRadius);
    // ensure subsequent rasterization reflects this new drop
    paintBufferDirty = true;
    paintBufferInitialized = false;
    lastMouse = [x,y];
  } else if (currentTool === 'comb'){
    // start comb stroke
    lastMouse = [x,y];
  } else if (currentTool === 'pull'){
    // start pull stroke (prepare raster)
    if (paintBufferDirty || !paintBufferInitialized) rasterizeDropsToPaintBuffer();
    // lastMouse holds the starting point for stroke calculation (the origin of the delta)
    lastMouse = [x,y];
  }
});

window.addEventListener('mouseup', (ev)=>{
  if (mouseDown){
    // end of stroke; clear lastMouse
    lastMouse = null;
  }
  mouseDown = false;
});

displayCanvas.addEventListener('mousemove', (ev)=>{
  if (!mouseDown) return;
  const [x,y] = toGridCoords(ev.clientX, ev.clientY);

  if (currentTool === 'drop'){
    // continuous brush strokes: scatter small drops while dragging
    performBrushHit(x,y);
  } else if (currentTool === 'awl'){
    // AWL as dropper on drag: add drops while dragging (like a dropper brush)
    performAwlDropperHit(x,y);
  } else if (currentTool === 'comb' && lastMouse){
    // comb stroke: move paint according to tines and drag vector
    const [lx, ly] = lastMouse;
    const dx = x - lx, dy = y - ly;
    if (Math.hypot(dx, dy) > 0.0001){
      applyCombStroke(lx, ly, dx, dy);
    }
  } else if (currentTool === 'pull' && lastMouse){
    // ----------------------------------------------------------------------
    // Call applyPullStroke with current position. It will use lastMouse for start.
    const [lx, ly] = lastMouse;
    const dx = x - lx, dy = y - ly;
    if (Math.hypot(dx, dy) > 0.0001){
      // Apply the local stroke. 
      applyPullStroke(x, y);
    }
    // ----------------------------------------------------------------------
  }

  // Update lastMouse to current position for next delta calculation (for all tools)
  lastMouse = [x,y];
});

displayCanvas.addEventListener('wheel', (ev)=>{
  const delta = Math.sign(ev.deltaY);
  mouseAddRadius = Math.max(1, mouseAddRadius + delta * 2);
  ev.preventDefault();
}, {passive:false});

/* Keyboard */
window.addEventListener('keydown', (ev)=>{
  if (ev.key === '1') selectedColor = 0;
  if (ev.key === '2') selectedColor = 1;
  if (ev.key === '3') selectedColor = 2;
  if (ev.key === 'm'){ mode = (mode === 'contour') ? 'raster' : 'contour'; }
  if (ev.key === 'c' || ev.key === 'C'){ drops = []; paintBufferDirty = true; paintBufferInitialized = false; }
  if (ev.key === 'q' || ev.key === 'Escape'){ drops = []; paintBufferDirty = true; paintBufferInitialized = false; }
});

/* UI wiring (palette & controls) */
const paletteEl = document.getElementById('palette');
const defaultColors = ['#1f4f64','#b0836a','#8a7b6f','#ffffff','#2b2b2b','#d6e9e2'];
if (paletteEl) {
  for(const c of defaultColors){
    const s = document.createElement('div'); s.className='swatch'; s.style.background = c; s.title = c;
    s.addEventListener('click', ()=> {
      const cp = document.getElementById('colorPicker');
      if (cp) cp.value = c;
      const rgb = hexToRgb(c);
      let best = 0; let bestDist = Infinity;
      for(let i=0;i<colorList.length;i++){
        const cc = colorList[i];
        const d = Math.hypot(cc[0]*255 - rgb.r, cc[1]*255 - rgb.g, cc[2]*255 - rgb.b);
        if (d < bestDist){ bestDist = d; best = i; }
      }
      selectedColor = best;
    });
    paletteEl.appendChild(s);
  }
}
function hexToRgb(hex){
  const h = hex.replace('#','');
  return { r: parseInt(h.substring(0,2),16), g: parseInt(h.substring(2,4),16), b: parseInt(h.substring(4,6),16) };
}

const brushRadiusEl = document.getElementById('brushRadius');
if (brushRadiusEl) brushRadiusEl.addEventListener('input', (e)=>{ mouseAddRadius = +e.target.value; brushScatter = Math.max(6, +e.target.value * 0.9); });
const flowEl = document.getElementById('flow');
if (flowEl) flowEl.addEventListener('input', (e)=>{ flow = (+e.target.value)/100.0; });
const expandEl = document.getElementById('expand');
if (expandEl) expandEl.addEventListener('input', (e)=>{ growTime = (+e.target.value)/1000.0; });

const colorPickerEl = document.getElementById('colorPicker');
if (colorPickerEl) colorPickerEl.addEventListener('input', (e)=>{
  const hex = e.target.value; const rgb = hexToRgb(hex);
  const newcol = [rgb.r/255, rgb.g/255, rgb.b/255];
  colorList.push(newcol);
  selectedColor = colorList.length - 1;
});

/* performAwlDropperHit: called while awl tool drag to drop color */
function performAwlDropperHit(x, y){
  // Add a moderate-sized drop at pointer with full alpha (acts like dropping paint)
  addDropAt(x, y, mouseAddRadius, null, 1.0);
  // mark raster dirty so next rasterization will include this color if needed
  paintBufferDirty = true;
  paintBufferInitialized = false;
}

/* Undo / Redo buttons (enhanced) */
const undoEl = document.getElementById('undo');
if (undoEl) undoEl.addEventListener('click', () => {
  if (undoStack.length > 0) {
    redoStack.push(cloneDrops(drops));
    drops = undoStack.pop();
    paintBufferDirty = true;
    paintBufferInitialized = false;
    updateUndoRedoUI();
  }
});
const redoEl = document.getElementById('redo');
if (redoEl) redoEl.addEventListener('click', () => {
  if (redoStack.length > 0) {
    undoStack.push(cloneDrops(drops));
    drops = redoStack.pop();
    paintBufferDirty = true;
    paintBufferInitialized = false;
    updateUndoRedoUI();
  }
});

/* Export (unchanged, but kept here for completeness) */
const exportEl = document.getElementById('export');
if (exportEl) exportEl.addEventListener('click', ()=>{
  let tmp = document.createElement('canvas');
  tmp.width = NX; tmp.height = NY;
  let tctx = tmp.getContext('2d', {alpha:false});
  if (mode === 'raster'){
    // if we've warped the paintBuffer and want to export that, prefer paintBuffer
    if (paintBufferInitialized && !paintBufferDirty){
      const img = new ImageData(new Uint8ClampedArray(paintBuffer), NX, NY);
      tctx.putImageData(img, 0, 0);
    } else {
      const imgData = rasterRender(drops);
      tctx.putImageData(imgData, 0, 0);
    }
  } else {
    contourRender(drops, tctx, 1.0);
  }
  const url = tmp.toDataURL('image/png');
  const a = document.createElement('a'); a.href = url; a.download = 'ebru_export.png'; a.click();
});

/* Tool implementations */

/* Brush: scatter many small drops with reduced alpha */
function performBrushHit(x,y){
  // when called repeatedly while dragging, we add a few randomized small drops
  // do not call saveState here (it's done at mousedown)
  for(let i=0;i<brushCount;i++){
    const angle = Math.random() * Math.PI * 2;
    const rdist = Math.random() * brushScatter;
    const nx = x + Math.cos(angle) * rdist;
    const ny = y + Math.sin(angle) * rdist;
    const rsize = brushSizeMin + Math.random() * (brushSizeMax - brushSizeMin);
    addDropAt(nx, ny, rsize, null, brushAlpha);
  }
}

/* --- Init & start --- */
function init(){
  fitCanvasCSS();
  updateCanvasPixelSizeIfNeeded();
  updateUndoRedoUI();
  requestAnimationFrame(animate);
}
window.addEventListener('resize', ()=>{ fitCanvasCSS(); updateCanvasPixelSizeIfNeeded(); });
init();