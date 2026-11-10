/* Figure 1 add-on, loaded after the explorer's app.js (copied to figures/figure1/addon.js by the build).
   Reuses the explorer's top-level helpers (lookup, gameRecords, stepTree, draw, options, prettify, S/T/P).
   - lays the controls out as a toolbar above the tree; "Play" (over step, simulation count, threads or exploration coefficient) and its speed control sit on the tree panel's row
   - replaces the fixed "Compare corners" grid with four always-visible, individually configurable panels */
(() => {
  'use strict';
  if (typeof lookup === 'undefined' || typeof stepTree !== 'function' || typeof draw !== 'function') return;
  const $ = id => document.getElementById(id);
  const aside = document.querySelector('.workspace > aside');
  const step = $('searchStep');
  if (!aside || !step || !$('game')) return;

  /* ---------- toolbar ---------- */
  const field = (...nodes) => { const d = document.createElement('div'); d.className = 'ctl-field'; nodes.forEach(n => n && d.append(n)); return d; };
  const top = document.createElement('div'); top.className = 'ctl-row ctl-top';
  const sliders = document.createElement('div'); sliders.className = 'ctl-row ctl-sliders';
  const options_ = document.createElement('div'); options_.className = 'ctl-options';

  const play = document.createElement('button'); play.type = 'button'; play.id = 'playSteps'; play.textContent = 'Play';
  const axisWrap = document.createElement('label'); axisWrap.className = 'ctl-axis';
  axisWrap.innerHTML = '<span>over</span><select id="playAxis" aria-label="Parameter to animate"><option value="searchStep">Step</option><option value="simulation">Simulations</option><option value="threads" selected>Threads</option><option value="puct">Exploration</option></select>';
  const axisSel = axisWrap.querySelector('select');
  const speedWrap = document.createElement('label'); speedWrap.className = 'ctl-speed';
  speedWrap.innerHTML = '<span>Speed</span><input id="playSpeed" type="range" min="1" max="10" step="1" value="3" aria-label="Playback speed, frames per second"><output id="playSpeedValue">3 frames/s</output>';
  const speed = speedWrap.querySelector('input'), speedOut = speedWrap.querySelector('output');

  const visits = $('visits')?.closest('label'), exportBtn = $('export');  // look these up before anything is detached
  options_.append(...[aside.querySelector('.actions')].filter(Boolean));
  const playGroup = document.createElement('div'); playGroup.className = 'ctl-play'; playGroup.append(play, axisWrap, speedWrap);
  // "Size nodes by visits" and "Export SVG" act on the drawn tree, so they live on the tree panel's own row.
  const viewActions = document.querySelector('.tree-panel .view-actions');
  // Playback leads the row (left); the three view tools sit at the right and wrap below it when narrow.
  if (viewActions) { if (visits) viewActions.prepend(visits); if (exportBtn) viewActions.append(exportBtn); viewActions.prepend(playGroup); }
  top.append(field(aside.querySelector('label[for="game"]'), $('game')), field(aside.querySelector('.snapshot-picker')), options_);
  sliders.append(...aside.querySelectorAll('.control'));
  aside.prepend(top, sliders);
  [$('modelOptions'), $('notice')].filter(Boolean).forEach(n => aside.append(n));
  aside.classList.add('ctl-toolbar');
  $('compareToggle')?.remove();

  /* ---------- intro: folded by default, pUCT formula typeset ---------- */
  const intro = document.querySelector('.intro');
  if (intro && !intro.querySelector('.intro-toggle')) {
    intro.classList.add('is-folded');
    const b = document.createElement('button');
    b.type = 'button'; b.className = 'intro-toggle'; b.textContent = 'About this figure'; b.setAttribute('aria-expanded', 'false');
    b.addEventListener('click', () => { const f = intro.classList.toggle('is-folded'); b.textContent = f ? 'About this figure' : 'Hide'; b.setAttribute('aria-expanded', String(!f)); });
    (intro.querySelector('h2') || intro).after(b);
  }
  const typeset = () => { if (window.renderMathInElement) { const intro = document.querySelector('.intro'); if (intro) renderMathInElement(intro, { delimiters: [{ left: '\\[', right: '\\]', display: true }, { left: '\\(', right: '\\)', display: false }], throwOnError: false }); } };
  typeset(); window.addEventListener('load', typeset);

  /* ---------- playback over any slider ----------
     "Play" sweeps the chosen slider (game step, simulation count, threads or exploration coefficient) from its current
     value upward, one archived setting per frame; unarchived combinations are skipped, never shown empty. Parameter sweeps
     hold one viewport (the union of every frame's layout box, each frame centred) so the tree visibly grows or shrinks;
     refitting per frame would draw every tree at the same size. */
  const AXES = {
    searchStep: { el: step, speed: 3, unit: 'steps/s' },
    simulation: { el: $('simulation'), speed: 3, unit: 'frames/s', opt: 'budget', values: () => S },
    threads: { el: $('threads'), speed: 3, unit: 'frames/s', opt: 'threads', values: () => T },
    puct: { el: $('puct'), speed: 3, unit: 'frames/s', opt: 'c', values: () => (mode === 'real' ? P : [0, 1, 2, 3, 4]) },
  };
  const axisOptions = (axis, i) => { const a = AXES[axis], o = options(); return a.opt ? { ...o, [a.opt]: a.values()[i] } : o; };
  const recordFor = o => lookup.get([o.game, o.budget, o.threads, o.c].join(':'));
  const frames = axis => {
    const a = AXES[axis], all = Array.from({ length: +a.el.max + 1 }, (_, i) => i);
    if (axis === 'searchStep') return a.el.disabled || mode !== 'real' ? [] : all;
    return mode === 'real' ? all.filter(i => recordFor(axisOptions(axis, i))) : all;
  };
  const expected = () => { const o = options(); return `c=${o.c} · simulations=${o.budget} · threads=${o.threads} · ${mode === 'real' ? `episode 1, recorded search step ${o.step}` : 'illustrative model'}`; };
  const shown = () => $('provenance')?.textContent || '';

  let active = false, timer = null, driving = false, held = null, session = 0;
  const speedLabel = () => { speedOut.textContent = `${speed.value} ${AXES[axisSel.value].unit}`; };
  const refreshAxes = () => {
    for (const opt of axisSel.options) opt.disabled = frames(opt.value).length < 2;
    const n = frames(axisSel.value).length;
    play.disabled = n < 2 && !active;
    play.title = n < 2 ? 'Fewer than two recorded settings along this axis for the current selection' : '';
  };
  const stop = () => { active = false; clearTimeout(timer); timer = null; held = null; session++; play.textContent = 'Play'; play.setAttribute('aria-pressed', 'false'); refreshAxes(); };
  const setSlider = (el, v) => { driving = true; try { el.value = v; el.dispatchEvent(new Event('input', { bubbles: true })); } finally { driving = false; } };
  // Hold the viewport during a parameter sweep: same scale for every frame, each frame centred horizontally.
  const applyHold = () => { if (held && fullBox) { viewBox = [fullBox[0] - (held[2] - fullBox[2]) / 2, held[1], held[2], held[3]]; $('treeSvg').setAttribute('viewBox', viewBox.join(' ')); } };
  const drawMain = draw;
  draw = function (svg, flat, isMain = false) {
    const r = drawMain(svg, flat, isMain);
    if (isMain) { applyHold(); refreshAxes(); }
    return r;
  };
  const frameNodes = async (axis, i) => {
    const o = axisOptions(axis, i);
    if (mode !== 'real') return engine.runTree(o).nodes;
    const rec = recordFor(o); if (!rec) return null;
    return stepTree(rec, Math.min(o.step, (rec.stepCount || 1) - 1));
  };
  const unionBox = async (axis, idxs) => {
    let w = 0, h = 0;
    for (const i of idxs) {
      let nodes = null; try { nodes = await frameNodes(axis, i); } catch { /* skipped frame */ }
      if (!nodes?.length) continue;
      const b = layout(nodes).box; w = Math.max(w, b[2]); h = Math.max(h, b[3]);
    }
    return w && h ? [0, 0, w, h] : null;
  };
  const run = async () => {
    const mine = ++session, axis = axisSel.value, a = AXES[axis], all = frames(axis), cur = +a.el.value;
    let queue = all.filter(i => i > cur); if (!queue.length) queue = all;
    if (axis !== 'searchStep') {
      play.textContent = 'Loading…';
      const box = await unionBox(axis, [cur, ...queue]);
      if (!active || mine !== session) return;
      held = box; applyHold();  // start frame at the shared scale, then hold one interval before moving on
    }
    play.textContent = 'Pause';
    const advance = () => {
      if (!active || mine !== session) return;
      if (!queue.length) { stop(); return; }
      setSlider(a.el, queue.shift());
      const started = Date.now(), interval = 1000 / +speed.value;
      const wait = () => {
        if (!active || mine !== session) return;
        const s = shown(), ready = s.startsWith(expected()) || s.startsWith('No recorded tree') || Date.now() - started > 4000;
        timer = setTimeout(ready ? advance : wait, ready ? Math.max(0, interval - (Date.now() - started)) : 40);
      };
      timer = setTimeout(wait, 40);
    };
    if (held) timer = setTimeout(advance, 1000 / +speed.value); else advance();
  };
  play.addEventListener('click', () => {
    if (active) { stop(); return; }
    if (frames(axisSel.value).length < 2) return;
    active = true; play.setAttribute('aria-pressed', 'true'); run();
  });
  speed.addEventListener('input', speedLabel);
  axisSel.addEventListener('input', () => { stop(); speed.value = AXES[axisSel.value].speed; speedLabel(); });
  ['game', 'snapshotPreset', 'puct', 'simulation', 'threads', 'searchStep'].forEach(id => $(id)?.addEventListener('input', () => { if (!driving) stop(); }));
  step.addEventListener('pointerdown', stop);
  ['reset', 'realMode', 'modelMode'].forEach(id => $(id)?.addEventListener('click', stop));
  speedLabel(); refreshAxes();

  /* ---------- comparison lab ---------- */
  const old = $('comparison'); if (old) old.remove();
  const lab = document.createElement('section'); lab.className = 'compare-lab'; lab.id = 'compareLab';
  lab.innerHTML = '<div class="compare-lab-head"><h3>Compare settings</h3><button type="button" id="cmpReset">Reset to corners</button></div><div class="compare-lab-grid"></div>';
  const grid = lab.querySelector('.compare-lab-grid');
  (document.querySelector('.workspace') || aside.parentElement).after(lab);

  const uniq = (records, key) => [...new Set(records.map(r => r[key]))].sort((a, b) => a - b);
  const nearest = (values, want) => values.reduce((best, v) => Math.abs(v - want) < Math.abs(best - want) ? v : best, values[0]);
  const corners = [{ c: 0, t: 1 }, { c: 5, t: 1 }, { c: 0, t: 32 }, { c: 5, t: 32 }];

  const panels = corners.map((corner, i) => {
    const card = document.createElement('article'); card.className = 'cmp-card';
    card.innerHTML = `<div class="cmp-config">
        <label><span>Game</span><select data-k="game"></select></label>
        <label><span>Simulation count</span><select data-k="sim"></select></label>
        <label><span>Search threads</span><select data-k="threads"></select></label>
        <label><span>Exploration coefficient</span><select data-k="puct"></select></label>
      </div><div class="cmp-canvas"><div class="cmp-empty" hidden>No recorded tree for this setting.</div></div><div class="stats cmp-stats"><div><span>Nodes</span><strong>—</strong></div><div><span>Max depth</span><strong>—</strong></div><div><span>Leaves</span><strong>—</strong></div><div><span>Mean node depth</span><strong>—</strong></div></div>`;
    grid.append(card);
    const sel = Object.fromEntries([...card.querySelectorAll('select')].map(s => [s.dataset.k, s]));
    const p = { card, sel, corner, dirty: false, gen: 0 };
    sel.game.append(...[...gameRecords.keys()].sort().map(g => new Option(prettify(g), g)));
    Object.values(sel).forEach(s => s.addEventListener('change', () => { p.dirty = true; if (s === sel.game) fill(p, true); render(p); }));
    return p;
  });

  function fill(p, keepValues) {
    const records = gameRecords.get(p.sel.game.value) || [];
    for (const k of ['sim', 'threads', 'puct']) {
      const values = uniq(records, k), prev = +p.sel[k].value;
      p.sel[k].replaceChildren(...values.map(v => new Option(String(v), String(v))));
      const want = keepValues && !Number.isNaN(prev) ? prev : (k === 'sim' ? options().budget : k === 'threads' ? p.corner.t : p.corner.c);
      if (values.length) p.sel[k].value = String(nearest(values, want));
    }
  }
  function setFromMain(p) {
    const o = options();
    p.sel.game.value = o.game;
    fill(p, false);
    p.dirty = false;
  }

  async function render(p) {
    const gen = ++p.gen;
    const canvas = p.card.querySelector('.cmp-canvas'), empty = canvas.querySelector('.cmp-empty'), cells = p.card.querySelectorAll('.cmp-stats strong');
    const setStats = st => { const v = st ? [st.nodes.toLocaleString(), st.depth, st.leaves.toLocaleString(), st.mean.toFixed(2)] : ['—', '—', '—', '—']; cells.forEach((c, i) => { c.textContent = v[i]; }); };
    canvas.querySelector('svg')?.remove();
    const key = [p.sel.game.value, +p.sel.sim.value, +p.sel.threads.value, +p.sel.puct.value].join(':');
    const record = lookup.get(key);
    if (!record) { empty.hidden = false; setStats(null); return; }
    const s = Math.min(+step.value, (record.stepCount || 1) - 1);
    let nodes = null;
    try { nodes = s === 0 ? record.nodes : await stepTree(record, s); } catch (e) { nodes = null; }
    if (gen !== p.gen) return;
    if (!nodes) { empty.hidden = false; empty.textContent = 'Step archive could not be loaded.'; setStats(null); return; }
    empty.textContent = 'No recorded tree for this setting.';
    empty.hidden = true;
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('role', 'img');
    svg.setAttribute('aria-label', `${prettify(record.game)}, ${record.sim} simulations, ${record.threads} threads, c=${record.puct}, step ${s}`);
    canvas.append(svg);
    setStats(draw(svg, nodes) || (typeof metrics === 'function' ? metrics(nodes) : null));
  }

  const renderAll = () => panels.forEach(render);
  let rerenderTimer = null;
  const scheduleAll = () => { clearTimeout(rerenderTimer); rerenderTimer = setTimeout(renderAll, 80); };
  step.addEventListener('input', scheduleAll);
  ['game', 'simulation', 'snapshotPreset'].forEach(id => $(id)?.addEventListener('input', () => {
    panels.forEach(p => { if (!p.dirty) setFromMain(p); });
    scheduleAll();
  }));
  $('cmpReset').addEventListener('click', () => { panels.forEach(setFromMain); renderAll(); });
  panels.forEach(setFromMain);
  renderAll();

  /* ---------- default exploration coefficient 1.25 (the common pUCT default) ---------- */
  const defaultC = () => {
    const i = (typeof P !== 'undefined' ? P : [0, .5, 1.25, 2.5, 5]).indexOf(1.25);
    if (i >= 0 && $('puct')) { $('puct').value = i; $('puct').dispatchEvent(new Event('input', { bubbles: true })); }
  };
  defaultC();
  $('reset')?.addEventListener('click', () => setTimeout(defaultC, 0));
})();
