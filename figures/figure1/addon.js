/* Figure 1 add-on, loaded after the explorer's app.js (copied to figures/figure1/addon.js by the build).
   Reuses the explorer's top-level helpers (lookup, gameRecords, stepTree, draw, options, prettify, S/T/P).
   - lays the controls out as a toolbar above the tree; "Play steps" and its speed control sit on the tree panel's row
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

  const play = document.createElement('button'); play.type = 'button'; play.id = 'playSteps'; play.textContent = 'Play steps';
  const speedWrap = document.createElement('label'); speedWrap.className = 'ctl-speed';
  speedWrap.innerHTML = '<span>Speed</span><input id="playSpeed" type="range" min="1" max="10" step="1" value="3" aria-label="Playback speed, steps per second"><output id="playSpeedValue">3 steps/s</output>';
  const speed = speedWrap.querySelector('input'), speedOut = speedWrap.querySelector('output');
  speed.addEventListener('input', () => { speedOut.textContent = `${speed.value} steps/s`; });

  const visits = $('visits')?.closest('label'), exportBtn = $('export');  // look these up before anything is detached
  options_.append(...[aside.querySelector('.actions')].filter(Boolean));
  const playGroup = document.createElement('div'); playGroup.className = 'ctl-play'; playGroup.append(play, speedWrap);
  // "Size nodes by visits" and "Export SVG" act on the drawn tree, so they live on the tree panel's own row.
  const viewActions = document.querySelector('.tree-panel .view-actions');
  if (viewActions) { if (visits) viewActions.prepend(visits); if (exportBtn) viewActions.append(exportBtn); viewActions.append(playGroup); }
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

  /* ---------- playback ---------- */
  let timer = null;
  const stop = () => { clearTimeout(timer); timer = null; play.textContent = 'Play steps'; };
  const shownStep = () => { const m = /recorded search step (\d+)/.exec($('provenance')?.textContent || ''); return m ? +m[1] : -1; };
  const advance = () => {
    if (+step.value >= +step.max) { stop(); return; }
    step.value = +step.value + 1;
    step.dispatchEvent(new Event('input', { bubbles: true }));
    const target = +step.value, started = Date.now(), interval = 1000 / +speed.value;
    const wait = () => {
      if (!timer) return;
      const ready = shownStep() === target || Date.now() - started > 2500;
      if (ready) timer = setTimeout(advance, Math.max(0, interval - (Date.now() - started)));
      else timer = setTimeout(wait, 40);
    };
    timer = setTimeout(wait, 40);
  };
  play.addEventListener('click', () => {
    if (timer) { stop(); return; }
    if (+step.value >= +step.max) step.value = 0;
    play.textContent = 'Pause'; advance();
  });
  ['game', 'snapshotPreset', 'puct', 'simulation', 'threads'].forEach(id => $(id)?.addEventListener('input', stop));
  step.addEventListener('pointerdown', stop);

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
