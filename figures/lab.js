/* Scaling lab: two slider panels for the asymptotic depth results (Theorem 2 / Corollary 2.2 and Theorem 4).
   Each panel plots the depth expression of the active regime, up to constants, on log-log axes. */
(() => {
  'use strict';
  const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
  const typeset = el => { if (el && window.renderMathInElement) renderMathInElement(el, { delimiters: [{ left: '\\[', right: '\\]', display: true }, { left: '\\(', right: '\\)', display: false }], throwOnError: false }); };
  const R = String.raw;

  // Slowly varying factors L(m) for c(m) = m^alpha L(m); each is positive on [1, inf). tex(v) writes L in the variable v.
  const M0 = Math.E ** 2;  // integrals and curves for log-based L start here, where log log m > 0; it only shifts depth by a constant
  const L_CHOICES = {
    one: { label: '1', tex: () => '1', f: () => 1, m0: 1 },
    log: { label: 'log m', tex: v => R`\log ${v}`, f: m => Math.log(m), m0: M0 },
    log2: { label: '(log m)²', tex: v => R`(\log ${v})^{2}`, f: m => Math.log(m) ** 2, m0: M0 },
    loglog: { label: 'log log m', tex: v => R`\log\log ${v}`, f: m => Math.log(Math.log(m)), m0: M0 },
    invlog: { label: '1 / log m', tex: v => R`(\log ${v})^{-1}`, f: m => 1 / Math.log(m), m0: M0 },
  };

  const PANELS = [
    {
      id: 'exploration', tag: '(a)', title: 'Exploration schedule', proof: 'corollary22',
      theorem: R`<p><strong>Theorem 2</strong> (General exploration coefficient \(c(\cdot)\)). Consider an MCTS search tree of \(n\) simulations satisfying Assumption 1 (regularity). Suppose that the exploration coefficient function \(c(\cdot)\) of the parent visit count is positive and continuous, and \(c(m)\sqrt m\) is eventually nondecreasing. If \(c(m)=O(\sqrt m)\), the maximum depth along the optimal path satisfies
        \[ H_{\mathrm{opt}}(n)=\Theta\!\left(\int_1^n \frac{1}{c(m)\sqrt m}\,dm\right). \]
        If \(c(m)=\Omega(\sqrt m)\), then \(H_{\mathrm{opt}}(n)=\Theta(\log n)\). Both hold until capped by a finite terminal depth.</p>
        <p><strong>Corollary 2.2</strong>. Under the common assumptions of Theorem 2, suppose further that \(c(m)=m^{\alpha}L(m)\), where \(L\) is positive and slowly varying. Then, \(\alpha\ge-\tfrac12\), and</p>
        <div class="lab-cases">
          <div class="lab-case" data-case="lt">\(H_{\mathrm{opt}}(n)=\Theta\big(\sqrt n/c(n)\big)\)<span>\(-\tfrac12\le\alpha<\tfrac12\)</span></div>
          <div class="lab-case" data-case="eq">\(H_{\mathrm{opt}}(n)=\Theta\big(\log n+\int_1^n \frac{dm}{m\,L(m)}\big)\)<span>\(\alpha=\tfrac12\)</span></div>
          <div class="lab-case" data-case="gt">\(H_{\mathrm{opt}}(n)=\Theta(\log n)\)<span>\(\alpha>\tfrac12\)</span></div>
        </div>
        <p>All estimates hold until capped by a finite terminal depth.</p>`,
      parameterLabel: R`Exploration exponent \(\alpha\)`, max: 1, initial: .25,
    },
    {
      id: 'parallel', tag: '(b)', title: 'Search threads', proof: 'theorem4',
      theorem: R`<p><strong>Theorem 4</strong> (General parallelism). Consider tree-parallel MCTS with a constant exploration coefficient \(c>0\), \(T=T(n)\) concurrent threads, and \(n\) simulations, under Assumptions 1 (regularity) and 2 (thread contention). Then, as \(n\to\infty\), we have
        \[ H_{\mathrm{opt}}(n,T)=\Theta\!\left(\int_1^n \frac{dm}{\sqrt m+T}\right), \]
        until capped by a finite terminal depth. In particular,</p>
        <div class="lab-cases">
          <div class="lab-case" data-case="small">\(H_{\mathrm{opt}}(n,T)=\Theta(\sqrt n)\)<span>if \(T=o(\sqrt n)\)</span></div>
          <div class="lab-case" data-case="large">\(H_{\mathrm{opt}}(n,T)=\Theta(n/T)\)<span>if \(T\gg\sqrt n\)</span></div>
        </div>`,
      parameterLabel: R`Thread exponent \(\tau\) in \(T(n)=\lfloor n^{\tau}\rfloor\)`, max: .95, initial: .6,
    },
  ];

  const root = document.getElementById('labPanels');
  root.innerHTML = PANELS.map(p => `<section class="lab-panel" id="lab-${p.id}" aria-labelledby="${p.id}-title">
      <header class="lab-panel-header"><h3 id="${p.id}-title"><span class="panel-tag">${p.tag}</span>${esc(p.title)}</h3>
        <div class="lab-theorem">${p.theorem}</div></header>
      <div class="lab-layout">
        <div class="lab-controls">
          <label for="${p.id}-exponent"><span>${p.parameterLabel}</span><output data-role="parameter-value" for="${p.id}-exponent"></output></label>
          <input id="${p.id}-exponent" data-role="parameter" type="range" min="0" max="${p.max}" step=".01" value="${p.initial}">
          ${p.id === 'exploration' ? `<label for="${p.id}-L" class="lab-select"><span>Slowly varying factor \\(L(m)\\)</span><select id="${p.id}-L" data-role="L">${Object.entries(L_CHOICES).map(([k, v]) => `<option value="${k}">${esc(v.label)}</option>`).join('')}</select></label>` : ''}
          <label for="${p.id}-simulations"><span>Simulation count \\(n\\)</span><output data-role="simulation-value" for="${p.id}-simulations"></output></label>
          <input id="${p.id}-simulations" data-role="simulations" type="range" min="0" max="7" step=".1" value="4">
          ${p.id === 'exploration' ? '<div class="lab-formula lab-formula-c" data-role="formula-c"></div>' : ''}
          <div class="lab-formula" data-role="formula"></div>
          <a class="lab-proof-link" href="../proof/index.html#lesson/${p.proof}">Read the corresponding proof <span aria-hidden="true">→</span></a>
        </div>
        <div class="lab-chart">
          <div class="chart-scroll" tabindex="0" aria-label="Scrollable depth chart"><svg class="lab-plot" data-role="chart" viewBox="-22 0 602 335" role="img" aria-label="${esc(p.title)}: asymptotic depth on logarithmic axes"></svg></div>
          <div class="lab-legend"><span><i></i>\\(H_{\\mathrm{opt}}\\) up to constants</span><span><i class="ref"></i>\\(\\sqrt n\\) reference</span></div>
          <p class="lab-explanation lab-value" data-role="value" role="status" aria-live="polite"></p>
          <p class="lab-limit">The curve is the expression inside \\(\\Theta(\\cdot)\\). The theorem fixes \\(H_{\\mathrm{opt}}\\) only up to constant factors and only asymptotically, so the curve shows the growth rate, not a predicted depth.</p>
        </div>
      </div>
    </section>`).join('');

  const U_MAX = Math.log(1e7), N_GRID = 1400;
  // Cumulative integral of g(u) du on a uniform grid over u = ln m in [0, U_MAX] (trapezoid).
  const cumulative = (g, u0) => { const h = (U_MAX - u0) / N_GRID, out = new Float64Array(N_GRID + 1); let prev = g(u0); for (let i = 1; i <= N_GRID; i++) { const v = g(u0 + i * h); out[i] = out[i - 1] + (prev + v) * h / 2; prev = v; } out.u0 = u0; return out; };
  const interp = (table, u) => { const t = Math.min(Math.max(u - table.u0, 0), U_MAX - table.u0) / (U_MAX - table.u0) * N_GRID, i = Math.min(Math.floor(t), N_GRID - 1); return table[i] + (table[i + 1] - table[i]) * (t - i); };
  const fmt = v => v.toLocaleString(undefined, { maximumFractionDigits: 2 });

  for (const p of PANELS) {
    const scope = document.getElementById('lab-' + p.id);
    const get = role => scope.querySelector(`[data-role="${role}"]`);
    const parameter = get('parameter'), simulations = get('simulations'), Lsel = get('L');
    const parallel = p.id === 'parallel';
    let tableKey = null, table = null;
    const draw = () => {
      const a = Number(parameter.value), n = Math.round(10 ** Number(simulations.value));
      let depth, formula, cFormula = '', regime, extra = '', m0 = 1;
      if (parallel) {
        const T = x => Math.max(1, Math.floor(x ** a));
        // int_1^n dm / (sqrt m + T) in closed form, with T = T(n).
        depth = x => { const t = T(x), s = Math.sqrt(x); return 2 * (s - 1) - 2 * t * Math.log((s + t) / (1 + t)); };
        regime = a < .5 ? 'small' : a > .5 ? 'large' : null;
        formula = R`\[ H_{\mathrm{opt}}(n,T)=\Theta\!\left(\int_1^n \frac{dm}{\sqrt m+T}\right) \]`;
        extra = `, with T = ${T(n).toLocaleString()} threads`;
      } else {
        const L = L_CHOICES[Lsel.value]; m0 = L.m0;
        const lower = m0 === 1 ? '1' : 'e^{2}';
        regime = a < .5 ? 'lt' : a === .5 ? 'eq' : 'gt';
        if (regime === 'lt') {
          depth = x => x ** (.5 - a) / L.f(x);
          formula = R`\[ H_{\mathrm{opt}}(n)=\Theta\big(\sqrt n/c(n)\big)=\Theta\big(n^{1/2-\alpha}` + (L.tex('n') === '1' ? '' : '/' + L.tex('n')) + R`\big) \]`;
        } else if (regime === 'eq') {
          const key = Lsel.value;
          if (key !== tableKey) { tableKey = key; table = cumulative(u => 1 / L.f(Math.exp(u)), Math.log(m0)); }  // int dm/(m L(m)) = int du / L(e^u)
          depth = x => Math.log(x) + interp(table, Math.log(x));
          formula = R`\[ H_{\mathrm{opt}}(n)=\Theta\Big(\log n+\int_{` + lower + R`}^n \frac{dm}{m` + (L.tex('m') === '1' ? '' : R`\,` + L.tex('m')) + R`}\Big) \]`;
        } else {
          depth = x => Math.log(x);
          formula = R`\[ H_{\mathrm{opt}}(n)=\Theta(\log n) \]`;
        }
        cFormula = `\\[ c(m)=m^{${a.toFixed(2)}}` + (L.tex('m') === '1' ? '' : L.tex('m')) + `\\]`;
      }
      get('parameter-value').textContent = a.toFixed(2);
      get('simulation-value').textContent = n.toLocaleString();
      parameter.setAttribute('aria-valuetext', a.toFixed(2));
      simulations.setAttribute('aria-valuetext', `${n.toLocaleString()} simulations`);
      scope.querySelectorAll('.lab-case').forEach(el => el.classList.toggle('active', el.dataset.case === regime));
      for (const [role, tex] of [['formula', formula], ['formula-c', cFormula]]) { const f = get(role); if (f && f.dataset.tex !== tex) { f.dataset.tex = tex; f.innerHTML = tex; typeset(f); } }
      const xp = x => 52 + Math.log10(x) / 7 * 498;
      const yp = y => 285 - Math.log10(Math.max(y, 1)) / 4 * 256;
      const curve = (g, x0 = 1) => Array.from({ length: 211 }, (_, i) => { const x = x0 * (1e7 / x0) ** (i / 210); return `${i ? 'L' : 'M'}${xp(x).toFixed(2)},${yp(g(x)).toFixed(2)}`; }).join(' ');
      const pow = k => k === 0 ? '1' : `10<tspan dy="-0.45em" font-size="9">${k}</tspan>`;
      let grid = '';
      for (let k = 0; k <= 7; k++) { const x = xp(10 ** k); grid += `<line x1="${x}" x2="${x}" y1="29" y2="285" stroke="#e6e6e0"/><text x="${x}" y="307" text-anchor="middle">${pow(k)}</text>`; }
      for (let k = 0; k <= 4; k++) { const y = yp(10 ** k); grid += `<line x1="52" x2="550" y1="${y}" y2="${y}" stroke="#e6e6e0"/><text x="40" y="${y + 4}" text-anchor="end">${pow(k)}</text>`; }
      get('chart').innerHTML = `<g fill="#71818a" font-size="12" font-family="Inter, system-ui, sans-serif">${grid}</g><g fill="#4c5b61" font-size="14" font-weight="700" font-family="Inter, system-ui, sans-serif"><text x="305" y="331" text-anchor="middle">Simulation count n</text><text transform="translate(-6 157) rotate(-90)" text-anchor="middle">Depth</text></g>`
        + `<path d="${curve(Math.sqrt)}" fill="none" stroke="#7aa58d" stroke-width="2" stroke-dasharray="5 5"/>`
        + `<path data-curve="depth" d="${curve(depth, m0)}" fill="none" stroke="#4b558f" stroke-width="2.8"/>`
        + `<line x1="${xp(n)}" x2="${xp(n)}" y1="29" y2="285" stroke="#bbc0d4" stroke-dasharray="3 4"/>`
        + (n >= m0 ? `<circle cx="${xp(n)}" cy="${yp(depth(n))}" r="5.5" fill="#4b558f" stroke="#fff" stroke-width="2"/>` : '');
      get('value').textContent = n >= m0 ? `At n = ${n.toLocaleString()} the plotted expression equals ${fmt(depth(n))}${extra}.` : `n = ${n.toLocaleString()} is below the starting point m\u2080 = e\u00b2 \u2248 7.4 for this factor.`;
    };
    parameter.addEventListener('input', draw);
    simulations.addEventListener('input', draw);
    if (Lsel) Lsel.addEventListener('change', draw);
    draw();
  }
  const typesetAll = () => document.querySelectorAll('.lab-theorem, .lab-controls label, .lab-formula, .lab-legend, .lab-limit').forEach(typeset);
  if (window.renderMathInElement) typesetAll(); else window.addEventListener('load', typesetAll);
})();
