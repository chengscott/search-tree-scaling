/* Browser-only interaction; no accounts, external scripts, or network services. */
(() => {
  'use strict';
  const lessons = window.LESSONS;
  const source = window.PROOF_SOURCE;
  const declarations = source.declarations;
  const codeLinks = window.PROOF_LINKS?.sha256 === source.sha256 ? window.PROOF_LINKS : null;
  const $ = selector => document.querySelector(selector);
  const esc = value => String(value).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
  // Trusted SVG output is generated locally from math-tex.cjs, never from input.
  const math = (label, display = true) => {
    const entry = window.PROOF_MATH?.[label];
    if (!entry) return esc(label);
    return `<span class="math-typeset ${display ? 'math-display' : 'math-inline'}" role="math" aria-label="${esc(label)}" title="${esc(entry.tex)}"><span aria-hidden="true">${entry[display ? 'display' : 'inline']}</span></span>`;
  };
  const richText = value => String(value).split(/(\$[^$]+\$)/g).map(part => {
    if (!part.startsWith('$') || !part.endsWith('$')) return esc(part);
    const tex = part.slice(1,-1);
    const svg = window.PROOF_INLINE_MATH?.[tex];
    if (!svg) return esc(tex);
    const width = Number(svg.match(/width="([\d.]+)ex"/)?.[1] || 0);
    const wide = width > 44;
    return `<span class="math-typeset math-inline${wide ? ' prose-math-wide' : ''}" role="math" aria-label="${esc(tex)}" title="${esc(tex)}"${wide ? ' tabindex="0"' : ''}><span aria-hidden="true">${svg}</span></span>`;
  }).join('');
  const main = $('#main');
  let toastTimeout;
  let activeRoute = '';
  const scrollPositions = new Map();
  if ('scrollRestoration' in history) history.scrollRestoration = 'manual';
  let searchQuery = '';
  let searchKind = 'all';
  const getDecl = name => declarations.find(d => d.qualified === name) || declarations.find(d => d.name === name) || declarations.find(d => d.qualified.endsWith('.' + name));
  const sourceHref = name => '#source/' + encodeURIComponent(getDecl(name)?.qualified || name);
  const refLink = name => `<a class="ref" href="${sourceHref(name)}">${esc(name)}</a>`;
  const sourceText = d => source.lines.slice(d.start - 1, d.end).join('\n');
  const heroArt = () => `<div class="hero-art" aria-label="Schematic search tree with the optimal path emphasized"><svg viewBox="0 0 395 220" role="img" aria-label="A branching search tree. The optimal path is highlighted in indigo."><g fill="none" stroke="#c7cfc0" stroke-width="1.2"><path d="M190 27L95 79M190 27L190 79M190 27L285 79M95 79L46 133M95 79L108 133M285 79L254 133M285 79L327 133M190 79L159 133M190 79L217 133M217 133L192 188M217 133L252 188M46 133L26 177M46 133L64 177M108 133L91 177M108 133L126 177"/></g><path d="M190 27L190 79L217 133L192 188" fill="none" stroke="#59669c" stroke-width="2.5"/><g fill="#eef0e8" stroke="#acb9a5"><circle cx="95" cy="79" r="8"/><circle cx="285" cy="79" r="8"/><circle cx="46" cy="133" r="6"/><circle cx="108" cy="133" r="6"/><circle cx="254" cy="133" r="6"/><circle cx="327" cy="133" r="6"/><circle cx="159" cy="133" r="6"/><circle cx="252" cy="188" r="6"/><circle cx="26" cy="177" r="3"/><circle cx="64" cy="177" r="3"/><circle cx="91" cy="177" r="3"/><circle cx="126" cy="177" r="3"/></g><g fill="#59669c" stroke="#f5f5ed" stroke-width="3"><circle cx="190" cy="27" r="9"/><circle cx="190" cy="79" r="8"/><circle cx="217" cy="133" r="8"/><circle cx="192" cy="188" r="7"/></g><g fill="#89928a" font-family="Georgia,serif" font-size="18"><text x="213" y="30">Root</text><text x="192" y="210" text-anchor="middle" fill="#59669c" font-size="18">the optimal path</text></g><path d="M354 24h6v164h-6" fill="none" stroke="#afb8a5"/><text x="368" y="113" text-anchor="start" fill="#778367" font-size="18" font-family="Georgia,serif">H</text></svg></div>`;

  function updateNav(page, id) {
    document.querySelectorAll('[data-page]').forEach(a => {
      const current = a.dataset.page === page;
      a.classList.toggle('active', current);
      if (current) a.setAttribute('aria-current','page'); else a.removeAttribute('aria-current');
    });
    let group = '';
    $('#lesson-nav').innerHTML = lessons.map((l, i) => {
      const heading = group !== l.group ? `<div class="group-title">${esc(l.group)}</div>` : '';
      group = l.group;
      return heading + `<a class="chapter-link ${l.id === id ? 'active' : ''}" ${l.id === id ? 'aria-current="page"' : ''} href="#lesson/${l.id}"><span class="chapter-number">${String(i + 1).padStart(2,'0')}</span><span>${esc(l.title)}</span></a>`;
    }).join('');
  }
  function overview() {
    $('#breadcrumb').textContent = 'Overview';
    main.innerHTML = `<section class="hero"><div><h1>Search-Tree Scaling<br><em>in Parallel Monte Carlo Tree Search</em></h1><p class="hero-copy"></p><div class="hero-actions"><a class="button primary" href="#lesson/${lessons[0].id}">Start the walkthrough <span>→</span></a><a class="text-link" href="#lesson/theorem1-1">Jump to Theorem 1(1) ↗</a></div></div>${heroArt()}</section>
    <section><div class="section-title"><h2>Exploration coefficient and parallelism</h2></div><div class="routes">
    <a class="route" href="#lesson/theorem1-1"><div class="route-index">01 / EXPLORATION COEFFICIENT <span>↗</span></div><h3>Constant exploration coefficient</h3><p>${richText(String.raw`Suboptimal visit counts and the maximum depth reached along the optimal path under a constant $c>0$.`)}</p><div class="math">${math('Hₒₚₜ(n) = Θ(√n)')}</div><div class="route-bottom"><span>Theorem 1 · Corollary 1.1</span><span>Explore →</span></div></a>
    <a class="route" href="#lesson/schedule"><div class="route-index">02 / EXPLORATION COEFFICIENT <span>↗</span></div><h3>General exploration coefficient</h3><p>${richText(String.raw`For $c(m)=O(\sqrt m)$, the integral gives the depth rate. For $c(m)=\Omega(\sqrt m)$, the rate is logarithmic.`)}</p><div class="math">${math('∫₁ⁿ dm/[c(m)√m]')}</div><div class="route-bottom"><span>Theorem 2 · Corollaries 2.1–2.3</span><span>Explore →</span></div></a>
    <a class="route" href="#lesson/parallel-model"><div class="route-index">03 / PARALLELISM <span>↗</span></div><h3>Tree-parallel MCTS</h3><p>${richText(String.raw`Under regularity and thread contention, with a constant exploration coefficient and $T=o(n)$, optimal-path depth has this rate until capped by a finite terminal depth.`)}</p><div class="math">${math('Hₒₚₜ(n,T) = Θ(n/(√n + T))')}</div><div class="route-bottom"><span>Lemma 4 · Theorems 3–4</span><span>Explore →</span></div></a>
    </div></section>
    <section class="map-section" aria-labelledby="proof-roadmap-title">
      <div class="section-title"><h2 id="proof-roadmap-title">From local dynamics to global depth bounds</h2></div>
      <p class="roadmap-intro">Under the assumptions of each result, the proofs compare pUCT scores, bound the difference between parent and optimal-child visit counts, and sum along the optimal path.</p>
      <ol class="proof-roadmap">
        <li class="roadmap-step"><span class="roadmap-number" aria-hidden="true">01</span><div class="roadmap-copy"><h3>Bound the suboptimal visit counts</h3><p>For a suboptimal action with positive prior, compare scores at its last selection for the upper bound, then at the last optimal selection for the lower bound.</p><a class="text-link" href="#lesson/theorem1-1">Follow Theorem 1(1) →</a></div><div class="roadmap-math"><p class="roadmap-context">For a constant exploration coefficient</p>${math('N(s,a) = Θ(√N(s))')}</div></li>
        <li class="roadmap-step"><span class="roadmap-number" aria-hidden="true">02</span><div class="roadmap-copy"><h3>Obtain the one-step estimates</h3><p>${richText(String.raw`Sum the suboptimal visit counts and account for the expansion visit. The comparison scale $g$ controls count losses or the corresponding edge integrals, depending on the schedule.`)}</p><a class="text-link" href="#lesson/depth-tools">From visits to depth →</a><p class="roadmap-qualification">For growing parallelism, the two-sided estimate also uses thread contention.</p></div><div class="roadmap-comparisons"><div><a href="#lesson/theorem1-2">Constant coefficient</a>${math('g(m) = √m',false)}</div><div><a href="#lesson/theorem2">General coefficient</a>${math('g(m) = min(c(m)√m, m)',false)}</div><div><a href="#lesson/lemma4">Parallelism · Lemma 4</a>${math('g(m) = √m + T',false)}</div></div></li>
        <li class="roadmap-step"><span class="roadmap-number" aria-hidden="true">03</span><div class="roadmap-copy"><h3>Sum along the optimal path</h3><p>Sum the edge integrals above a fixed count threshold. For general continuous schedules, logarithmic correction terms also telescope. Controlling these terms, the endpoint, and the remaining tail gives the depth estimate.</p><a class="text-link" href="#lesson/integrals">Follow the integral comparison →</a></div><div class="roadmap-math">${math('Hₒₚₜ(n) = Θ(∫₁ⁿ dm/g(m))')}<p class="roadmap-context">Choose the comparison function for the setting above.</p></div></li>
      </ol>
      <div class="roadmap-cap"><div><h3>Until capped by a finite terminal depth</h3><p>Under the corresponding hypotheses, the capped results show that the optimal path eventually reaches a fixed terminal depth.</p></div><a class="text-link" href="#lesson/caps">Read the finite-depth case →</a></div>
    </section>
    <div class="note-row"><div><strong>Read the mathematics and the code together.</strong>Every lesson links to exact source excerpts. The source explorer includes the entire file and all supporting declarations.</div><div><strong>The assumptions are part of the result.</strong>Each chapter states what it needs. Finite terminal depth, uniform convergence of value estimates, and thread contention have their own explanations.</div></div>
    <section class="map-section"><div class="section-title"><h2>A small notation guide</h2><a class="text-link" href="#source">Find a declaration →</a></div><div class="symbol-grid">${[['N(s)','Visit count at state s; written m in local proofs.'],['N(s,a)','Action visit count; written nᵢ for a suboptimal action and n* for the optimal action.'],['Nₓ / Vₓ','The paper uses Nₓ along a path. Lean uses Vₓ for arrival counts, including the initial expansion.'],['Hₒₚₜ / Hₘₐₓ','Maximum depth reached along the optimal path / maximum depth of the search tree.'],['f = Θ(g)','Eventually bounded above and below by positive multiples of g.'],['∀ᶠ t in atTop','A property holds for all sufficiently large t.']].map(([s,d])=>`<div class="symbol"><b>${math(s,false)}</b><p>${esc(d)}</p></div>`).join('')}</div></section>`;
  }

  function highlightPlain(line) {
    // Tokenize raw text first, then escape every token; source never becomes HTML.
    const commentAt = line.indexOf('--');
    const normal = commentAt >= 0 ? line.slice(0,commentAt) : line;
    const colored = normal.split(/(\b(?:theorem|lemma|structure|where|def|private|noncomputable|by|have|let|letI|obtain|intro|exact|apply|refine|simpa|simp|rw|constructor|filter_upwards|with|using|at|fun|by_contra|by_cases|rcases|induction|in|if|then|else|classical|omega|linarith|nlinarith|positivity|ring|dsimp|exact_mod_cast)\b|\b\d+\b)/g).map(t => /^\d+$/.test(t) ? `<span class="number">${esc(t)}</span>` : /^(theorem|lemma|structure|where|def|private|noncomputable|by|have|let|letI|obtain|intro|exact|apply|refine|simpa|simp|rw|constructor|filter_upwards|with|using|at|fun|by_contra|by_cases|rcases|induction|in|if|then|else|classical|omega|linarith|nlinarith|positivity|ring|dsimp|exact_mod_cast)$/.test(t) ? `<span class="kw">${esc(t)}</span>` : esc(t)).join('');
    return colored + (commentAt >= 0 ? `<span class="comment">${esc(line.slice(commentAt))}</span>` : '');
  }
  function highlight(line, lineNumber) {
    const spans = codeLinks?.lines[String(lineNumber)] || [];
    if (!spans.length) return highlightPlain(line);
    let html = '', cursor = 0;
    for (const [start, end, symbolIndex] of spans) {
      const symbol = codeLinks.symbols[symbolIndex];
      const external = symbol.kind === 'library';
      const destination = external ? (symbol.module.startsWith('Mathlib.') ? 'Mathlib documentation' : 'Lean documentation') : 'Project definition';
      const title = `${symbol.name} — ${destination}${external ? ' (opens in a new tab)' : ''}`;
      html += highlightPlain(line.slice(cursor, start));
      html += `<a class="code-link ${symbol.kind}" href="${esc(symbol.href)}" title="${esc(title)}" aria-label="${esc(title)}"${external ? ' target="_blank" rel="noopener noreferrer"' : ''}>${esc(line.slice(start, end))}</a>`;
      cursor = end;
    }
    return html + highlightPlain(line.slice(cursor));
  }
  function codeBlock(start, end, highlightAt = -1, caption = '') {
    return `<div class="code-pane"><div class="code-header"><span>MCTS.lean <span style="opacity:.6">/ ${start}–${end}</span></span><button type="button" data-copy-code data-start="${start}" data-end="${end}">Copy code</button></div><div class="code-scroll" tabindex="0" aria-label="Lean source code"><pre class="code-lines"><code>${source.lines.slice(start - 1,end).map((line, i) => `<span class="code-line ${start+i === highlightAt ? 'highlight' : ''}"><span class="line-num" aria-hidden="true">${start+i}</span>${highlight(line,start+i)}</span>`).join('')}</code></pre></div>${caption ? `<div class="code-caption" tabindex="0" aria-label="Source links and navigation hint">${caption}<span class="code-link-hint">Underlined names link to definitions · library links open a new tab ↗</span></div>` : ''}</div>`;
  }
  function lessonView(id) {
    const l = lessons.find(l => l.id === id);
    if (!l) { location.hash = '#overview'; return; }
    const paper = window.PAPER_STATEMENTS?.[id];
    const statement = paper
      ? `<section class="paper-statement" aria-labelledby="lesson-title"><div class="statement-body">${paper.html}</div></section>`
      : `<div class="result-banner"><div class="label">${id === 'caps' ? 'Finite terminal depth in Lean' : 'Proof ingredient'}</div><div class="math">${math(l.result)}</div></div>`;
    $('#breadcrumb').textContent = l.group;
    const number = lessons.indexOf(l) + 1;
    const stepLocations = l.steps.map(s => {
      const d = getDecl(s.ref);
      const markerIndex = s.marker && d ? source.lines.findIndex((line,i) => i >= d.start-1 && i < d.end && line.includes(s.marker)) : -1;
      return { declaration: d, focus: markerIndex >= 0 ? markerIndex + 1 : d.start };
    });
    const steps = l.steps.map((s, index) => {
      const { declaration, focus } = stepLocations[index];
      const boundaries = [...new Set(stepLocations.filter(location => location.declaration === declaration).map(location => location.focus))].sort((left, right) => left - right);
      const start = focus === boundaries[0] ? declaration.start : focus;
      const end = (boundaries.find(boundary => boundary > focus) || declaration.end + 1) - 1;
      const code = codeBlock(start,end,focus,`<a href="${sourceHref(s.ref)}" style="color:#d3daf2">Read the full declaration ↗</a>`);
      return `<section class="walkthrough" id="step-${index}" aria-labelledby="step-title-${index}"><article class="explanation"><div class="step-kicker">STEP ${index+1}</div><h2 id="step-title-${index}">${esc(s.title)}</h2>${s.body.split('\n\n').map(p=>`<p>${richText(p)}</p>`).join('')}${s.hideEquation ? '' : `<div class="step-equation">${math(s.equation)}</div>`}</article>${code}</section>`;
    }).join('');
    main.innerHTML = `<section class="lesson-head"><h1 id="lesson-title">${esc(l.title)}</h1>${paper ? '' : `<p>${richText(l.subtitle)}</p>`}</section>
    ${statement}
    <div class="lesson-steps">${steps}</div>
    <div class="lesson-bottom"><span>Explore the source</span>${l.refs.map(refLink).join('')}</div>
    <nav class="chapter-controls" aria-label="Chapter navigation">${number > 1 ? `<a class="button" href="#lesson/${lessons[number-2].id}">← Previous chapter</a>` : '<a class="button" href="#overview">← Overview</a>'}<a class="button primary" id="next-chapter" href="${number < lessons.length ? '#lesson/'+lessons[number].id : '#overview'}">${number < lessons.length ? 'Next chapter →' : 'Back to overview →'}</a></nav>`;
  }
  function toast(message) { $('#toast').textContent=message; $('#toast').classList.add('toast-show'); clearTimeout(toastTimeout); toastTimeout=setTimeout(()=>$('#toast').classList.remove('toast-show'),2200); }
  function attachCopy() {
    main.querySelectorAll('[data-copy-code]').forEach(button => {
      button.onclick = async () => {
        const text = source.lines.slice(Number(button.dataset.start)-1, Number(button.dataset.end)).join('\n');
        try { await navigator.clipboard.writeText(text); toast('Lean source copied'); }
        catch { toast('Clipboard unavailable. Select code to copy manually.'); }
      };
    });
  }
  function sourceView(name) {
    const lineMatch = (name || '').match(/\/L([1-9]\d*)$/);
    const requestedLine = lineMatch ? Number(lineMatch[1]) : -1;
    const declarationName = lineMatch ? name.slice(0,lineMatch.index) : name;
    const decoded = (()=>{try{return decodeURIComponent(declarationName||'');}catch{return null;}})();
    const all = decoded === 'all';
    const d = decoded === '' ? declarations[0] : getDecl(decoded);
    $('#breadcrumb').textContent='Source explorer';
    if (!all && !d) {
      main.innerHTML = `<section class="explorer-header"><h1>Declaration not found</h1><p>This source link does not match a declaration in the bundled proof.</p><a class="button" href="#source">Browse the source →</a></section>`;
      return;
    }
    const description = all ? 'Full source snapshot. Download it from the footer to compile in the original Lean project.' : d.doc.trim();
    main.innerHTML=`<section class="explorer-header"><h1>Look inside the proof.</h1><p>Search ${declarations.length} declarations by name or source text.</p></section><div class="search-row"><input id="source-search" class="search-input" type="search" placeholder="Search declarations, tactics, or hypotheses…" aria-label="Search Lean declarations" value="${esc(searchQuery)}"><select id="kind-filter" aria-label="Declaration type"><option value="all">All declarations</option><option value="theorem">Theorems</option><option value="def">Definitions</option><option value="structure">Structures</option></select><a class="button" href="#source/all" style="white-space:nowrap">Entire file ↗</a></div><div class="source-layout"><div><div id="search-count" role="status" aria-live="polite" class="step-meta" style="margin-bottom:9px"></div><nav class="declaration-list" id="declarations" aria-label="Lean declarations"></nav></div><section class="source-detail"><h2>${all?'MCTS.lean':esc(`${d.kind} ${d.name}`)}</h2>${description?`<p class="source-description">${esc(description)}</p>`:''}${codeBlock(all?1:d.start,all?source.lines.length:d.end,requestedLine,'Source viewer · explanatory site, not a live Lean session')}<div id="related" class="source-related"></div></section></div>`;
    $('#kind-filter').value=searchKind;
    function results() {
      const query=searchQuery.toLowerCase().trim();
      const filtered=declarations.filter(x=>(searchKind==='all'||x.kind===searchKind)&&(!query||x.qualified.toLowerCase().includes(query)||x.doc.toLowerCase().includes(query)||sourceText(x).toLowerCase().includes(query)));
      $('#search-count').textContent=`${filtered.length} ${filtered.length===1?'declaration':'declarations'}`;
      $('#declarations').innerHTML=filtered.length?filtered.map(x=>`<a class="declaration-item ${!all&&x.qualified===d.qualified?'active':''}" href="${sourceHref(x.qualified)}"><b>${esc(x.name)}</b><small>${x.kind} · lines ${x.start}–${x.end}</small></a>`).join(''):'<div class="empty">No declarations match. Try a shorter term or choose all declaration types.</div>';
    }
    $('#source-search').addEventListener('input',e=>{searchQuery=e.target.value;results();});
    $('#kind-filter').addEventListener('change',e=>{searchKind=e.target.value;results();});
    results();
    if (requestedLine > 0) {
      const highlighted = main.querySelector('.source-detail .code-line.highlight');
      const scroller = main.querySelector('.source-detail .code-scroll');
      if (highlighted && scroller) scroller.scrollTop = Math.max(0, highlighted.offsetTop - 35);
    }
    if(!all) {
      const referencedNames = new Set();
      if (codeLinks) for (let line=d.start;line<=d.end;line++) {
        for (const [, , index] of codeLinks.lines[String(line)] || []) {
          const symbol = codeLinks.symbols[index];
          if (symbol.kind === 'project') referencedNames.add(decodeURIComponent(symbol.href.split('/')[1]));
        }
      }
      const referenced=declarations.filter(x=>x.qualified!==d.qualified && referencedNames.has(x.qualified));
      const guides=lessons.filter(l=>l.refs.some(r=>getDecl(r)?.qualified===d.qualified));
      $('#related').innerHTML=(guides.length?`<span style="width:100%;font-size:14px;color:var(--muted)">Guided explanations</span>${guides.map(l=>`<a class="ref" href="#lesson/${l.id}">${esc(l.title)} →</a>`).join('')}`:'')+(referenced.length?`<span style="width:100%;font-size:14px;color:var(--muted);margin-top:10px">Referenced project declarations</span>${referenced.map(x=>refLink(x.qualified)).join('')}`:'');
    }
  }

  function lab() {
    $('#breadcrumb').textContent='Scaling lab';
    const panels = [
      {
        id:'exploration', title:'General exploration coefficient',
        description:String.raw`For $c(m)=m^\alpha$, the general depth estimate combines $\log n$ with the exploration integral. At $\alpha=1/2$, the integral becomes $\log n$.`,
        parameterLabel:'Exploration exponent α', maximum:1, initial:.25,
        formula:'S(n) = log n + ∫₁ⁿ m⁻ᵅ⁻½ dm', curve:'log n + ∫₁ⁿ m⁻ᵅ⁻½ dm', proof:'corollary22',
        explanation:a=>a<.5
          ? String.raw`For $\alpha<1/2$, the comparison function is $\Theta(n^{1/2-\alpha})$. Near the boundary, its growth at finite simulation counts can still look logarithmic.`
          : a===.5
            ? String.raw`At $\alpha=1/2$, the integral is exactly $\log n$, so the displayed comparison function is $2\log n$.`
            : String.raw`For $\alpha>1/2$, the integral approaches a finite limit. The logarithmic contribution continues to grow, giving the depth rate $\Theta(\log n)$.`
      },
      {
        id:'parallel', title:'General parallelism',
        description:String.raw`For tree-parallel MCTS with a constant exploration coefficient, regularity and thread contention give optimal-path depth $H_{\mathrm{opt}}(n,T(n))=\Theta(n/(\sqrt n+T(n)))$ when $T(n)=o(n)$, until capped by a finite terminal depth. Here $n$ is the simulation count and $T(n)=\lfloor n^\tau\rfloor$ is the thread count, with $0\le\tau<1$. The curve shows the comparison function, not an exact depth or a runtime speedup.`,
        parameterLabel:'Thread exponent τ', maximum:.95, initial:.6,
        formula:'R(n) = n / (√n + ⌊nᵗ⌋)', curve:'n / (√n + T(n))', proof:'theorem4',
        explanation:a=>a<.5
          ? String.raw`For $\tau<1/2$, the thread count grows more slowly than $\sqrt n$. The depth rate remains $\Theta(\sqrt n)$.`
          : a===.5
            ? String.raw`At $\tau=1/2$, the two denominator terms are comparable, and the depth rate is still $\Theta(\sqrt n)$.`
            : String.raw`For $1/2<\tau<1$, the thread count dominates $\sqrt n$. The depth rate becomes $\Theta(n/T(n))$.`
      }
    ];
    main.innerHTML=`<section class="explorer-header"><h1>Exploration and parallelism</h1><p>Adjust each panel independently to explore the asymptotic depth estimates. Curves show comparison functions; the theorems relate them to depth up to constant factors.</p></section>
      <div class="lab-panels">${panels.map(panel=>`<section class="lab-panel" id="lab-${panel.id}" aria-labelledby="${panel.id}-title">
        <header class="lab-panel-header"><h2 id="${panel.id}-title">${esc(panel.title)}</h2><p>${richText(panel.description)}</p></header>
        <div class="lab-layout"><div class="lab-controls">
          <label for="${panel.id}-exponent">${esc(panel.parameterLabel)} <output data-role="parameter-value" for="${panel.id}-exponent"></output></label>
          <input id="${panel.id}-exponent" data-role="parameter" type="range" min="0" max="${panel.maximum}" step=".01" value="${panel.initial}">
          <label for="${panel.id}-simulations"><span>${richText(String.raw`Simulation count $n$`)}</span> <output data-role="simulation-value" for="${panel.id}-simulations"></output></label>
          <input id="${panel.id}-simulations" data-role="simulations" type="range" min="2" max="7" step=".1" value="4">
          <div class="lab-formula">${math(panel.formula)}</div>
          <p class="lab-explanation" data-role="explanation"></p>
          <a class="text-link lab-proof-link" href="#lesson/${panel.proof}">Read the corresponding proof →</a>
        </div><div class="lab-chart">
          <div class="section-title"><h3>Comparison functions</h3><span class="step-meta">LOG–LOG AXES</span></div>
          <div class="chart-scroll" tabindex="0" aria-label="Scrollable comparison chart"><svg class="lab-plot" data-role="chart" viewBox="0 0 580 335" role="img" aria-label="${esc(panel.title)} comparison functions on logarithmic axes"></svg></div>
          <div class="legend"><span><i></i>${math(panel.curve,false)}</span><span><i class="green"></i>${richText(String.raw`$\sqrt n$ reference`)}</span></div>
          <p class="lab-explanation" data-role="value" role="status" aria-live="polite"></p>
          <p class="lab-limit">Constants and thresholds from the theorem are not estimated here.</p>
        </div></div>
      </section>`).join('')}</div>`;
    for (const panel of panels) {
      const scope=$('#lab-'+panel.id);
      const get=role=>scope.querySelector(`[data-role="${role}"]`);
      const parameter=get('parameter'), simulations=get('simulations');
      function draw() {
        const parallel=panel.id==='parallel';
        const a=Number(parameter.value),n=Math.round(10**Number(simulations.value));
        const rate=x=>parallel
          ? x/(Math.sqrt(x)+Math.max(1,Math.floor(x**a)))
          : Math.log(x)+(Math.abs(.5-a)<1e-9?Math.log(x):Math.expm1((.5-a)*Math.log(x))/(.5-a));
        get('parameter-value').textContent=a.toFixed(2);
        get('simulation-value').textContent=n.toLocaleString();
        parameter.setAttribute('aria-valuetext',a.toFixed(2));
        simulations.setAttribute('aria-valuetext',`${n.toLocaleString()} simulations`);
        get('explanation').innerHTML=richText(panel.explanation(a));
        const xp=x=>52+(Math.log10(x)-1)/6*498;
        const yp=y=>285-(Math.log10(Math.max(y,.1))+1)/5*256;
        const curve=f=>Array.from({length:181},(_,i)=>{const x=10**(1+i/180*6);return `${i?'L':'M'}${xp(x).toFixed(2)},${yp(f(x)).toFixed(2)}`;}).join(' ');
        const fmtPower=k=>k===0?'1':`10<tspan dy="-0.4em" font-size="14">${k}</tspan>`;
        let grid='';
        for(let k=1;k<=7;k++){const x=xp(10**k);grid+=`<line x1="${x}" x2="${x}" y1="29" y2="285" stroke="#e7e9e1"/><text x="${x}" y="307" text-anchor="middle">${fmtPower(k)}</text>`;}
        for(let k=-1;k<=4;k++){const y=yp(10**k);grid+=`<line x1="52" x2="550" y1="${y}" y2="${y}" stroke="#e7e9e1"/><text x="40" y="${y+4}" text-anchor="end">${fmtPower(k)}</text>`;}
        get('chart').innerHTML=`<g fill="#66725e" font-size="18" font-family="sans-serif">${grid}<text x="305" y="331" text-anchor="middle">simulation count n</text></g><path d="${curve(Math.sqrt)}" fill="none" stroke="#75a18c" stroke-width="2" stroke-dasharray="5 5"/><path data-curve="rate" d="${curve(rate)}" fill="none" stroke="#4b558f" stroke-width="2.6"/><line x1="${xp(n)}" x2="${xp(n)}" y1="29" y2="285" stroke="#bbc0d4" stroke-dasharray="3 4"/><circle cx="${xp(n)}" cy="${yp(rate(n))}" r="5" fill="#4b558f" stroke="#fff" stroke-width="2"/>`;
        get('value').textContent=`At n = ${n.toLocaleString()}, the comparison function is ${rate(n).toLocaleString(undefined,{maximumFractionDigits:2})}${parallel?`, with T = ${Math.floor(n**a).toLocaleString()}`:''}.`;
      }
      parameter.addEventListener('input',draw);
      simulations.addEventListener('input',draw);
      draw();
    }
  }
  const mobileNavigation = window.matchMedia('(max-width: 800px)');
  function setMenu(open, restoreFocus = false) {
    const sidebar = $('#sidebar');
    sidebar.classList.toggle('open', open && mobileNavigation.matches);
    sidebar.inert = mobileNavigation.matches && !open;
    $('#menu').setAttribute('aria-expanded', String(open && mobileNavigation.matches));
    if (open && mobileNavigation.matches) {
      (sidebar.querySelector('.chapter-link.active') || sidebar.querySelector('a'))?.focus();
    } else if (restoreFocus && mobileNavigation.matches) $('#menu').focus();
  }
  function route() {
    const hash=location.hash || '#overview';
    if (activeRoute) scrollPositions.set(activeRoute, window.scrollY);
    const parts=(hash.replace(/^#/,'')||'overview').split('/');
    const page=parts[0];
    updateNav(page,parts[1]);
    if(page==='lesson')lessonView(parts[1]);
    else if(page==='source')sourceView(parts.slice(1).join('/'));
    else if(page==='lab'){location.replace('../figures/lab.html');return;}
    else overview();
    attachCopy();
    document.title=`${page === 'lesson' ? lessons.find(l=>l.id===parts[1])?.title || $('#breadcrumb').textContent : $('#breadcrumb').textContent} · Search-Tree Scaling`;
    setMenu(false);
    if (activeRoute && activeRoute !== hash) main.focus({preventScroll:true});
    window.scrollTo({top:scrollPositions.get(hash) || 0,behavior:'instant'});
    // Previously shared step URLs are anchors into the fully expanded chapter.
    if(page==='lesson' && /^\d+$/.test(parts[2] || '') && Number(parts[2]) > 0 && !scrollPositions.has(hash)) {
      document.getElementById(`step-${Number(parts[2])}`)?.scrollIntoView({block:'start'});
    }
    activeRoute=hash;
  }
  $('#menu').onclick=()=>setMenu(!$('#sidebar').classList.contains('open'));
  mobileNavigation.addEventListener('change',()=>setMenu(false));
  document.addEventListener('click',e=>{if(mobileNavigation.matches&&!e.target.closest('#sidebar')&&!e.target.closest('#menu'))setMenu(false);});
  document.addEventListener('keydown',e=>{
    if(e.key==='Escape' && $('#sidebar').classList.contains('open'))setMenu(false,true);
  });
  $('#decl-count').textContent=declarations.length;
  window.addEventListener('hashchange',route);
  route();
})();
