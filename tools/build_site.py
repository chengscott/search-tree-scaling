#!/usr/bin/env python3
"""Assemble the public demo site from the two existing interactive demos.

Sources (override with flags):
  --figures-src  <figure explorer folder>            (interactive figures source)
  --proof-src    <proof-walkthrough dist folder>     (Lean proof walkthrough source)

Output (inside the repository root, next to index.html):
  figures/   runtime copy of the explorer, Figure 1 trimmed to --max-steps steps
  proof/     copy of the proof walkthrough dist/, paper statements synced to camera_ready/main.tex

The full Figure 1 step archive is 3.7 GB / 78k files, above the 1 GB GitHub Pages
limit for a single site. Each recorded setting is stored in 32-step chunks.

  * Without --data-shards, this script keeps the chunks covering steps
    [0, max_steps) and rewrites snapshots.js so the UI only offers shipped steps.
  * With --data-shards N, the complete archive is split into N "data mirror"
    folders (each its own GitHub Pages site, ~3.7 GB / N), settings are assigned
    whole to a mirror by greedy bin packing, and snapshots.js records a per-setting
    base URL. The first max_steps steps are still shipped locally for a fast path;
    later steps load on demand from the mirror when the slider reaches them.

Step 0 of every setting is embedded in snapshots.js and is always available.
"""
import argparse
import json
import re
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SITE_BAR_META = 'Interactive figures 1–4 · NeurIPS 2026'


# User-visible wording fixes applied to copied explorer files. The paper speaks of "simulation count" /
# "simulations", never of a "budget". JS identifiers such as o.budget are left untouched.
WORDING = [
    ('Explore how search budgets, exploration and parallelism change', 'Explore how simulation counts, exploration and parallelism change'),
    ('Simulation budget <small>SIMULATIONS</small>', 'Simulation count <small>SIMULATIONS</small>'),
    ('<span>Small budget</span><span>More nodes</span>', '<span>Fewer simulations</span><span>More simulations</span>'),
    ('Four corners at a fixed search budget', 'Four corners at a fixed simulation count'),
    ('Same budget, different shapes.', 'Same simulation count, different shapes.'),
    ('Threads exceed the budget; the batch is capped by remaining simulations.', 'Threads exceed the simulation count; the batch is capped by remaining simulations.'),
    ('${sims.length} simulation budgets', '${sims.length} simulation counts'),
    ('Single-budget experiments remain isolated points.', 'Experiments with a single simulation count remain isolated points.'),
    ('Some settings have only isolated budgets.', 'Some settings have only isolated simulation counts.'),
    ('Differences are more apparent at larger budgets.', 'Differences are more apparent at larger simulation counts.'),
    ('up to 44 games per budget', 'up to 44 games per simulation count'),
    ('because low-budget vs400 matches can have zero wins', 'because low-simulation-count vs400 matches can have zero wins'),
    ('8 episodes per budget', '8 episodes per simulation count'),
    ('<title>Figure 1 · Search-Tree Scaling</title>', '<title>Search trees · Search-Tree Scaling</title>'),
    ('<label for="threads">Parallel search <small>THREADS</small>', '<label for="threads">Search threads <small>THREADS</small>'),
    ('<label for="searchStep">Recorded step <small>EPISODE 1 · ZERO-BASED</small>', '<label for="searchStep">Game step <small>EPISODE 1 · ZERO-BASED</small>'),
    ('n=${r.sim} · threads=${r.threads} · PUCT=${r.puct}', '${r.sim} simulations · ${r.threads} threads · c=${r.puct}'),
    ('n=${n}: ${records.filter(r=>r.sim===n).length} settings', '${n} simulations: ${records.filter(r=>r.sim===n).length} settings'),
    ('No recorded tree for n=${o.budget}, t=${o.threads}, c=${o.c}. Choose an available setting.', 'No recorded tree for ${o.budget} simulations, ${o.threads} threads, c=${o.c}. Choose an available setting.'),
    ('<p class="sub">Explore how simulation counts, exploration and parallelism change the shape of a search tree.</p>',
     '<p class="sub">The trees below were recorded from pUCT searches on Atari games. Each simulation descends from the root, choosing at every state \\(s\\) the action with the highest pUCT score (right): the value estimate \\(Q(s,a)\\) plus an exploration bonus that scales with the coefficient \\(c\\), the policy prior \\(P(s,a)\\) and the visit counts \\(N(s)\\) and \\(N(s,a)\\). A larger \\(c\\) spreads simulations over more actions, so the tree grows wider and shallower. More search threads do the same implicitly, since threads descend before earlier results are backed up. Choose a game, simulation count, thread count and \\(c\\) to browse the recorded trees.</p>'),
    ('<div class="formula">argmax <i>Q(s,a)</i> + <span>c</span> · <i>P(s,a)</i> √N / (1 + n)</div>',
     '<div class="formula">\\[ a^{*} = \\arg\\max_{a}\\; Q(s,a) + c \\, P(s,a)\\, \\frac{\\sqrt{N(s)}}{1 + N(s,a)} \\]</div>'),
    ('Box plots summarize search depth across 44 Atari games. Select games to compare their depth trajectories with the paper model.',
     'Theorem 2: with an exploration schedule \\\\(c(m)\\\\), the depth of the optimal path grows as \\\\(H_{\\\\mathrm{opt}}(n)=\\\\Theta\\\\big(\\\\int_1^n \\\\frac{dm}{c(m)\\\\sqrt m}\\\\big)\\\\). MuZero\'s exploration schedule (right) grows like \\\\(\\\\log m\\\\), giving \\\\(H_{\\\\mathrm{opt}}(n)=\\\\Theta(\\\\sqrt n/\\\\log n)\\\\). The red curve fits \\\\(a\\\\sqrt n/\\\\log n\\\\) to the empirical depth over 44 Atari games (\\\\(a\\\\approx 3.004\\\\), RMSE 4.10).'),
    ('<p class="control-title">Parallel threads</p>', '<p class="control-title">Search threads</p>'),
    # Figure 1 shows recorded trees only; the synthetic "illustrative model" mode is retired.
    ('<p>The illustrative model runs seeded PUCT and virtual loss in your browser. It does not run Atari inference or produce experiment scores.</p>', ''),
    ('Recorded mode shows observed trees; the illustrative model supports continuous coefficients and search animations.', 'Every tree shown is an observed search tree from the recorded experiments.'),
    ('Inspect archived trees from recorded experiments. Choose a search step within the first recorded episode.', 'Inspect archived trees from recorded experiments. Choose a search step within the first recorded episode.'),
]


PATH_RE = re.compile(r"/data/[^\"'\s,;<>)\]]*")
_path_hits = [0]


# Targeted source patches for the explorer's app.js (each must match exactly once).
APP_PATCHES = [
    # Threads: drop the 6-thread chip (keeping the original colour per thread count); "Paper selection" becomes "Select all" (same eight values).
    ("      const threadValues = [1, 2, 4, 6, 8, 16, 32, 64, 128];",
     "      const threadValues = [1, 2, 4, 8, 16, 32, 64, 128], threadColorIndex = value => [1, 2, 4, 6, 8, 16, 32, 64, 128].indexOf(value);"),
    ("<span class=\"chip-dot\" style=\"background:${THREAD_COLORS[index]}\"></span>${value}</label>`).join(\"\")}",
     "<span class=\"chip-dot\" style=\"background:${THREAD_COLORS[threadColorIndex(value)]}\"></span>${value}</label>`).join(\"\")}"),
    ("          </div><p class=\"control-description\">The paper shows 1, 2, 4, 8, 16, 32, 64 and 128 threads. The CSV also contains 6 threads.</p>\n"
     "          <div class=\"inline-actions\"><button type=\"button\" data-action=\"thread-paper\">Paper selection</button><button type=\"button\" data-action=\"thread-clear\">Clear</button></div></section>`;",
     "          </div><div class=\"inline-actions\"><button type=\"button\" data-action=\"thread-paper\">Select all</button><button type=\"button\" data-action=\"thread-clear\">Clear</button></div></section>`;"),
    # Tooltip: the Unicode-subscript "cₚᵤcₜ" has no glyphs in the site fonts; use a real subscript like the control title.
    ('addTooltip(target, `<strong>${isPuct ? "cₚᵤcₜ" : "threads"} = ${group}</strong>',
     'addTooltip(target, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong>'),
    # Only Figure 3 remains on this page (Figures 2 and 4 are dropped from the site).
    ("  function renderNotes() {\n", "  function renderNotes() {\n    return;  // notes, sources and the paper-reference image are not shown on this site\n"),
    ("    el(\"paperReference\").src = meta.reference;\n", ""),
    ("    figure: [2, 3, 4].includes(Number(location.hash.slice(1))) ? Number(location.hash.slice(1)) : 2,", "    figure: 3,"),
    ("if ([2, 3, 4].includes(value) && value !== state.figure) setFigure(value);", "if (value === 3 && value !== state.figure) setFigure(value);"),
    ('    history.replaceState(null, "", `#${figure}`);\n', ''),
    ("download(`figure_${state.figure}${charts.length > 1 ? `_${index ? \"threads\" : \"puct\"}` : \"\"}.svg`", "download(`tree_shape${charts.length > 1 ? `_${index + 1}` : \"\"}.svg`"),
    ("download(`figure_${state.figure}_visible_data.csv`", "download(`tree_shape_data.csv`"),
    ("    document.title=`Figure ${figure} · Search-Tree Scaling`;", "    document.title=`${FIGURE_META[figure].title} · Search-Tree Scaling`;"),
    ('      description: "At 400 Go simulations, compare depth distributions as the exploration coefficient or thread count changes. Select the settings to display.",',
     '      description: "Depth distributions of Go search trees. Panel (a) varies the exploration coefficient \\\\(c\\\\) at 400 simulations; panel (b) varies the thread count \\\\(T\\\\) at 50 to 1600 simulations. A larger \\\\(c\\\\) or more threads shifts visits toward shallower nodes, the contention regime of Theorem 4 where depth grows only as \\\\(\\\\Theta(n/T)\\\\). Use the chips to pick settings and hover a legend entry to highlight one curve.",'),
    # Thread panel per simulation count (50-1600); 400 keeps the paper data, the rest come from data.js threadsBySim.
    ("  function distributionPanel(kind) {\n    const isPuct = kind === \"puct\";\n    const data = isPuct ? DATA.figure3.puct : DATA.figure3.threads;",
     "  const FIGURE3_SIMS = [50, 100, 200, 400, 800, 1600];\n  const threadsAt = sim => sim === 400 ? DATA.figure3.threads : ((DATA.figure3.threadsBySim || {})[sim] || []);\n"
     "  function distributionPanel(kind, sim = 400) {\n    const isPuct = kind === \"puct\";\n    const data = isPuct ? DATA.figure3.puct : threadsAt(sim);"),
    ("        const elo = isPuct ? DATA.figure3.puctElo[String(group)] : DATA.figure3.threadElo[String(group)];",
     "        const elo = isPuct ? DATA.figure3.puctElo[String(group)] : (sim === 400 ? DATA.figure3.threadElo[String(group)] : null);"),
    # Figure 3: per-panel legend with hover highlight (applied after the tooltip/elo patches above).
    ('    allGroups.forEach((group, index) => {\n      if (!selected.has(String(group))) return;\n      const values = data.filter(point => point.group === group && point.depth <= xmax).sort((a, b) => a.depth - b.depth);\n      const color = colors[index];\n      add(svg, "path", { d: pathFrom(values.map(point => [x(point.depth), y(point.value)])), fill: "none", stroke: color, "stroke-width": 2.7, "stroke-linejoin": "round", "stroke-linecap": "round" });\n      values.forEach(point => {\n        const target = add(svg, "circle", { cx: x(point.depth), cy: y(point.value), r: 5, fill: "transparent", stroke: "none" });',
     '    const series = new Map();\n    allGroups.forEach((group, index) => {\n      if (!selected.has(String(group)) || !data.some(point => point.group === group)) return;\n      const values = data.filter(point => point.group === group && point.depth <= xmax).sort((a, b) => a.depth - b.depth);\n      const color = colors[index];\n      const g = add(svg, "g", { class: "series", "data-group": String(group) }); series.set(String(group), g);\n      add(g, "path", { d: pathFrom(values.map(point => [x(point.depth), y(point.value)])), fill: "none", stroke: color, "stroke-width": 2.7, "stroke-linejoin": "round", "stroke-linecap": "round" });\n      values.forEach(point => {\n        const target = add(g, "circle", { cx: x(point.depth), cy: y(point.value), r: 5, fill: "transparent", stroke: "none" });'),
    ('        addTooltip(target, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong><br>Depth ${point.depth}<br>Node share ${fmt(point.value * 100, 2)}%<br><span class="soft">Samples ${point.samples.toLocaleString()} moves${elo == null ? "" : ` · ${fmt(elo, 1)} Elo`}</span>`);\n      });\n    });\n    return svg;\n  }',
     '        addTooltip(target, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong><br>Depth ${point.depth}<br>Node share ${fmt(point.value * 100, 2)}%<br><span class="soft">Samples ${point.samples.toLocaleString()} moves${elo == null ? "" : ` · ${fmt(elo, 1)} Elo`}</span>`);\n      });\n    });\n    // In-chart legend (top-right corner, where the distributions are ~0). Hovering an entry or a curve highlights that curve.\n    const highlight = group => {\n      svg.classList.toggle("has-hot", group != null);\n      svg.querySelectorAll("g.series, g.legend-entry").forEach(node => node.classList.toggle("hot", node.dataset.group === group));\n    };\n    const shown = allGroups.filter(group => selected.has(String(group)) && data.some(point => point.group === group));\n    const lx = box.l + box.w - 66, ly = box.t + 16, lh = 16;\n    const title = add(svg, "text", { x: lx, y: ly, class: "legend-title", "font-size": 12, "font-weight": 600, fill: "#40515a" }, isPuct ? "c" : "Threads");\n    if (isPuct) add(title, "tspan", { dy: 3, "font-size": 9 }, "puct");\n    shown.forEach((group, i) => {\n      const y0 = ly + lh * (i + 1);\n      const entry = add(svg, "g", { class: "legend-entry", "data-group": String(group) });\n      add(entry, "rect", { x: lx - 6, y: y0 - 12, width: 74, height: lh, fill: "transparent" });\n      add(entry, "line", { x1: lx, x2: lx + 18, y1: y0 - 4, y2: y0 - 4, stroke: colors[allGroups.indexOf(group)], "stroke-width": 3, "stroke-linecap": "round" });\n      add(entry, "text", { x: lx + 25, y: y0, "font-size": 12, fill: "#40515a" }, String(group));\n      const pts = data.filter(point => point.group === group), mass = pts.reduce((t, q) => t + q.value, 0);\n      const mean = mass ? pts.reduce((t, q) => t + q.depth * q.value, 0) / mass : 0, samples = pts.length ? Math.max(...pts.map(q => q.samples)) : 0;\n      const gElo = isPuct ? DATA.figure3.puctElo[String(group)] : (sim === 400 ? DATA.figure3.threadElo[String(group)] : null);\n      addTooltip(entry, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong><br>Mean depth ${fmt(mean, 2)}${gElo == null ? "" : `<br>Elo ${fmt(gElo, 1)}`}<br><span class="soft">Samples ${samples.toLocaleString()} moves</span>`);\n      entry.addEventListener("mouseenter", () => highlight(String(group)));\n      entry.addEventListener("mouseleave", () => highlight(null));\n    });\n    series.forEach((g, group) => { g.addEventListener("mouseenter", () => highlight(group)); g.addEventListener("mouseleave", () => highlight(null)); });\n    return svg;\n  }'),
    # Tree shape: two panel cards, (a) exploration coefficient and (b) thread count × simulation counts, each carrying its own chip row.
    ('function renderFigure3() {\n    const chart = el("chartArea"); chart.innerHTML = "";',
     'function renderFigure3() {\n    const chart = el("chartArea");\n    // The chip groups live inside the two panels; take fresh ones from #controls after renderControls(), else re-use the ones already in the panels.\n    const fresh = el("controls").querySelectorAll(".control-group");\n    const groups = fresh.length ? [...fresh] : [...chart.querySelectorAll(".control-group")];\n    chart.innerHTML = "";'),
    ('    for (const [kind, label] of [["puct", "(a) Varying exploration coefficient"], ["threads", "(b) Varying thread count"]]) {\n      const panel = document.createElement("div"); panel.className = "dual-panel";\n      panel.innerHTML = `<h4><span class="panel-tag">${label.slice(0, 3)}</span>${label.slice(4)}</h4>`;\n      panel.appendChild(distributionPanel(kind));\n      wrapper.appendChild(panel);\n    }',
     '    const card = (tag, title, group) => { const s = document.createElement("section"); s.className = "shape-panel"; s.innerHTML = `<h4><span class="panel-tag">${tag}</span>${title}</h4>`; if (group) s.appendChild(group); return s; };\n    const a = card("(a)", "Varying the exploration coefficient · 400 simulations", groups[0]);\n    const aChart = document.createElement("div"); aChart.className = "shape-chart shape-single"; aChart.appendChild(distributionPanel("puct", 400)); a.appendChild(aChart);\n    const b = card("(b)", "Varying the thread count", groups[1]);\n    const grid = document.createElement("div"); grid.className = "shape-chart shape-grid";\n    FIGURE3_SIMS.forEach((sim, i) => { const cell = document.createElement("div"); cell.className = "shape-cell"; cell.appendChild(distributionPanel("threads", sim)); const cap = document.createElement("p"); cap.className = "shape-caption"; cap.innerHTML = `<span class="panel-tag">(b-${i + 1})</span>${sim} simulations`; cell.appendChild(cap); grid.appendChild(cell); });\n    b.appendChild(grid);\n    chart.append(a, b);'),
    ('    chart.appendChild(wrapper);\n    el("chartLegend").innerHTML = `<span class="legend-item">Left: ${state.figure3Puct.size} pUCT curves</span><span class="legend-item">Right: ${state.figure3Threads.size} thread curves</span><span class="legend-item">Hover over curves for depth and sample counts</span>`;',
     '    el("chartLegend").innerHTML = "";'),
    # Chips now live inside the chart area, so delegate their events from the document.
    ('  controls.addEventListener("change", event => {', '  document.addEventListener("change", event => {'),
    ('  controls.addEventListener("click", event => {', '  document.addEventListener("click", event => {'),
    ("      DATA.figure3.threads.filter(point => state.figure3Threads.has(String(point.group))).forEach(point => rows.push([3, \"threads\", point.group, point.depth, point.value, point.samples]));",
     "      FIGURE3_SIMS.forEach(sim => threadsAt(sim).filter(point => state.figure3Threads.has(String(point.group))).forEach(point => rows.push([3, `threads_n${sim}`, point.group, point.depth, point.value, point.samples])));"),
]


# shared-nav.js: two tabs (Search trees, Tree shape), numbered 01/02 on the page.
NAV_PATCHES = [
    ("const figures=[{id:1,path:'figure1/index.html',title:'Search trees',sub:'PUCT · simulation · threads'},{id:2,path:'index.html#2',title:'Depth scaling',sub:'Depth across games'},{id:3,path:'index.html#3',title:'Tree shape',sub:'Depth distribution · parallelism'},{id:4,path:'index.html#4',title:'Performance scaling',sub:'Go · Atari · LLM'}];",
     "const figures=[{id:1,num:'01',path:'figure1/index.html',title:'Search trees',sub:'PUCT · simulation · threads'},{id:3,num:'02',path:'index.html',title:'Tree shape',sub:'Depth distribution · parallelism'},{id:5,num:'03',path:'lab.html',title:'Scaling lab',sub:'Asymptotic depth rates'}];"),
    ("<span class=\"research-nav-number\">0${f.id}</span>", "<span class=\"research-nav-number\">${f.num}</span>"),
    ("nav.setAttribute('aria-label','Figures 1 through 4');", "nav.setAttribute('aria-label','Interactive figures');"),
    ("let figure=location.pathname.includes('/figure1/')?1:location.pathname.endsWith('figure4_puct.html')?4:([2,3,4].includes(Number(location.hash.slice(1)))?Number(location.hash.slice(1)):2);",
     "let figure=location.pathname.includes('/figure1/')?1:location.pathname.endsWith('/lab.html')?5:3;"),
]
FILE_PATCHES = {'app.js': APP_PATCHES, 'shared-nav.js': NAV_PATCHES}
# Explorer files that only served Figures 2 and 4.
DROPPED_FILES = {'figure4_updates.js', 'figure4_puct.html', 'figure4_puct.css', 'figure4_puct.js', 'figure4_puct_data.js',
                 'figure4_puct_inventory.csv', 'atari_additional_curves.csv', 'atari_legacy2_by_game.csv'}
DROPPED_ASSETS = {'figure1_paper.png', 'figure2_paper.png', 'figure3_paper.png', 'figure4_paper.png'}


def patch_app(text: str, patches=None, name: str = 'app.js') -> str:
    for old, new in (APP_PATCHES if patches is None else patches):
        if text.count(old) != 1:
            sys.exit(f'{name} patch expected exactly one match, found {text.count(old)}: {old[:70]!r}')
        text = text.replace(old, new)
    return text


def figure3_threads_by_sim(src: Path) -> dict:
    """Depth distributions by thread count for 50-1600 simulations (archived Go runs, 50 games each).
    400 simulations keeps the paper's own data, so it is left out here."""
    import csv
    out = {}
    with (src / 'exports' / 'figure3b' / 'figure3b_depth_points.csv').open(encoding='utf-8') as fh:
        for r in csv.DictReader(fh):
            n = int(r['simulation'])
            if n == 400:
                continue
            out.setdefault(n, []).append({'group': int(r['threads']), 'depth': int(r['depth']),
                                          'value': float(r['mean_pdf']), 'samples': int(r['samples'])})
    return out


def fix_wording(text: str) -> str:
    """Apply wording fixes and strip local filesystem paths (experiment provenance strings)."""
    for old, new in WORDING:
        text = text.replace(old, new)
    text, n = PATH_RE.subn('archived run', text)
    _path_hits[0] += n
    return text


def log(msg):
    print(msg, flush=True)


def reset_dir(path: Path):
    if path.exists():
        shutil.rmtree(path)
    path.mkdir(parents=True)


KATEX_TAGS = ('<link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.css">'
              '<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/katex.min.js"></script>'
              '<script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.11/dist/contrib/auto-render.min.js"></script>')
FONTS_LINK = ('<link rel="preconnect" href="https://fonts.googleapis.com"><link rel="preconnect" href="https://fonts.gstatic.com" crossorigin>'
              '<link rel="stylesheet" href="https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600&amp;family=Source+Serif+4:ital,opsz,wght@0,8..60,400;0,8..60,500;1,8..60,400&amp;display=swap">')


def inject_site_bar(html: str, depth: int, body_class: str = '') -> str:
    """Add the shared top bar, fonts and theme layer to a sub-site page. depth = directory depth below root."""
    rel = '../' * depth
    tags = (FONTS_LINK + f'<link rel="stylesheet" href="{rel}site-bar.css"><link rel="stylesheet" href="{rel}theme.css">'
            f'<script defer src="{rel}site-bar.js?v=2" data-root="{rel}"></script>')
    if 'site-bar.js' in html:
        return html
    html = html.replace('</head>', tags + '</head>', 1)
    if body_class:
        def add_class(m):
            attrs = m.group(1) or ''
            if 'class="' in attrs:
                return '<body' + attrs.replace('class="', f'class="{body_class} ', 1) + '>'
            return f'<body class="{body_class}"{attrs}>'
        html = re.sub(r'<body(\s[^>]*)?>', add_class, html, count=1)
    return html


LOADER_OLD = "script.src=chunk.file;"
LOADER_NEW = "script.src=(record.stepBase&&chunk.start>=(record.localSteps||0)?record.stepBase:'')+chunk.file;"


def assign_shards(records, sizes, n):
    """Greedy bin packing: largest setting first into the least-loaded mirror. Returns record index -> shard."""
    order = sorted(range(len(records)), key=lambda i: -sizes[i])
    loads = [0] * n
    where = {}
    for i in order:
        k = min(range(n), key=lambda j: loads[j])
        loads[k] += sizes[i]
        where[i] = k
    return where, loads


def build_figures(src: Path, dest: Path, max_steps: int, shards: int = 0, data_base: str = '', data_out: str = '', write_mirrors: bool = True):
    log(f'[figures] {src} -> {dest}')
    reset_dir(dest)
    # Explorer root: runtime files + small provenance CSVs. Builders (.py), exports and caches stay out.
    for p in sorted(src.iterdir()):
        if p.is_file() and p.suffix in {'.html', '.css', '.js', '.csv'} and p.name not in DROPPED_FILES:
            text = None
            if p.suffix == '.html':
                text = p.read_text(encoding='utf-8')
                text = text.replace('Local / standalone · Figures 1–4', SITE_BAR_META)
                text = text.replace('  <script defer src="figure4_updates.js"></script>\n', '')
                # Hidden "Reading the chart" / "Source & method" / paper-reference blocks: drop them from the markup entirely.
                text, n1 = re.subn(r'\s*<div class="bottom-grid">.*?</section>\s*<section class="source-card">.*?</section>\s*</div>', '', text, count=1, flags=re.S)
                text, n2 = re.subn(r'\s*<details class="reference-card">.*?</details>', '', text, count=1, flags=re.S)
                if (n1, n2) != (1, 1):
                    sys.exit(f'figures/index.html: expected the bottom-grid and reference-card blocks (found {n1}, {n2})')
                text = inject_site_bar(text, depth=1, body_class='site-figures')
                text = text.replace('</head>', KATEX_TAGS + '<script defer src="figures-addon.js"></script></head>', 1)
                text = fix_wording(text)
            elif p.suffix == '.js':
                text = fix_wording(p.read_text(encoding='utf-8'))
                if p.name in FILE_PATCHES:
                    text = patch_app(text, FILE_PATCHES[p.name], p.name)
                elif p.name == 'data.js':
                    text += '\nwindow.FIGURE_DATA.figure3.threadsBySim = ' + json.dumps(figure3_threads_by_sim(src), separators=(',', ':')) + ';\n'
            elif p.suffix == '.csv':
                text = fix_wording(p.read_text(encoding='utf-8'))
            if text is None:
                shutil.copy2(p, dest / p.name)
            else:
                (dest / p.name).write_text(text, encoding='utf-8')
    shutil.copytree(src / 'assets', dest / 'assets', ignore=lambda _d, names: [n for n in names if n in DROPPED_ASSETS])
    if not any((dest / 'assets').iterdir()):
        (dest / 'assets').rmdir()
    shutil.copy2(ROOT / 'tools' / 'figures_addon.js', dest / 'figures-addon.js')
    # Scaling lab (moved here from the proof walkthrough's #lab page).
    lab = (ROOT / 'tools' / 'lab.html').read_text(encoding='utf-8')
    lab = inject_site_bar(lab, depth=1, body_class='site-figures')
    lab = lab.replace('</head>', KATEX_TAGS + '<script defer src="figures-addon.js"></script></head>', 1)
    (dest / 'lab.html').write_text(fix_wording(lab), encoding='utf-8')
    shutil.copy2(ROOT / 'tools' / 'lab.js', dest / 'lab.js')
    shutil.copy2(ROOT / 'tools' / 'lab.css', dest / 'lab.css')

    # Figure 1: runtime files only.
    f1_src, f1_dest = src / 'figure1', dest / 'figure1'
    f1_dest.mkdir()
    for name in ['engine.js', 'style.css']:
        shutil.copy2(f1_src / name, f1_dest / name)
    app = (f1_src / 'app.js').read_text(encoding='utf-8')
    if app.count(LOADER_OLD) != 1:
        sys.exit(f'figure1/app.js: expected exactly one occurrence of {LOADER_OLD!r}; loader changed upstream')
    (f1_dest / 'app.js').write_text(fix_wording(app.replace(LOADER_OLD, LOADER_NEW)), encoding='utf-8')

    raw = (f1_src / 'snapshots.js').read_text(encoding='utf-8')
    prefix, body = raw.split('=', 1)
    data = json.loads(body.rstrip().rstrip(';'))
    full_steps = sum(r.get('stepCount', 1) for r in data['records'])
    records = data['records']
    shard_of, shard_files = {}, {}
    if shards:
        sizes = [sum((f1_src / c['file']).stat().st_size for c in r.get('stepChunks', [])) for r in records]
        shard_of, loads = assign_shards(records, sizes, shards)
        log('[figures] mirror sizes: ' + ', '.join(f'{k + 1}: {b / 1e6:.0f} MB' for k, b in enumerate(loads)))
    kept_files, kept_steps = [], 0
    for i, rec in enumerate(records):
        count = rec.get('stepCount', 1)
        chunks = rec.get('stepChunks', [])
        local_count = min(count, max_steps)
        new_chunks = []
        for c in chunks:
            if c['start'] < local_count:
                kept_files.append(c['file'])
                new_chunks.append({**c, 'end': min(c['end'], local_count - 1)} if not shards else c)
            elif shards:
                new_chunks.append(c)
            if shards:
                shard_files.setdefault(shard_of[i], []).append(c['file'])
        if shards and chunks:
            rec['stepBase'] = data_base.format(k=shard_of[i] + 1)
            rec['localSteps'] = local_count
            kept_steps += count
        else:
            rec['stepCount'] = local_count
            kept_steps += local_count
        if chunks or 'stepChunks' in rec:
            rec['stepChunks'] = new_chunks
    data['publicSubset'] = {
        'maxStepsPerSetting': max_steps,
        'localTrees': sum(min(r.get('stepCount', 1), max_steps) for r in records),
        'archivedTrees': full_steps,
        'mirrors': [data_base.format(k=k + 1) for k in range(shards)],
        'note': ('First steps of each setting are served from this site; later steps load on demand from the data mirrors.'
                 if shards else 'Public build ships the first steps of each recorded setting; the full archive is held by the authors.'),
    }
    data['totalSteps'] = kept_steps
    (f1_dest / 'snapshots.js').write_text(fix_wording(prefix + '=' + json.dumps(data, separators=(',', ':')) + ';'), encoding='utf-8')

    total_gb = sum((f1_src / c['file']).stat().st_size for r in records for c in r.get('stepChunks', [])) / 1e9
    steps_dest = f1_dest / 'steps'
    steps_dest.mkdir()
    total_bytes = 0
    for i, rel in enumerate(kept_files):
        s = f1_src / rel
        if not s.exists():
            log(f'  warning: missing chunk {rel}')
            continue
        shutil.copy2(s, steps_dest / s.name)
        total_bytes += s.stat().st_size
        if i % 1000 == 0 and i:
            log(f'  copied {i}/{len(kept_files)} chunks')

    html = (f1_src / 'index.html').read_text(encoding='utf-8')
    html = html.replace('Local / standalone · Figures 1–4', SITE_BAR_META)
    local_trees = data['publicSubset']['localTrees']
    if shards:
        note = (f'<p><strong>Public build.</strong> The first {max_steps} recorded steps of each of the {len(records)} '
                f'archived settings ({local_trees:,} trees) are served from this site. The remaining steps '
                f'({full_steps - local_trees:,} trees, {total_gb:.1f} GB in total) load on demand from {shards} '
                f'static data mirrors when you move the step slider; nothing is fetched until you ask for it.</p>')
    else:
        note = (f'<p><strong>Public build.</strong> This site ships the first {max_steps} recorded steps of each '
                f'of the {len(records)} archived settings ({kept_steps:,} of {full_steps:,} trees; '
                f'step 0 is always included). The complete 3.7 GB archive is available from the authors.</p>')
    html = html.replace('<p id="provenance"></p>', '<p id="provenance"></p>' + note, 1)
    # Hidden "Reading the figure" block: keep only the two buttons app.js binds to (never shown), drop the stale copy and the paper-image link.
    html, n = re.subn(r'<section class="reference">.*?</section>',
                      '<section class="reference" hidden><div class="play-row"><button id="play">Animate model search</button><button id="saveJson">Export tree JSON</button></div></section>',
                      html, count=1, flags=re.S)
    if n != 1:
        sys.exit('figure1/index.html: reference block not found')
    html = inject_site_bar(html, depth=2, body_class='site-figures')
    shutil.copy2(ROOT / 'tools' / 'figure1_addon.js', f1_dest / 'addon.js')
    html = html.replace('</head>', KATEX_TAGS + '<script defer src="addon.js?v=3"></script></head>', 1)
    (f1_dest / 'index.html').write_text(fix_wording(html), encoding='utf-8')
    log(f'[figures] stripped {_path_hits[0]} local file paths from copied text files')
    log(f'[figures] figure1: {len(records)} settings, {local_trees:,} local trees of {full_steps:,}, '
        f'{len(kept_files)} local chunk files, {total_bytes / 1e6:.1f} MB')

    if shards and not write_mirrors:
        log('[figures] --skip-mirror-copy: mirror folders not regenerated; only the site index references them')
    if shards and write_mirrors:
        manifest = []
        for k in range(shards):
            out = Path(data_out.format(k=k + 1))
            if not out.is_absolute():
                out = ROOT.parent / out
            reset_dir(out)
            (out / '.nojekyll').write_text('')
            steps = out / 'steps'
            steps.mkdir()
            size = 0
            files = shard_files.get(k, [])
            for j, rel in enumerate(files):
                sp = f1_src / rel
                shutil.copy2(sp, steps / sp.name)
                size += sp.stat().st_size
                if j and j % 5000 == 0:
                    log(f'  mirror {k + 1}: {j}/{len(files)} chunks')
            settings = sorted(records[i]['game'] + f"_n{records[i]['sim']}_t{records[i]['threads']}_c{records[i]['puct']}"
                              for i, sk in shard_of.items() if sk == k)
            (out / 'manifest.json').write_text(json.dumps({
                'mirror': k + 1, 'of': shards, 'baseUrl': data_base.format(k=k + 1), 'files': len(files),
                'bytes': size, 'settings': settings}, indent=1) + '\n')
            (out / 'README.md').write_text(
                f'# Search-Tree Scaling · Figure 1 data mirror {k + 1} of {shards}\n\n'
                f'Static hosting for recorded MCTS search trees used by the interactive Figure 1 page of '
                f'"Search-Tree Scaling in Parallel Monte Carlo Tree Search" (NeurIPS 2026). '
                f'Each file in `steps/` holds 32 consecutive recorded search steps of one experiment setting '
                f'(gzip + base64, loaded on demand by the figure page). {len(files)} files, {size / 1e6:.0f} MB. '
                f'Generated by `tools/build_site.py`; see `manifest.json` for the settings served here.\n')
            (out / 'index.html').write_text(
                f'<!doctype html><meta charset="utf-8"><title>Figure 1 data mirror {k + 1}/{shards}</title>'
                f'<p>Data mirror {k + 1} of {shards} for the Search-Tree Scaling Figure 1 explorer. '
                f'{len(files)} step files, {size / 1e6:.0f} MB. See <code>manifest.json</code>.</p>\n')
            manifest.append({'mirror': k + 1, 'baseUrl': data_base.format(k=k + 1), 'files': len(files), 'bytes': size})
            log(f'[figures] mirror {k + 1}: {out} ({len(files)} files, {size / 1e6:.0f} MB)')
        (f1_dest / 'data-mirrors.json').write_text(json.dumps(manifest, indent=1) + '\n')


def build_proof(src: Path, dest: Path):
    log(f'[proof] {src} -> {dest}')
    reset_dir(dest)
    shutil.copytree(src, dest, dirs_exist_ok=True)
    index = dest / 'index.html'
    html = index.read_text(encoding='utf-8')
    html = inject_site_bar(html, depth=1, body_class='with-site-bar-fixed site-proof')
    # The scaling lab lives on the figures site now.
    html, n = re.subn(r'<a href="#lab" data-page="lab">.*?</a>', '', html, count=1, flags=re.S)
    if n != 1:
        sys.exit('proof index: scaling-lab nav link not found')
    index.write_text(html, encoding='utf-8')
    app = dest / 'app.js'
    js = app.read_text(encoding='utf-8')
    old = "else if(page==='lab')lab();"
    if js.count(old) != 1:
        sys.exit('proof app.js: lab route not found')
    app.write_text(js.replace(old, "else if(page==='lab'){location.replace('../figures/lab.html');return;}"), encoding='utf-8')
    tex = ROOT / 'camera_ready' / 'main.tex'
    if tex.exists():
        import subprocess
        subprocess.run([sys.executable, str(ROOT / 'tools' / 'sync_paper_statements.py'), '--tex', str(tex),
                        '--walkthrough', str(src.parent), '--bundle', str(dest / 'paper-statements.js')], check=True)
    else:
        log('[proof] camera_ready/main.tex not found; paper statements left as bundled')


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--figures-src', type=Path, required=True, help='figure explorer source folder')
    ap.add_argument('--proof-src', type=Path, required=True, help='proof walkthrough dist folder (its parent holds sync-paper.py)')
    ap.add_argument('--max-steps', type=int, default=128, help='recorded steps kept per Figure 1 setting (multiples of 32 avoid partial chunks)')
    ap.add_argument('--only', choices=['figures', 'proof'], action='append', help='build only these parts')
    ap.add_argument('--data-shards', type=int, default=0, help='split the full Figure 1 archive into N data-mirror folders (0 = ship only --max-steps)')
    ap.add_argument('--data-base', default='https://chengscott.io/search-tree-scaling-data-{k}/',
                    help='base URL template of mirror {k} (1-based); each mirror serves steps/ under it')
    ap.add_argument('--data-out', default='search-tree-scaling-data-{k}',
                    help='output folder template for mirror {k}; relative paths are placed next to this repository')
    ap.add_argument('--skip-mirror-copy', action='store_true', help='with --data-shards: rewrite the site index for the mirrors but do not regenerate the mirror folders')
    args = ap.parse_args()

    parts = set(args.only or ['figures', 'proof'])
    if 'figures' in parts:
        if not args.figures_src.exists():
            sys.exit(f'figures source not found: {args.figures_src}')
        build_figures(args.figures_src, ROOT / 'figures', args.max_steps, args.data_shards, args.data_base, args.data_out, not args.skip_mirror_copy)
    if 'proof' in parts:
        if not args.proof_src.exists():
            sys.exit(f'proof source not found: {args.proof_src}')
        build_proof(args.proof_src, ROOT / 'proof')
    log('done')


if __name__ == '__main__':
    main()
