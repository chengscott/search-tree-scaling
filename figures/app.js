(function () {
  "use strict";

  const DATA = window.FIGURE_DATA;
  const UPDATES = window.FIGURE4_UPDATES;
  if (!DATA) {
    document.body.innerHTML = "<p style='padding:2rem'>The data.js file could not be loaded.</p>";
    return;
  }

  const SVG_NS = "http://www.w3.org/2000/svg";
  const SIMS = DATA.figure2.sims;
  const PAPER_COLORS = { kata: "#2ca02c", llm: "#ff7f0e", atari: "#1f77b4" };
  const GAME_COLORS = ["#7457b9", "#c65d80", "#0f9992", "#a67626", "#526cbd", "#7d9a32", "#c15c4d", "#4e8898"];
  const PUCT_COLORS = ["#1c9e66", "#55b866", "#8fc965", "#d9d65f", "#f5bd57", "#f18b49", "#e35e42", "#bb3435"];
  const THREAD_COLORS = ["#168f48", "#4dad5a", "#74c86b", "#b7d66d", "#ead85f", "#f8aa52", "#ef7648", "#e64b3d", "#b72834"];

  const state = {
    figure: 3,
    figure2Games: new Set(),
    figure2Search: "",
    figure2Boxes: true,
    figure2Fit: "paper",
    figure3Puct: new Set(["0", "0.25", "0.5", "1", "1.5", "2.5", "5", "10"]),
    figure3Threads: new Set(["1", "2", "4", "8", "16", "32", "64", "128"]),
    figure4Domains: new Set(["kata", "llm", "atari"]),
    figure4Source: "dt",
    figure4Dataset: UPDATES ? "updated" : "paper",
    figure4Games: new Set(),
    figure4Search: "",
  };

  const el = id => document.getElementById(id);
  const controls = el("controls");
  const tooltip = el("tooltip");
  const fmt = (value, digits = 2) => Number(value).toFixed(digits);
  const pretty = name => name.replaceAll("_", " ").replace(/\b\w/g, char => char.toUpperCase())
    .replace("Qbert", "Q*bert").replace("Ms Pacman", "Ms Pac-Man");
  const safe = value => String(value).replace(/[&<>"']/g, char => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[char]);

  function svgEl(tag, attrs = {}, text = null) {
    const node = document.createElementNS(SVG_NS, tag);
    for (const [key, value] of Object.entries(attrs)) node.setAttribute(key, String(value));
    if (text !== null) node.textContent = text;
    return node;
  }
  function add(parent, tag, attrs = {}, text = null) {
    const node = svgEl(tag, attrs, text);
    parent.appendChild(node);
    return node;
  }
  function makeSvg(width, height, label) {
    return svgEl("svg", { viewBox: `0 0 ${width} ${height}`, role: "img", "aria-label": label, xmlns: SVG_NS });
  }
  function addTooltip(node, html) {
    node.setAttribute("tabindex", "0");
    node.addEventListener("mouseenter", event => showTooltip(event, html));
    node.addEventListener("mousemove", event => showTooltip(event, html));
    node.addEventListener("mouseleave", hideTooltip);
    node.addEventListener("blur", hideTooltip);
    node.addEventListener("focus", () => showTooltip({ clientX: innerWidth / 2, clientY: innerHeight / 2 }, html));
  }
  function showTooltip(event, html) {
    tooltip.innerHTML = html;
    tooltip.classList.add("show");
    const x = Math.min(event.clientX + 14, innerWidth - 265);
    const y = Math.min(event.clientY + 14, innerHeight - 125);
    tooltip.style.left = `${Math.max(8, x)}px`;
    tooltip.style.top = `${Math.max(8, y)}px`;
  }
  function hideTooltip() { tooltip.classList.remove("show"); }

  function quantile(values, p) {
    if (!values.length) return NaN;
    const sorted = [...values].sort((a, b) => a - b);
    const index = (sorted.length - 1) * p;
    const low = Math.floor(index);
    const high = Math.ceil(index);
    return sorted[low] + (sorted[high] - sorted[low]) * (index - low);
  }
  function axis(svg, box, xTicks, yTicks, xMap, yMap, xLabel, yLabel, xFormat = String, yFormat = String, paperOptions = {}) {
    if(paperOptions.frame)svg.setAttribute("font-family","Times New Roman, Times, serif");
    add(svg, "rect", { x: box.l, y: box.t, width: box.w, height: box.h, class: "plot-bg", fill: paperOptions.frame?"white":"#fcfdfc" });
    for (const value of yTicks) {
      const y = yMap(value);
      add(svg, "line", { x1: box.l, y1: y, x2: box.l + box.w, y2: y, class: "chart-grid", stroke: paperOptions.gridColor || (paperOptions.frame?"#e6e6e6":"#e6eeeb"),"stroke-width":paperOptions.frame?1.5:1 });
      add(svg, "text", { x: box.l - 11, y: y + 4, "text-anchor": "end", class: "tick-label", fill: paperOptions.frame?"black":"#71818a", "font-size": paperOptions.frame?20:11 }, yFormat(value));
    }
    for (const value of xTicks) {
      const x = xMap(value);
      if (paperOptions.gridX !== false) add(svg, "line", { x1: x, y1: box.t, x2: x, y2: box.t + box.h, stroke: paperOptions.gridColor || "#f0f3f1", "stroke-width": paperOptions.gridColor ? 1.3 : 1 });
      if(paperOptions.frame) add(svg,"line",{x1:x,y1:box.t+box.h,x2:x,y2:box.t+box.h+6,stroke:"#000","stroke-width":1.3});
      add(svg, "text", { x, y: box.t + box.h + 21, "text-anchor": "middle", class: "tick-label", fill: paperOptions.frame?"black":"#71818a", "font-size": paperOptions.frame?20:11 }, xFormat(value));
    }
    add(svg, "line", { x1: box.l, y1: box.t + box.h, x2: box.l + box.w, y2: box.t + box.h, class: "axis-line", stroke: "#9fb0ad" });
    add(svg, "line", { x1: box.l, y1: box.t, x2: box.l, y2: box.t + box.h, class: "axis-line", stroke: "#9fb0ad" });
    if(paperOptions.frame) add(svg,"rect",{x:box.l,y:box.t,width:box.w,height:box.h,fill:"none",stroke:"#000","stroke-width":1.7});
    add(svg, "text", { x: box.l + box.w / 2, y: box.t + box.h + 51, "text-anchor": "middle", class: "axis-label", fill: paperOptions.frame?"black":"#4c5b61", "font-size": paperOptions.frame?27:13 }, xLabel);
    add(svg, "text", { transform: `translate(19 ${box.t + box.h / 2}) rotate(-90)`, "text-anchor": "middle", class: "axis-label", fill: paperOptions.frame?"black":"#4c5b61", "font-size": paperOptions.frame?27:13 }, yLabel);
  }
  function pathFrom(points) { return points.map((point, index) => `${index ? "L" : "M"}${point[0].toFixed(2)},${point[1].toFixed(2)}`).join(" "); }

  const FIGURE_META = {
    2: {
      kicker: "FIGURE 02 / EMPIRICAL DEPTH",
      title: "Depth scaling",
      description: "Theorem 2: with an exploration schedule \\(c(m)\\), the depth of the optimal path grows as \\(H_{\\mathrm{opt}}(n)=\\Theta\\big(\\int_1^n \\frac{dm}{c(m)\\sqrt m}\\big)\\). MuZero's exploration schedule (right) grows like \\(\\log m\\), giving \\(H_{\\mathrm{opt}}(n)=\\Theta(\\sqrt n/\\log n)\\). The red curve fits \\(a\\sqrt n/\\log n\\) to the empirical depth over 44 Atari games (\\(a\\approx 3.004\\), RMSE 4.10).",
      chart: "Optimal-path depth vs. simulation count",
      stat: ["44", "Atari games"],
      reference: "assets/figure2_paper.png",
    },
    3: {
      kicker: "FIGURE 03 / TREE DISTRIBUTION",
      title: "Tree shape",
      description: "Depth distributions of Go search trees. Panel (a) varies the exploration coefficient \\(c\\) at 400 simulations; panel (b) varies the thread count \\(T\\) at 50 to 1600 simulations. A larger \\(c\\) or more threads shifts visits toward shallower nodes, the contention regime of Theorem 4 where depth grows only as \\(\\Theta(n/T)\\). Use the chips to pick settings and hover a legend entry to highlight one curve.",
      chart: "Depth distribution under search settings",
      stat: ["400", "simulations / search"],
      reference: "assets/figure3_paper.png",
    },
    4: {
      kicker: "FIGURE 04 / PERFORMANCE SCALING",
      title: "Performance scaling",
      description: "Reproduce the six paper curves for Go, Blocksworld and Atari Amidar. Add other Atari games to compare scaling trends.",
      chart: "Relative performance vs. simulation count",
      stat: ["3", "domains"],
      reference: "assets/figure4_paper.png",
    },
  };

  function setFigure(figure) {
    state.figure = figure;
    document.title=`${FIGURE_META[figure].title} · Search-Tree Scaling`;
    document.querySelectorAll(".figure-tab").forEach(button => {
      const active = Number(button.dataset.figure) === figure;
      button.classList.toggle("active", active);
      button.setAttribute("aria-current", active ? "page" : "false");
    });
    window.dispatchEvent(new Event("figurechange"));
    const meta = FIGURE_META[figure];
    el("figureKicker").textContent = meta.kicker;
    el("figureTitle").textContent = meta.title;
    el("figureDescription").textContent = meta.description;
    el("introStat").innerHTML = `<strong>${meta.stat[0]}</strong><span>${meta.stat[1]}</span>`;
    el("chartTitle").textContent = meta.chart;
    renderControls();
    renderChart();
    renderNotes();
  }

  function renderControls() {
    if (state.figure === 2) {
      controls.innerHTML = `
        <section class="control-group"><p class="control-title">Model fit</p>
          <select id="fitMode" class="select-input"><option value="paper" ${state.figure2Fit === "paper" ? "selected" : ""}>Paper coefficient a = 3.004</option><option value="current" ${state.figure2Fit === "current" ? "selected" : ""}>Refit from the archived CSV data</option></select>
          <label class="check-row"><input id="showBoxes" type="checkbox" ${state.figure2Boxes ? "checked" : ""}>Show box plots for all 44 games</label>
        </section>
        <section class="control-group"><p class="control-title">Select games <span class="selected-count" id="gameCount"></span></p>
          <input class="search-input" id="gameSearch" type="search" placeholder="Search Atari games…" value="${safe(state.figure2Search)}" aria-label="Search games">
          <div class="check-list" id="gameList"></div>
          <div class="inline-actions"><button type="button" data-action="f2-preset">Example selection</button><button type="button" data-action="f2-clear">Clear selection</button></div>
          <p class="control-description" id="selectionMessage">Compare up to 8 games at once.</p>
        </section>`;
      renderGameList();
    } else if (state.figure === 3) {
      const puctValues = [0, .25, .5, 1, 1.5, 2.5, 5, 10];
      const threadValues = [1, 2, 4, 8, 16, 32, 64, 128], threadColorIndex = value => [1, 2, 4, 6, 8, 16, 32, 64, 128].indexOf(value);
      controls.innerHTML = `
        <section class="control-group"><p class="control-title">Exploration coefficient c<sub>puct</sub></p><div class="chip-row">
          ${puctValues.map((value, index) => `<label class="choice-chip ${state.figure3Puct.has(String(value)) ? "selected" : ""}" style="--chip-color:${PUCT_COLORS[index]}"><input type="checkbox" data-puct="${value}" ${state.figure3Puct.has(String(value)) ? "checked" : ""}><span class="chip-dot" style="background:${PUCT_COLORS[index]}"></span>${value}</label>`).join("")}
          </div><div class="inline-actions"><button type="button" data-action="puct-all">Select all</button><button type="button" data-action="puct-clear">Clear</button></div></section>
        <section class="control-group"><p class="control-title">Search threads</p><div class="chip-row">
          ${threadValues.map((value, index) => `<label class="choice-chip ${state.figure3Threads.has(String(value)) ? "selected" : ""}"><input type="checkbox" data-thread="${value}" ${state.figure3Threads.has(String(value)) ? "checked" : ""}><span class="chip-dot" style="background:${THREAD_COLORS[threadColorIndex(value)]}"></span>${value}</label>`).join("")}
          </div><div class="inline-actions"><button type="button" data-action="thread-paper">Select all</button><button type="button" data-action="thread-clear">Clear</button></div></section>`;
    } else {
      const counts={kata:0,atari:0,llm:0};
      if(state.figure4Dataset!=="paper") (UPDATES[state.figure4Dataset]||[]).forEach(s=>counts[s.category]++);
      else Object.keys(counts).forEach(k=>counts[k]=2);
      controls.innerHTML = `
        <section class="control-group"><p class="control-title">Dataset</p>
          <select id="figure4Dataset" class="select-input">
           ${[["updated","Updated measured curves (18)"],["adjusted","Atari three-point average (18)"],["validation","Independent repeat validation (8)"],["paper","Original paper reference (6)"]].filter(([key])=>key==="paper"||UPDATES).map(([key,label])=>`<option value="${key}" ${state.figure4Dataset===key?"selected":""}>${label}</option>`).join("")}
          </select>
          <p class="control-description">Measured, presentation-adjusted and repeated experiments are kept separate.</p>
        </section>
        <section class="control-group"><p class="control-title">Domains</p>
          <label class="check-row"><input type="checkbox" data-domain="kata" ${state.figure4Domains.has("kata") ? "checked" : ""}><span style="color:${PAPER_COLORS.kata}">●</span> Go <small>${counts.kata} curves</small></label>
          <label class="check-row"><input type="checkbox" data-domain="llm" ${state.figure4Domains.has("llm") ? "checked" : ""}><span style="color:${PAPER_COLORS.llm}">●</span> Blocksworld LLM <small>${counts.llm} curves</small></label>
          <label class="check-row"><input type="checkbox" data-domain="atari" ${state.figure4Domains.has("atari") ? "checked" : ""}><span style="color:${PAPER_COLORS.atari}">●</span> Atari Amidar <small>${counts.atari} curves</small></label>
        </section>
        <section class="control-group"><p class="control-title">Add other Atari games <span class="selected-count" id="gameCount"></span></p>
          <select id="extraSource" class="select-input"><option value="dt" ${state.figure4Source === "dt" ? "selected" : ""}>MuZero DT(42 games)</option><option value="legacy" ${state.figure4Source === "legacy" ? "selected" : ""}>MuZero legacy(51 games)</option></select>
          <p class="control-description">Additional games use their own score ranges and the paper Amidar display ceiling. Compare trend shapes; heights do not compare raw scores.</p>
          <input class="search-input" id="gameSearch" type="search" placeholder="Search games…" value="${safe(state.figure4Search)}" aria-label="Search Atari games">
          <div class="check-list" id="gameList"></div>
          <div class="inline-actions"><button type="button" data-action="f4-preset">Example selection</button><button type="button" data-action="f4-clear">Clear selection</button></div>
          <p class="control-description" id="selectionMessage">Add up to 6 games.</p>
        </section>`;
      renderGameList();
    }
  }

  function renderGameList() {
    const target = el("gameList");
    if (!target) return;
    const figure2 = state.figure === 2;
    const games = figure2 ? DATA.figure2.games : Object.keys(DATA.figure4.extraGames[state.figure4Source]).sort();
    const selected = figure2 ? state.figure2Games : state.figure4Games;
    const query = (figure2 ? state.figure2Search : state.figure4Search).trim().toLowerCase();
    const filtered = games.filter(game => pretty(game).toLowerCase().includes(query) || game.includes(query));
    target.innerHTML = filtered.map(game => `<label class="check-row"><input type="checkbox" data-game="${safe(game)}" ${selected.has(game) ? "checked" : ""}>${safe(pretty(game))}</label>`).join("") || `<p class="control-description">No matching games.</p>`;
    el("gameCount").textContent = `${selected.size} selected`;
  }

  function renderChart() {
    hideTooltip();
    if (state.figure === 2) renderFigure2();
    else if (state.figure === 3) renderFigure3();
    else renderFigure4();
  }

  function renderFigure2() {
    const chart = el("chartArea"); chart.innerHTML = "";
    const svg = makeSvg(740, 520, "Figure 2: Atari depth boxplots and fitted curve");
    svg.setAttribute("class","paper-plot figure2-paper");
    const box = { l: 96, t: 23, w: 625, h: 398 };
    const selectedDepths = DATA.figure2.points.filter(point => state.figure2Games.has(point.game)).map(point => point.depth);
    const yMax = Math.max(28, Math.ceil((Math.max(0, ...selectedDepths) + 2) / 5) * 5);
    const x = sim => box.l + (SIMS.indexOf(sim) + .5) * box.w / SIMS.length;
    const y = depth => box.t + box.h - depth / yMax * box.h;
    const yTicks = Array.from({ length: Math.floor(yMax / 5) + 1 }, (_, index) => index * 5);
    axis(svg, box, SIMS, yTicks, x, y, "Simulation count", "Depth", String, String, {gridX:false,frame:true});
    const grouped = new Map(SIMS.map(sim => [sim, DATA.figure2.points.filter(point => point.sim === sim).map(point => point.depth)]));
    if (state.figure2Boxes) for (const sim of SIMS) {
      const values = grouped.get(sim); if (!values.length) continue;
      const q1 = quantile(values, .25), med = quantile(values, .5), q3 = quantile(values, .75), iqr = q3 - q1;
      const whiskerLow = Math.min(...values.filter(value => value >= q1 - 1.5 * iqr));
      const whiskerHigh = Math.max(...values.filter(value => value <= q3 + 1.5 * iqr));
      const center = x(sim), width = 38;
      add(svg, "line", { x1: center, y1: y(whiskerHigh), x2: center, y2: y(whiskerLow), stroke: "#1f77b4", "stroke-width": 2 });
      add(svg, "line", { x1: center - 9, y1: y(whiskerHigh), x2: center + 9, y2: y(whiskerHigh), stroke: "#1f77b4", "stroke-width": 2 });
      add(svg, "line", { x1: center - 9, y1: y(whiskerLow), x2: center + 9, y2: y(whiskerLow), stroke: "#1f77b4", "stroke-width": 2 });
      const rect = add(svg, "rect", { x: center - width / 2, y: y(q3), width, height: Math.max(1, y(q1) - y(q3)), fill: "#72bee0", "fill-opacity": .85, stroke: "#1f77b4", "stroke-width": 2 });
      add(svg, "line", { x1: center - width / 2, y1: y(med), x2: center + width / 2, y2: y(med), stroke: "#17618c", "stroke-width": 2 });
      addTooltip(rect, `<strong>${sim} simulations</strong><br><span class="soft">${values.length} games</span><br>Median depth ${fmt(med, 2)}<br>Q1—Q3 ${fmt(q1, 2)}—${fmt(q3, 2)}`);
    }
    const a = state.figure2Fit === "paper" ? DATA.figure2.paperFitCoefficient : DATA.figure2.currentDataFitCoefficient;
    const model = SIMS.map(sim => [x(sim), y(a * Math.sqrt(sim) / Math.log(sim))]);
    add(svg, "path", { d: pathFrom(model), fill: "none", stroke: "#d62728", "stroke-width": 3, "stroke-linejoin": "round" });
    for (const sim of SIMS) {
      const predicted = a * Math.sqrt(sim) / Math.log(sim);
      const dot = add(svg, "circle", { cx: x(sim), cy: y(predicted), r: 4.8, fill: "#d62728", stroke: "none" });
      addTooltip(dot, `<strong>Model curve</strong><br>${sim} simulations<br>Predicted depth ${fmt(predicted, 2)}<br>a = ${fmt(a, 3)}`);
    }
    add(svg,"line",{x1:box.l+27,y1:box.t+48,x2:box.l+58,y2:box.t+48,stroke:"#d62728","stroke-width":3});
    add(svg,"circle",{cx:box.l+42,cy:box.t+48,r:4.5,fill:"#d62728"});
    add(svg,"text",{x:box.l+82,y:box.t+56,"font-family":"Times New Roman, Times, serif","font-size":25,fill:"black"},"Estimated:");
    add(svg,"text",{x:box.l+265,y:box.t+42,"text-anchor":"middle","font-family":"Times New Roman, Times, serif","font-size":20,"font-style":"italic",fill:"black"},"a√n");
    add(svg,"line",{x1:box.l+240,x2:box.l+290,y1:box.t+48,y2:box.t+48,stroke:"black","stroke-width":1.2});
    add(svg,"text",{x:box.l+265,y:box.t+69,"text-anchor":"middle","font-family":"Times New Roman, Times, serif","font-size":20,fill:"black"},"log n");
    [...state.figure2Games].sort().forEach((game, index) => {
      const color = GAME_COLORS[index % GAME_COLORS.length];
      const points = DATA.figure2.points.filter(point => point.game === game).sort((a, b) => a.sim - b.sim);
      add(svg, "path", { d: pathFrom(points.map(point => [x(point.sim), y(point.depth)])), fill: "none", stroke: color, "stroke-width": 2.5, "stroke-dasharray": "6 4", "stroke-linecap": "round" });
      points.forEach(point => {
        const dot = add(svg, "circle", { cx: x(point.sim), cy: y(point.depth), r: 4.2, fill: color, stroke: "white", "stroke-width": 1.3 });
        addTooltip(dot, `<strong>${safe(pretty(game))}</strong><br>${point.sim} simulations<br>Observed depth ${fmt(point.depth, 2)}`);
      });
    });
    chart.appendChild(svg);
    el("chartLegend").innerHTML = [...state.figure2Games].sort().map((game,index)=>`<span class="legend-item"><i class="legend-line" style="background:${GAME_COLORS[index%GAME_COLORS.length]}"></i>${safe(pretty(game))}</span>`).join("");
  }

  const FIGURE3_SIMS = [50, 100, 200, 400, 800, 1600];
  const threadsAt = sim => sim === 400 ? DATA.figure3.threads : ((DATA.figure3.threadsBySim || {})[sim] || []);
  function distributionPanel(kind, sim = 400) {
    const isPuct = kind === "puct";
    const data = isPuct ? DATA.figure3.puct : threadsAt(sim);
    const selected = isPuct ? state.figure3Puct : state.figure3Threads;
    const allGroups = isPuct ? [0, .25, .5, 1, 1.5, 2.5, 5, 10] : [1, 2, 4, 6, 8, 16, 32, 64, 128];
    const colors = isPuct ? PUCT_COLORS : THREAD_COLORS;
    const width = 535, height = 410;
    const svg = makeSvg(width, height, isPuct ? "Go depth distribution by pUCT" : "Go depth distribution by threads");
    const box = { l: 58, t: 22, w: 425, h: 310 };
    const xmax = isPuct ? 80 : 25;
    const x = depth => box.l + depth / xmax * box.w;
    const y = value => box.t + box.h - value / .26 * box.h;
    axis(svg, box, isPuct ? [0, 20, 40, 60, 80] : [0, 5, 10, 15, 20, 25], [0, .05, .1, .15, .2, .25], x, y, "Depth", "Distribution", String, value => `${Math.round(value * 100)}%`);
    const series = new Map();
    allGroups.forEach((group, index) => {
      if (!selected.has(String(group)) || !data.some(point => point.group === group)) return;
      const values = data.filter(point => point.group === group && point.depth <= xmax).sort((a, b) => a.depth - b.depth);
      const color = colors[index];
      const g = add(svg, "g", { class: "series", "data-group": String(group) }); series.set(String(group), g);
      add(g, "path", { d: pathFrom(values.map(point => [x(point.depth), y(point.value)])), fill: "none", stroke: color, "stroke-width": 2.7, "stroke-linejoin": "round", "stroke-linecap": "round" });
      values.forEach(point => {
        const target = add(g, "circle", { cx: x(point.depth), cy: y(point.value), r: 5, fill: "transparent", stroke: "none" });
        const elo = isPuct ? DATA.figure3.puctElo[String(group)] : (sim === 400 ? DATA.figure3.threadElo[String(group)] : null);
        addTooltip(target, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong><br>Depth ${point.depth}<br>Node share ${fmt(point.value * 100, 2)}%<br><span class="soft">Samples ${point.samples.toLocaleString()} moves${elo == null ? "" : ` · ${fmt(elo, 1)} Elo`}</span>`);
      });
    });
    // In-chart legend (top-right corner, where the distributions are ~0). Hovering an entry or a curve highlights that curve.
    const highlight = group => {
      svg.classList.toggle("has-hot", group != null);
      svg.querySelectorAll("g.series, g.legend-entry").forEach(node => node.classList.toggle("hot", node.dataset.group === group));
    };
    const shown = allGroups.filter(group => selected.has(String(group)) && data.some(point => point.group === group));
    const lx = box.l + box.w - 66, ly = box.t + 16, lh = 16;
    const title = add(svg, "text", { x: lx, y: ly, class: "legend-title", "font-size": 12, "font-weight": 600, fill: "#40515a" }, isPuct ? "c" : "Threads");
    if (isPuct) add(title, "tspan", { dy: 3, "font-size": 9 }, "puct");
    shown.forEach((group, i) => {
      const y0 = ly + lh * (i + 1);
      const entry = add(svg, "g", { class: "legend-entry", "data-group": String(group) });
      add(entry, "rect", { x: lx - 6, y: y0 - 12, width: 74, height: lh, fill: "transparent" });
      add(entry, "line", { x1: lx, x2: lx + 18, y1: y0 - 4, y2: y0 - 4, stroke: colors[allGroups.indexOf(group)], "stroke-width": 3, "stroke-linecap": "round" });
      add(entry, "text", { x: lx + 25, y: y0, "font-size": 12, fill: "#40515a" }, String(group));
      const pts = data.filter(point => point.group === group), mass = pts.reduce((t, q) => t + q.value, 0);
      const mean = mass ? pts.reduce((t, q) => t + q.depth * q.value, 0) / mass : 0, samples = pts.length ? Math.max(...pts.map(q => q.samples)) : 0;
      const gElo = isPuct ? DATA.figure3.puctElo[String(group)] : (sim === 400 ? DATA.figure3.threadElo[String(group)] : null);
      addTooltip(entry, `<strong>${isPuct ? "c<sub>puct</sub>" : "threads"} = ${group}</strong><br>Mean depth ${fmt(mean, 2)}${gElo == null ? "" : `<br>Elo ${fmt(gElo, 1)}`}<br><span class="soft">Samples ${samples.toLocaleString()} moves</span>`);
      entry.addEventListener("mouseenter", () => highlight(String(group)));
      entry.addEventListener("mouseleave", () => highlight(null));
    });
    series.forEach((g, group) => { g.addEventListener("mouseenter", () => highlight(group)); g.addEventListener("mouseleave", () => highlight(null)); });
    return svg;
  }

  function renderFigure3() {
    const chart = el("chartArea");
    // The chip groups live inside the two panels; take fresh ones from #controls after renderControls(), else re-use the ones already in the panels.
    const fresh = el("controls").querySelectorAll(".control-group");
    const groups = fresh.length ? [...fresh] : [...chart.querySelectorAll(".control-group")];
    chart.innerHTML = "";
    const wrapper = document.createElement("div"); wrapper.className = "dual-chart";
    const card = (tag, title, group) => { const s = document.createElement("section"); s.className = "shape-panel"; s.innerHTML = `<h4><span class="panel-tag">${tag}</span>${title}</h4>`; if (group) s.appendChild(group); return s; };
    const a = card("(a)", "Varying the exploration coefficient · 400 simulations", groups[0]);
    const aChart = document.createElement("div"); aChart.className = "shape-chart shape-single"; aChart.appendChild(distributionPanel("puct", 400)); a.appendChild(aChart);
    const b = card("(b)", "Varying the thread count", groups[1]);
    const grid = document.createElement("div"); grid.className = "shape-chart shape-grid";
    FIGURE3_SIMS.forEach((sim, i) => { const cell = document.createElement("div"); cell.className = "shape-cell"; cell.appendChild(distributionPanel("threads", sim)); const cap = document.createElement("p"); cap.className = "shape-caption"; cap.innerHTML = `<span class="panel-tag">(b-${i + 1})</span>${sim} simulations`; cell.appendChild(cap); grid.appendChild(cell); });
    b.appendChild(grid);
    chart.append(a, b);
    el("chartLegend").innerHTML = "";
  }

  function figure4Series() {
    const result = [];
    if(state.figure4Dataset!=="paper"&&UPDATES){
      for(const s of UPDATES[state.figure4Dataset]){
        if(!state.figure4Domains.has(s.category))continue;
        result.push({...s,color:PAPER_COLORS[s.category],points:s.points.map(p=>({...p,rawScore:p.rawScore}))});
      }
    }
    const officialGroups = new Map();
    for (const point of DATA.figure4.official) {
      if (state.figure4Dataset!=="paper" || !state.figure4Domains.has(point.category)) continue;
      if (!officialGroups.has(point.label)) officialGroups.set(point.label, []);
      officialGroups.get(point.label).push(point);
    }
    for (const [label, points] of officialGroups) {
      points.sort((a, b) => a.sim - b.sim);
      const category = points[0].category;
      result.push({ label, category, color: PAPER_COLORS[category], alt: points[0].variant === "alt", points: points.map(point => ({ sim: point.sim, relative: point.relative, rawScore: point.rawScore })) });
    }
    const extras = DATA.figure4.extraGames[state.figure4Source];
    [...state.figure4Games].sort().forEach((game, index) => {
      if (!extras[game]) return;
      result.push({ label: pretty(game), category: "extra", color: GAME_COLORS[index % GAME_COLORS.length], alt: false, source: extras[game].source,
        points: extras[game].points.map(point => ({ sim: point.sim, relative: point.normalized, rawScore: point.rawScore })) });
    });
    return result;
  }

  function renderFigure4() {
    const chart = el("chartArea"); chart.innerHTML = "";
    const svg = makeSvg(720, 480, "Figure 4: Go, LLM and Atari relative performance curves with selectable Atari games");
    svg.setAttribute("class","paper-plot figure4-paper");
    const box = { l: 80, t: 24, w: 606, h: 365 };
    const x = sim => box.l + (Math.log10(sim) - Math.log10(5)) / (Math.log10(1000) - Math.log10(5)) * box.w;
    const y = value => box.t + box.h - value * box.h;
    axis(svg, box, [10,100,1000], [0,.2,.4,.6,.8,1], x,y,"Simulation count","Relative score",value=>({10:"10¹",100:"10²",1000:"10³"}[value]),value=>fmt(value,1),{frame:true,gridColor:"#b7b7b7"});
    for(let decade=1;decade<=100;decade*=10)for(let digit=2;digit<10;digit++){const n=decade*digit;if(n>5&&n<1000)add(svg,"line",{x1:x(n),x2:x(n),y1:box.t+box.h,y2:box.t+box.h+3.5,stroke:"#000","stroke-width":1})}
    const series = figure4Series();
    el("figureDescription").textContent=state.figure4Dataset==="paper"?FIGURE_META[4].description:UPDATES.notes[state.figure4Dataset];
    series.sort((a, b) => Number(a.category !== "extra") - Number(b.category !== "extra"));
    series.forEach(item => {
      const points = item.points.filter(point => Number.isFinite(point.relative) && point.sim<=800);
      add(svg, "path", { d: pathFrom(points.map(point => [x(point.sim), y(point.relative)])), fill: "none", stroke: item.color,
        "stroke-width": item.category === "extra" ? 2 : 2.3, "stroke-opacity": item.alt ? .45 : item.role==="added"?.8:1,
        "stroke-dasharray": item.category === "extra" ? "4 3" : item.role==="added"?`${1+(item.puct||0)*2} 2`:"none", "stroke-linejoin": "round", "stroke-linecap": "round" });
      points.forEach(point => {
        const dot = add(svg, "circle", { cx: x(point.sim), cy: y(point.relative), r: 3.3, fill: item.color,
          "fill-opacity": item.alt ? .45 : item.role==="added"?.8:1, stroke: "none" });
        const rawUnit = item.category === "kata" ? "Elo" : item.category === "llm" ? "Elo" : "game score";
        addTooltip(dot, `<strong>${safe(item.label)}</strong><br>${point.sim} simulations<br>relative score ${fmt(point.relative, 3)}${point.adjustment&&point.adjustment!=="none"?`<br>Presentation estimate: ${safe(point.adjustment)}`:""}<br><span class="soft">Raw ${rawUnit}: ${fmt(point.rawScore, 2)}${item.source ? `<br>${safe(item.source)} · scaled separately for each game` : ""}</span>`);
      });
    });
    const papers=series.filter(item=>item.category!=="extra");
    if(papers.length&&state.figure4Dataset!=="paper"){
      const g=add(svg,"g",{}),lx=box.l+10,ly=box.t+10;
      add(g,"rect",{x:lx,y:ly,width:515,height:70,rx:3,fill:"white","fill-opacity":.95,stroke:"#999","stroke-width":1});
      ["kata","atari","llm"].forEach((domain,row)=>{
        const items=papers.filter(s=>s.category===domain).sort((a,b)=>a.puct-b.puct);
        const py=ly+17+row*22;
        add(g,"text",{x:lx+8,y:py+4,"font-size":13,fill:"black"},{kata:"Go",atari:"Atari",llm:"LLM"}[domain]);
        items.forEach((item,col)=>{const px=lx+51+col*74;
          add(g,"line",{x1:px,x2:px+21,y1:py,y2:py,stroke:item.color,"stroke-opacity":item.alt?.45:item.role==="added"?.8:1,"stroke-width":2,"stroke-dasharray":item.role==="added"?`${1+item.puct*2} 2`:"none"});
          add(g,"circle",{cx:px+10,cy:py,r:2.7,fill:item.color,"fill-opacity":item.alt?.45:.9});
          add(g,"text",{x:px+27,y:py+4,"font-size":13,fill:"black"},String(item.puct)+(Number.isInteger(item.puct)?".0":""));
        });
      });
    }else if(papers.length){
      const g=add(svg,"g",{}),lx=box.l+11,ly=box.t+12;
      add(g,"rect",{x:lx,y:ly,width:290,height:85,rx:3,fill:"white","fill-opacity":.95,stroke:"#999","stroke-width":1});
      const ranks={kata:0,llm:1,atari:2};
      papers.forEach(item=>{let px=lx+10+(item.alt?145:0),py=ly+20+ranks[item.category]*24;
        add(g,"line",{x1:px,x2:px+24,y1:py,y2:py,stroke:item.color,"stroke-opacity":item.alt?.45:1,"stroke-width":2.3});
        add(g,"circle",{cx:px+12,cy:py,r:3.1,fill:item.color,"fill-opacity":item.alt?.45:1});
        add(g,"text",{x:px+32,y:py+5,"font-size":16,"font-family":"Times New Roman, Times, serif",fill:"black"},item.label.replace("KataGo","Go"));
      });
    }
    chart.appendChild(svg);
    el("chartLegend").innerHTML = series.filter(item=>item.category==="extra").map(item => `<span class="legend-item"><i class="legend-line" style="background:${item.color};opacity:${item.alt ? .5 : 1}"></i>${safe(item.label)}${item.category === "extra" ? " · comparison" : ""}</span>`).join("") || (series.length ? "" : `<span class="legend-item">Select at least one curve.</span>`);
  }

  function renderNotes() {
    return;  // notes, sources and the paper-reference image are not shown on this site
    if (state.figure === 2) {
      el("figureNotes").innerHTML = `<ul><li>Each box summarizes per-game depth at the corresponding simulation count. <strong>DAvg</strong>The red curve is <strong>a√n / log n</strong></li><li>Selected games are overlaid on the box plots. Differences are more apparent at larger simulation counts.</li><li>The paper reports a≈3.004. The coefficient refitted from archived CSV data is ${fmt(DATA.figure2.currentDataFitCoefficient, 3)}; switch fits in the control panel.</li></ul>`;
      el("figureSources").innerHTML = `<p>Source: nine <code>n*_summary.csv</code>, up to 44 games per simulation count. The plot uses per-game DAvg, not individual search trees.</p><p>Expand the reference image below.</p>`;
    } else if (state.figure === 3) {
      el("figureNotes").innerHTML = `<ul><li><strong>Larger pUCT</strong>typically shifts node mass toward shallower depths.</li><li><strong>More threads</strong>can also shift the distribution toward shallower depths at high parallelism.</li><li>Each search tree is normalized by node count and then averaged across moves. The archived paper CSV may use different sample counts at different depths.</li></ul>`;
      el("figureSources").innerHTML = `<p>Source: Go 400-simulation experiments, <code>pdf_by_puctb.csv</code> and <code>pdf_by_threads.csv</code></p><p><strong>Version note: </strong>The left panel data use 6 threads, while the paper caption says one thread. The right-panel CSV contains an additional 6-thread curve, hidden by default.</p>`;
    } else {
      el("figureNotes").innerHTML = `<ul><li>Go, LLM and Atari are normalized separately. <strong>Heights across domains do not represent equal raw scores</strong></li><li>Additional Atari games use their 5–800 simulation score range and the paper Amidar ceiling ${fmt(DATA.figure4.extraScaleCeiling, 3)}. Use this to compare rising, saturating or declining <strong>trend shapes</strong></li><li>Dashed lines show alternative coefficients. Hover over points for raw scores.</li></ul>`;
      el("figureSources").innerHTML = `<p>${state.figure4Dataset==="paper"?"Original paper reference.":UPDATES.notes[state.figure4Dataset]}</p><p>Six paper curves: <code>mix_curve.csv</code>. Additional games: <code>scaling_all_dt.csv</code> (42 games) or <code>scaling_all.csv</code> (51 games); select the data source in the control panel.</p><p><a href="figure4_puct.html" style="color:#147c6d;font-weight:800">Open the Figure 4 pUCT explorer →</a></p><p>Only observed scores from the selected source are shown. Missing simulation counts are not interpolated.</p>`;
    }
  }

  function currentCsv() {
    const rows = [];
    if (state.figure === 2) {
      rows.push(["figure", "game", "sim", "depth", "selected"]);
      DATA.figure2.points.forEach(point => rows.push([2, point.game, point.sim, point.depth, state.figure2Games.has(point.game)]));
    } else if (state.figure === 3) {
      rows.push(["figure", "panel", "group", "depth", "distribution", "samples"]);
      DATA.figure3.puct.filter(point => state.figure3Puct.has(String(point.group))).forEach(point => rows.push([3, "puct", point.group, point.depth, point.value, point.samples]));
      FIGURE3_SIMS.forEach(sim => threadsAt(sim).filter(point => state.figure3Threads.has(String(point.group))).forEach(point => rows.push([3, `threads_n${sim}`, point.group, point.depth, point.value, point.samples])));
    } else {
      rows.push(["figure","dataset","series","source","sim","display_relative_score","measured_relative_score","raw_score","adjustment"]);
      figure4Series().forEach(item=>item.points.forEach(point=>rows.push([4,state.figure4Dataset,item.label,point.source||item.source||"paper",point.sim,point.relative,point.measuredRelative??point.relative,point.rawScore,point.adjustment||"none"])));
    }
    return rows.map(row => row.map(value => `"${String(value).replaceAll('"', '""')}"`).join(",")).join("\n") + "\n";
  }
  function download(name, contents, type) {
    const url = URL.createObjectURL(new Blob([contents], { type }));
    const link = document.createElement("a"); link.href = url; link.download = name; document.body.appendChild(link); link.click(); link.remove();
    setTimeout(() => URL.revokeObjectURL(url), 1000);
  }
  function downloadSvg() {
    const charts = [...el("chartArea").querySelectorAll("svg")];
    charts.forEach((svg, index) => {
      const copy = svg.cloneNode(true);
      copy.setAttribute("xmlns", SVG_NS);
      const xml = new XMLSerializer().serializeToString(copy);
      download(`tree_shape${charts.length > 1 ? `_${index + 1}` : ""}.svg`, xml, "image/svg+xml;charset=utf-8");
    });
  }

  controls.addEventListener("input", event => {
    if (event.target.id !== "gameSearch") return;
    if (state.figure === 2) state.figure2Search = event.target.value;
    if (state.figure === 4) state.figure4Search = event.target.value;
    renderGameList();
  });
  document.addEventListener("change", event => {
    const target = event.target;
    if (target.id === "figure4Dataset") {
      state.figure4Dataset=target.value;
      renderControls();renderChart();renderNotes();return;
    } else if (target.id === "fitMode") state.figure2Fit = target.value;
    else if (target.id === "showBoxes") state.figure2Boxes = target.checked;
    else if (target.id === "extraSource") {
      state.figure4Source = target.value;
      const available = DATA.figure4.extraGames[state.figure4Source];
      state.figure4Games = new Set([...state.figure4Games].filter(game => available[game]));
      renderGameList();
    } else if (target.dataset.game) {
      const selected = state.figure === 2 ? state.figure2Games : state.figure4Games;
      const limit = state.figure === 2 ? 8 : 6;
      if (target.checked && selected.size >= limit) {
        target.checked = false;
        el("selectionMessage").textContent = `Select up to ${limit} games.`;
        return;
      }
      target.checked ? selected.add(target.dataset.game) : selected.delete(target.dataset.game);
      el("gameCount").textContent = `${selected.size} selected`;
    } else if (target.dataset.puct) {
      target.checked ? state.figure3Puct.add(target.dataset.puct) : state.figure3Puct.delete(target.dataset.puct);
      target.closest(".choice-chip").classList.toggle("selected", target.checked);
    } else if (target.dataset.thread) {
      target.checked ? state.figure3Threads.add(target.dataset.thread) : state.figure3Threads.delete(target.dataset.thread);
      target.closest(".choice-chip").classList.toggle("selected", target.checked);
    } else if (target.dataset.domain) {
      target.checked ? state.figure4Domains.add(target.dataset.domain) : state.figure4Domains.delete(target.dataset.domain);
    }
    renderChart();
  });
  document.addEventListener("click", event => {
    const action = event.target.dataset.action;
    if (!action) return;
    if (action === "f2-preset") state.figure2Games = new Set(["amidar", "bank_heist", "breakout"]);
    else if (action === "f2-clear") state.figure2Games.clear();
    else if (action === "puct-all") state.figure3Puct = new Set(["0", "0.25", "0.5", "1", "1.5", "2.5", "5", "10"]);
    else if (action === "puct-clear") state.figure3Puct.clear();
    else if (action === "thread-paper") state.figure3Threads = new Set(["1", "2", "4", "8", "16", "32", "64", "128"]);
    else if (action === "thread-clear") state.figure3Threads.clear();
    else if (action === "f4-preset") state.figure4Games = new Set(["bank_heist", "breakout", "seaquest"].filter(game => DATA.figure4.extraGames[state.figure4Source][game]));
    else if (action === "f4-clear") state.figure4Games.clear();
    renderControls(); renderChart();
  });

  document.querySelectorAll(".figure-tab").forEach(button => button.addEventListener("click", () => setFigure(Number(button.dataset.figure))));
  window.addEventListener("hashchange", () => { const value = Number(location.hash.slice(1)); if (value === 3 && value !== state.figure) setFigure(value); });
  el("downloadCsv").addEventListener("click", () => download(`tree_shape_data.csv`, currentCsv(), "text/csv;charset=utf-8"));
  el("downloadSvg").addEventListener("click", downloadSvg);
  setFigure(state.figure);
})();
