/* Injects the shared project bar. Include with <script defer src="../site-bar.js"></script> from any page; links resolve relative to this script's own location, which is the site root. */
(() => {
  const script = document.currentScript;
  // The script lives at the site root, so its directory is the root. Fall back to data-root
  // (relative to the page) only when the script URL is unavailable.
  const root = script?.src ? new URL('.', script.src) : new URL(script?.dataset.root || '.', location.href);
  const here = location.pathname;
  const links = [
    { id: 'home', label: 'Overview', href: 'index.html', test: p => !/\/(figures|proof)\//.test(p) },
    { id: 'figures', label: 'Interactive figures', short: 'Figures', href: 'figures/figure1/index.html', test: p => /\/figures\//.test(p) },
    { id: 'proof', label: 'Proof walkthrough', short: 'Proof', href: 'proof/index.html', test: p => /\/proof\//.test(p) },
    { id: 'neurips', label: 'NeurIPS', href: 'https://neurips.cc/virtual/2026/loc/sydney/poster/150219', ext: true, hide: true },
    { id: 'code', label: 'Code', href: 'https://github.com/chengscott/search-tree-scaling', ext: true, hide: true },
  ];
  const bar = document.createElement('header');
  bar.className = 'site-bar';
  bar.setAttribute('role', 'banner');
  const brand = document.createElement('a');
  brand.className = 'site-bar-brand';
  brand.href = new URL('index.html', root).href;
  brand.innerHTML = '<span class="site-bar-title">Search-Tree Scaling<em>in Parallel Monte Carlo Tree Search</em></span>';
  const nav = document.createElement('nav');
  nav.className = 'site-bar-links';
  nav.setAttribute('aria-label', 'Project pages');
  for (const l of links) {
    const a = document.createElement('a');
    a.href = /^https?:/.test(l.href) ? l.href : new URL(l.href, root).href;
    a.innerHTML = (l.short ? `<span class="long">${l.label}</span><span class="short">${l.short}</span>` : l.label) + (l.ext ? '<span class="arrow" aria-hidden="true">↗</span>' : '');
    if (l.ext) { a.className = 'ext'; a.target = '_blank'; a.rel = 'noopener'; }
    if (l.hide) a.dataset.hideNarrow = '';
    if (l.id === 'home') a.dataset.home = '';
    if (l.test && l.test(here)) { a.classList.add('active'); a.setAttribute('aria-current', 'page'); }
    nav.append(a);
  }
  bar.append(brand, nav);
  document.body.prepend(bar);
})();
