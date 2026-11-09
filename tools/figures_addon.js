/* Figure 3 add-on (copied to figures/figures-addon.js by the build).
   - folds the intro card by default behind a "Details" toggle
   - typesets the figure description with KaTeX whenever the figure changes */
(() => {
  'use strict';
  const card = document.querySelector('.intro-card');
  if (card && !card.querySelector('.intro-toggle')) {
    card.classList.add('is-folded');
    const b = document.createElement('button');
    b.type = 'button'; b.className = 'intro-toggle'; b.textContent = 'About this figure'; b.setAttribute('aria-expanded', 'false');
    b.addEventListener('click', () => {
      const folded = card.classList.toggle('is-folded');
      b.textContent = folded ? 'About this figure' : 'Hide';
      b.setAttribute('aria-expanded', String(!folded));
    });
    (card.querySelector('h2') || card).after(b);
  }
  const typeset = () => {
    const el = document.getElementById('figureDescription');
    if (el && window.renderMathInElement) renderMathInElement(el, { delimiters: [{ left: '\\(', right: '\\)', display: false }, { left: '\\[', right: '\\]', display: true }], throwOnError: false });
  };
  const later = () => setTimeout(typeset, 0);
  window.addEventListener('figurechange', later);
  window.addEventListener('hashchange', later);
  window.addEventListener('load', later);
  // The explorer re-sets the text on dataset changes; typeset again whenever the node's text changes.
  const el = document.getElementById('figureDescription');
  if (el) new MutationObserver(muts => { if (muts.some(m => m.type === 'childList' && [...m.addedNodes].some(n => n.nodeType === 3))) later(); }).observe(el, { childList: true });
  later();
})();
