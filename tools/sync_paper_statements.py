#!/usr/bin/env python3
"""Bring proof/paper-statements.js in line with the camera-ready main.tex.

The proof walkthrough renders its boxed paper statements with MathJax (see
render-statements.cjs in the walkthrough repo). That renderer needs the
mathjax-full package, which is not installed on this machine, so this script:

  1. runs the walkthrough's own sync-paper.py against the camera-ready main.tex
     in a temporary directory, producing fresh statement bodies + line numbers;
  2. copies body / source_start / source_end for every statement into the
     rendered bundle;
  3. applies the prose-only edits between the two paper versions to the
     rendered HTML (listed in PATCHES below, each asserted to match exactly once);
  4. checks that, for every statement, the prose of the rendered HTML now
     matches the prose of the new body. Any unexpected difference fails the run,
     which means the rendered HTML needs a real MathJax re-render.

Usage: sync_paper_statements.py --tex camera_ready/main.tex \
          --walkthrough <proof-walkthrough folder> --bundle proof/paper-statements.js
"""
import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

# (chapter, regex to find in rendered html, replacement). Each must match exactly once.
PATCHES = [
    ('theorem2',
     r'Assume also that the optimal-action priors are uniformly bounded away from zero at nonterminal states\. ',
     ''),
    ('theorem4',
     r' concurrent threads with <span class="math-typeset math-inline" role="math" aria-label="T\(n\)=o\(n\)">.*?</mjx-container></span></span>,',
     ' concurrent threads,'),
]
# Display equations whose only change is the trailing punctuation glyph: (chapter, old aria-label, new aria-label).
PUNCTUATION_SWAPS = [
    ('theorem4', r'H_{\mathrm{opt}}(n,T)=\Theta(\sqrt n),', r'H_{\mathrm{opt}}(n,T)=\Theta(\sqrt n).'),
]
GLYPH = {',': '2C', '.': '2E'}


def load_bundle(path: Path):
    src = path.read_text(encoding='utf-8')
    head, body = src.split('=', 1)
    return head + '=', json.loads(body.rstrip().rstrip(';'))


def run_sync(tex: Path, walkthrough: Path) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        (tmp / 'wt').mkdir()
        shutil.copy2(walkthrough / 'sync-paper.py', tmp / 'wt' / 'sync-paper.py')
        shutil.copy2(tex, tmp / 'main.tex')
        subprocess.run([sys.executable, '-I', 'sync-paper.py'], cwd=tmp / 'wt', check=True, capture_output=True)
        return json.loads((tmp / 'wt' / 'paper-source.json').read_text(encoding='utf-8'))


def body_for_part(body: str, part):
    """The renderer shows one enumerated part of a multi-part theorem; mirror that for comparison."""
    if part is None or '\\begin{thmparts}' not in body:
        return body
    head, rest = body.split('\\begin{thmparts}', 1)
    items = re.split(r'\\item', rest.split('\\end{thmparts}', 1)[0])[1:]
    return head + ' ' + items[int(part) - 1]


def prose_words(text: str) -> list:
    """Words outside math/refs, lowercase, for comparing LaTeX body vs rendered HTML."""
    text = re.sub(r'\\begin\{equation\}.*?\\end\{equation\}', ' ', text, flags=re.S)
    text = re.sub(r'\$[^$]*\$', ' ', text)
    text = re.sub(r'\\label\{[^}]*\}|\\ref\{[^}]*\}|\\begin\{[^}]*\}|\\end\{[^}]*\}|\\item|\\textbf|\\emph', ' ', text)
    text = re.sub(r'<div class="statement-equation">.*?</div>', ' ', text, flags=re.S)
    text = re.sub(r'<span class="math-typeset[^"]*".*?</mjx-container></span></span>', ' ', text, flags=re.S)
    text = re.sub(r'<a [^>]*>.*?</a>', ' ', text, flags=re.S)
    text = re.sub(r'<[^>]+>', ' ', text)
    text = text.replace('&amp;', '&').replace('&lt;', '<').replace('&gt;', '>')
    words = re.findall(r"[A-Za-z][A-Za-z'-]*", text)
    # Numbers in reference labels ("Assumption 1") are produced by rendering, not by the body.
    return [w.lower() for w in words]


def swap_punctuation(html: str, old_label: str, new_label: str) -> str:
    span_re = re.compile(r'<span class="math-typeset math-display" role="math" aria-label="([^"]*)">.*?</mjx-container></span></span>', re.S)
    spans = list(span_re.finditer(html))
    target = [m for m in spans if m.group(1) == old_label]
    if len(target) != 1:
        sys.exit(f'expected exactly one display equation labelled {old_label!r}, found {len(target)}')
    new_code = GLYPH[new_label[-1]]
    donors = [m for m in spans if re.search(rf'<g data-mml-node="mo"[^>]*><path data-c="{new_code}" d="([^"]*)"></path></g>\s*</g></g></svg>', m.group(0))]
    if not donors:
        sys.exit(f'no rendered glyph {new_code} available to borrow for {new_label!r}')
    donor_d = re.search(rf'<path data-c="{new_code}" d="([^"]*)"></path></g>\s*</g></g></svg>', donors[0].group(0)).group(1)
    m = target[0]
    seg = m.group(0)
    old_code = GLYPH[old_label[-1]]
    pat = re.compile(rf'(<g data-mml-node="mo"[^>]*>)<path data-c="{old_code}" d="[^"]*"></path></g>(\s*</g></g></svg>)')
    if len(pat.findall(seg)) != 1:
        sys.exit(f'could not locate the trailing {old_label[-1]!r} glyph in {old_label!r}')
    seg = pat.sub(lambda mm: f'{mm.group(1)}<path data-c="{new_code}" d="{donor_d}"></path></g>{mm.group(2)}', seg)
    seg = seg.replace(f'aria-label="{old_label}"', f'aria-label="{new_label}"', 1)
    return html[:m.start()] + seg + html[m.end():]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--tex', type=Path, required=True)
    ap.add_argument('--walkthrough', type=Path, required=True, help='proof-walkthrough folder (holds sync-paper.py)')
    ap.add_argument('--bundle', type=Path, default=Path(__file__).resolve().parents[1] / 'proof' / 'paper-statements.js')
    args = ap.parse_args()

    head, bundle = load_bundle(args.bundle)
    fresh = run_sync(args.tex, args.walkthrough)
    by_chapter = {s['chapter']: s for s in fresh['statements']}
    if set(by_chapter) != set(bundle):
        sys.exit(f'statement sets differ: {sorted(set(by_chapter) ^ set(bundle))}')

    changed_bodies = []
    for ch, st in bundle.items():
        new = by_chapter[ch]
        if st['body'] != new['body']:
            changed_bodies.append(ch)
        for k in ('title', 'subtitle', 'part', 'body', 'source_start', 'source_end'):
            st[k] = new[k]

    for ch, pattern, repl in PATCHES:
        html = bundle[ch]['html']
        hits = re.findall(pattern, html, flags=re.S)
        if len(hits) == 0 and re.search(re.escape(repl) if repl else '(?!)', html):
            print(f'[{ch}] patch already applied, skipping')
            continue
        if len(hits) != 1:
            sys.exit(f'[{ch}] patch matched {len(hits)} times, expected 1: {pattern}')
        bundle[ch]['html'] = re.sub(pattern, repl, html, flags=re.S)
    for ch, old_label, new_label in PUNCTUATION_SWAPS:
        if f'aria-label="{new_label}"' in bundle[ch]['html'] and f'aria-label="{old_label}"' not in bundle[ch]['html']:
            print(f'[{ch}] punctuation already swapped, skipping')
            continue
        bundle[ch]['html'] = swap_punctuation(bundle[ch]['html'], old_label, new_label)

    problems = []
    for ch, st in bundle.items():
        a, b = prose_words(body_for_part(st['body'], st['part'])), prose_words(st['html'])
        if a != b:
            problems.append((ch, a, b))
    if problems:
        for ch, a, b in problems:
            i = next((k for k in range(min(len(a), len(b))) if a[k] != b[k]), min(len(a), len(b)))
            print(f'[{ch}] prose mismatch near word {i}:\n  body: {" ".join(a[max(0,i-6):i+8])}\n  html: {" ".join(b[max(0,i-6):i+8])}')
        sys.exit('rendered HTML no longer matches the paper prose; re-render with render-statements.cjs')

    bundle_src = head + json.dumps(bundle, ensure_ascii=False, separators=(',', ':')) + ';\n'
    header = f'/* Extracted from main.tex (sha256 {fresh["sha256"]}); generated by sync-paper.py and render-statements.cjs, prose synced by tools/sync_paper_statements.py. */\n'
    bundle_src = re.sub(r'^/\*.*?\*/\n', header, bundle_src, count=1, flags=re.S)
    args.bundle.write_text(bundle_src, encoding='utf-8')
    print(f'updated {args.bundle} from {args.tex} (sha256 {fresh["sha256"][:12]}); bodies changed: {changed_bodies or "none"}')


if __name__ == '__main__':
    main()
