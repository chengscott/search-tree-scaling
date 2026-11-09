# Search-Tree Scaling in Parallel Monte Carlo Tree Search — project page

Static demo site for the NeurIPS 2026 paper. Everything is plain HTML/CSS/JS and runs from
files alone, so it can be served by GitHub Pages or opened from a local HTTP server.

| Path | What it is |
| --- | --- |
| `index.html`, `site.css` | Project page: title, authors, clickable search-tree teaser, abstract (citation block kept commented out until the official entry exists) |
| `static/` | The paper's overview figure, used as the social-preview image |
| `site-bar.css`, `site-bar.js` | The shared top bar injected into every sub-page |
| `figures/` | Interactive figures: search trees, tree shape and the scaling lab (built from the figure-explorer source with `tools/build_site.py`) |
| `figures/figure1/` | Recorded search-tree browser; `steps/` holds the first 128 steps per setting, the rest come from the data mirrors |
| `proof/` | Guided walkthrough of the Lean formalization (copied from the proof-walkthrough build) |
| `tools/build_site.py` | Rebuilds `figures/` and `proof/` from the sources above |
| `tools/sync_paper_statements.py` | Re-syncs the boxed paper statements in `proof/` to `camera_ready/main.tex` |
| `camera_ready/` | Camera-ready sources (git-ignored; `main.tex` is read only to sync the proof statements) |

## Rebuilding

```bash
SRC="--figures-src <figure explorer folder> --proof-src <proof-walkthrough dist folder>"
python3 tools/build_site.py $SRC                 # everything
python3 tools/build_site.py $SRC --only proof    # one part
python3 tools/build_site.py $SRC --data-shards 5 # also regenerate the five Figure 1 data mirrors
python3 tools/build_site.py $SRC --max-steps 256 # ship more Figure 1 steps locally
```

The two source folders are not part of this repository.

### Figure 1 data and the mirror sites

The full Figure 1 archive is 3.7 GB (78,912 files). A single GitHub Pages site is capped at
1 GB, so the archive is served from several small static sites:

```bash
python3 tools/build_site.py $SRC --data-shards 5
```

This writes five folders next to this repository, `../search-tree-scaling-data-1` through
`-5` (about 740 MB each), each a complete GitHub Pages site: `.nojekyll`, a short `index.html`,
`manifest.json` and `steps/`. Settings are assigned whole to one mirror by size. `snapshots.js`
records each setting's mirror base URL, and the loader in `figures/figure1/app.js` is patched to
prefix it for steps beyond the locally shipped range. The first `--max-steps` steps (default
128, about 172 MB) stay in this repository, so the page works without the mirrors for the first
part of every episode and nothing is fetched from a mirror until the slider reaches it.

Publish each mirror as its own repository with Pages enabled on `main` / root:

```bash
for k in 1 2 3 4 5; do
  d=../search-tree-scaling-data-$k
  git -C $d init -q -b main && git -C $d add -A && git -C $d commit -q -m "Figure 1 data mirror $k"
  git -C $d remote add origin git@github.com:<user>/search-tree-scaling-data-$k.git
  git -C $d push -u origin main
done
```

The base URL template defaults to the mirrors' custom-domain address (the `github.io` address only redirects there over plain HTTP, which browsers block as mixed content);
pass `--data-base` to change it and rebuild the site afterwards. Mirrors are loaded with
`<script>` tags, so no CORS headers are needed. Without `--data-shards`, the build ships only
the first `--max-steps` steps and shortens the step slider accordingly.

The proof walkthrough is copied verbatim, then `sync_paper_statements.py` re-extracts the 14
boxed paper statements from `camera_ready/main.tex` with the walkthrough's own `sync-paper.py`
and patches the rendered bundle. Prose edits are applied textually and verified word by word
against the new LaTeX; any change inside rendered math needs a real MathJax re-render with the
walkthrough's `render-statements.cjs` (requires `mathjax-full` 3.2.2).

## Local preview

```bash
python3 -m http.server 8000
# open http://localhost:8000/
```

## Publishing on GitHub Pages

```bash
git add -A && git commit -m "Project page"
git remote add origin git@github.com:<user>/<repo>.git
git push -u origin main
```

Then in the repository settings choose Pages → Deploy from a branch → `main` / `/ (root)`.
`.nojekyll` is present so files and folders are served as-is. All links are relative, so the
site works at `https://<user>.github.io/<repo>/` without configuration.
