# arXiv submission checklist

This manuscript is intended for the **computer science** archive.

## Categories on the arXiv form

- **Primary:** `cs.CC` (Computational Complexity)
- **Cross-lists:** `cs.DM` (Discrete Mathematics), `math.CO` (Combinatorics)

Do not use `cs.AI`, `cs.LG`, or `cs.SE` as primary. The paper is
communication complexity / discrete mathematics.

Suggested comments field (plain text, no LaTeX):

```text
Restricted-column theorems for the HLS two-level formulation of the
log-rank conjecture. 36 pages. Ancillary code is in the Git repository,
not in this TeX bundle.
```

## Checklist

1. Verify the final author metadata in `paper/main.tex` (currently JinWen Li,
   SouthWest Petroleum University, lifesize1@163.com).
2. Confirm title, abstract, acknowledgements, and the categories above.
3. Run `make paper` (or `make all` if Lean/Python should also pass).
4. Inspect `output/pdf/spectral_lattice_logrank.pdf` visually.
5. Confirm the source archive contains no code caches or generated screenshots:

   ```bash
   tar -tzf output/arxiv/log-rank-spectral-hls-arxiv.tar.gz
   ```

6. At https://arxiv.org/submit choose archive **Computer Science**, then the
   categories above. Upload `output/arxiv/log-rank-spectral-hls-arxiv.tar.gz`.
7. Add the arXiv identifier and final citation metadata to this repository.
8. Tag the submitted commit, for example `arxiv-v1`.

The repository has final author metadata. Complete any required arXiv
AI-use disclosure, and an external proof/priority check, before clicking
submit. This process cannot be finished from the local repo: the upload
uses your arXiv account.
