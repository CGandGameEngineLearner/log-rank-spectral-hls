# arXiv submission checklist

1. Replace `Anonymous draft` in `paper/main.tex` with final author metadata.
2. Confirm title, abstract, acknowledgements, and subject classifications.
3. Run `make all` from a clean checkout.
4. Inspect `output/pdf/spectral_lattice_logrank.pdf` visually.
5. Confirm the source archive contains no code caches or generated screenshots:

   ```bash
   tar -tzf output/arxiv/log-rank-spectral-hls-arxiv.tar.gz
   ```

6. Upload `output/arxiv/log-rank-spectral-hls-arxiv.tar.gz` to arXiv.
7. Add the arXiv identifier and final citation metadata to this repository.
8. Tag the submitted commit, for example `arxiv-v1`.

The repository is submission-ready except for final author metadata and the
external proof/priority audit.
