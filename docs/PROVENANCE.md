# Provenance

This clean reviewer repository was extracted on 2026-08-26 from the
`math/log-rank-conjecture` subtree of the research repository
`CGandGameEngineLearner/scientific-research`.

Source commit at extraction:

```text
41d96b6aea7d68e44673947afac515ef10c0ce51
```

The paper, five verification scripts, and selected Lean modules were copied
without changing their mathematical statements. The reviewer repository then
received only packaging edits:

- historical Lean modules were omitted;
- the deterministic spectral module's unused dependency was replaced by a
  direct `Mathlib` import;
- a minimal standalone rank-factorization module was added;
- the machine-verification section was rewritten to describe the curated
  ancillary core accurately;
- build, review, and arXiv instructions were added.

No research-workspace Git history, `.lake` tree, compiled Lean object, TeX
auxiliary file, Python cache, screenshot, or temporary enumeration output is
included.
