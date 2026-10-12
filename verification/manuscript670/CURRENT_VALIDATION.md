# Current manuscript validation — 12 October 2026

This record covers the paired TeX and PDF after an appendix prose update that
distinguishes the original macOS source replay from the completed independent
Linux replay and fresh Lean kernel check. The prior [editorial validation](EDITORIAL_VALIDATION_20261012.md)
and [original referee-revised validation](VALIDATION.md) remain unchanged as
historical receipts; neither certifies the current PDF. The theorem statement,
mathematical proof text, calculations, and Lean source files were not edited.

| Current artifact | SHA-256 |
| --- | --- |
| `paper/fixed_dimension_670.tex` | `d1740d28939baee4a8b3f8fdac255aa5f897ca1d37f7467731bb2945e893b8c0` |
| `paper/fixed_dimension_670.pdf` | `ac7a85b0301e334410006ae3d14598350700f96bbd03fabe4ca11e1f8eaf44ce` |
| [Arithmetic and reference checks](verification-wording-20261012/arithmetic_and_references.json) | `35028eaf59484f3d370d37430fd7457beae552b77e321eb82ddb50ce9718529a` |
| [Final TeX log](verification-wording-20261012/tectonic-final.log) | `aeb5662ff519916d9814a332d8976d6507b9444cdbf04467e148dee3fdeb7b0d` |

Tectonic 0.17.0 built the revised TeX twice in separate clean output directories
with `SOURCE_DATE_EPOCH=1791763200`, `--only-cached`, and `--keep-logs`. Both
processes exited zero and produced byte-identical 15-page PDFs and TeX logs.
The [first](verification-wording-20261012/tectonic-a.stdout.log) and
[second](verification-wording-20261012/tectonic-b.stdout.log) build outputs,
their corresponding stderr logs, and the final TeX log are included. The log
has no TeX error, unresolved reference, missing character, or overfull box.
Underfull spacing warnings remain. Pages 13 and 14, which contain the changed
appendix prose, were rendered and visually inspected without clipping.

The unchanged `check_manuscript.py` passed all 34 supplementary exact
arithmetic, source-structure, label, reference, and citation checks on the
current TeX. The [Lean verification record](../fixed670/REPLAY_STATUS.md)
documents the macOS and Linux builds, axiom audits, fresh checker result, and
upstream compiled-cache boundary. This PDF rebuild adds no new Lean execution,
independent mathematical review, or priority review.
