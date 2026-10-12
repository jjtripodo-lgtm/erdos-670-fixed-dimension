# Current manuscript validation — 12 October 2026

This note covers the public manuscript after a prose-only editorial cleanup. The [original dated validation record](VALIDATION.md), its logs, and its arithmetic result remain unchanged as evidence for the previous TeX/PDF pair. They do not certify the present PDF. The current scientific version before these edits is preserved by public Git commit `632b571a37859bc5141da40e1d0bcae4dc448f9e`.

| Current artifact | SHA-256 |
| --- | --- |
| `paper/fixed_dimension_670.tex` | `c30147a6e5468b1cfb52a3de1c46948555d49bac5fe5a0d5c281b67d460a99a0` |
| `paper/fixed_dimension_670.pdf` | `6b6eb104f507c4a8fc70fee4d6431d81b86a6ed3f301f7761ac2aa65809194ec` |
| [Current arithmetic and reference checks](editorial/arithmetic_and_references.json) | `474ee1905461b7eb95d87bfa7d9ab6d389b8654e1a919d71ad824ae76069d678` |
| [Current final TeX log](editorial/tectonic-final.log) | `6cfce60a7e8a2efd9f66df6d810f9dee1cdce1e614b479b4891950a7f01c58aa` |

The edits remove references to an earlier internal manuscript, proof route, and candidate package from the paper's prose. The theorem statement, proof calculations, and source correspondence remain. A structural comparison against the TeX at commit `632b571` found identical sequences of 338 inline dollar math spans, 36 bracketed displays, 28 equation/alignment environments, eight theorem/lemma/proposition environments, 47 labels, and 60 references or citations. A sorted-key JSON serialization of those extracted sequences has SHA-256 `39ef1b7dacb6be07e872b57ce8a77f7c86807890e1c5a1fae1b73329d874b12f` on both versions. This comparison checks preserved TeX structure; it is not independent proof review.

Tectonic 0.17.0 built the edited TeX twice in separate clean output directories with `SOURCE_DATE_EPOCH=1791763200`, `--only-cached`, and `--keep-logs`. Both builds exited zero and produced byte-identical PDFs. The [first](editorial/tectonic-a.stdout.log) and [second](editorial/tectonic-b.stdout.log) process outputs, corresponding [stderr](editorial/tectonic-a.stderr.log) and [stderr](editorial/tectonic-b.stderr.log), and final log are included. Neither log has a TeX error, unresolved reference, missing character, or overfull box. Four underfull horizontal boxes remain, without visible clipping. Ghostscript 10.07.1 reported 15 pages, and all 15 rendered pages were visually inspected. Extracted text had no `??` or `undefined` marker.

The unchanged `check_manuscript.py` passed all 34 supplementary arithmetic, source-structure, label, reference, and citation checks on the edited TeX. The Lean source and its [source-bound replay status](../fixed670/REPLAY_STATUS.md) are unchanged. The replay reused precompiled upstream imports and is not an independent mathematical or priority review; the editorial PDF build adds no such review.
