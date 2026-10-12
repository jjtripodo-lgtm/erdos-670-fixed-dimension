# Referee-revised integrated manuscript validation

**Private candidate checked 12 October 2026.** This receipt covers the paired TeX and PDF in `paper/` after the four scoped adversarial-referee exposition and attribution fixes. The referee's report reviewed the previous candidate at merged main `7fbae9afd57af5336877dcd18c69a1d076a50331`; it does not automatically review these new bytes. A focused review of the changed proof passages and independent specialist review remain open.

| Artifact | SHA-256 |
| --- | --- |
| `paper/fixed_dimension_670.tex` | `d7faa1e6d5dc5f595655a3055371030b3ae05be7015c49d9672bc38eac520a11` |
| `paper/fixed_dimension_670.pdf` | `8b9c48959835386795b78e14ee200ca71413c0c31432c546179652b42ce403ea` |
| `arithmetic_and_references.json` | `bad8fbc361bc47f5cbb4a38e7649b3b815f5e9986cfeee02df3ba80a12b85d1f` |
| `tectonic-final.log` | `d0f7e9f6d0773ec74e0bed6db01109bd5345bd8eb89226d38d1304827b0d1d5e` |

The TeX diff against the merged candidate displays the forward-projection sign and endpoint identities, the conditional-Gram interval identity, and the actual perturbation norm/orthogonality cancellation. It adds a bounded Brass comparison and bibliography item, and moves operational replay detail to a titled appendix. The theorem statement, numbered metric identities, construction, scalar estimates, and final Lean source route were not changed. The exact baseline-to-revision TeX patch and full original referee report are preserved privately outside the selected-tree allowlist. This manuscript revision is **not** a new Lean replay: the unchanged 54 Lean modules and prior execution receipt retain only their recorded source-bound scope.

`check_manuscript.py` passed all 34 supplementary exact rational, source-structure, label, reference, and citation checks, producing the JSON above. Tectonic 0.17.0 built the revised TeX twice from separate clean output directories with `SOURCE_DATE_EPOCH=1791763200` and `--only-cached`; both processes exited zero and the PDFs were byte-identical. The copied final log has no TeX error, unresolved reference, missing character, or overfull box. Underfull spacing warnings remain in the prior-work paragraph, formal summary, appendix transition, and bibliography; they do not visibly clip text.

Ghostscript 10.07.1 rendered all 15 pages and extracted their text. Every rendered page was inspected in eight complete two-page contact sheets (the last contains page 15): theorem, Gram and sign displays, literal metric and cancellation, scalar bounds, Brass citation, formal scope, appendix, module map, provenance, and six bibliography entries are present without visible clipping. Extracted text and logs have no `??` or `undefined` marker. Render and build directories are generated artifacts outside the candidate manifest.

The manuscript states the same unconditional all-`n` theorem as the unchanged final Lean declaration: `n ≥ 68000`, fixed dimension `458999`, minimum pair distance at least one, distinct unordered-edge distance gaps at least one, and strict diameter `< (37/50)n²`. The prior source-bound Lean replay and upstream-cache limits are documented in [REPLAY_STATUS.md](../fixed670/REPLAY_STATUS.md). Formal checking establishes the encoded statement relative to the pinned environment and declared axioms; it does not independently referee this rewritten exposition or certify priority.
