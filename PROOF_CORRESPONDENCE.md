# Paper-to-Lean proof correspondence

The current manuscript source is `paper/fixed_dimension_670.tex` (SHA-256
`c30147a6e5468b1cfb52a3de1c46948555d49bac5fe5a0d5c281b67d460a99a0`).
All 54 Lean modules in the final theorem's import closure are included from source
commit `35c67a69e009c9ca27267077608864987b7e2851`.

| Paper step | Exact formal relationship |
| --- | --- |
| Macro Gram reserve, Lemma 2: direct `|N[x]| ≤ 2√(S₀S₂)Q[x] ≤ (√754/64)Q[x] ≤ Q[x]/2`, strict in the middle product step only for `x≠0` | `ColexReserveDirectCS.lean` proves the actual-source direct bound and strict nonzero case. `IncidenceBridge.flattened_colex_two_reserves` calls `colex_incrementGram_ge_half_tridiagonal_direct`, so this route feeds the final theorem. `ColexReserve.lean` remains imported for other reserve lemmas. |
| Whole B matrix and completion, Lemmas 3–4: `Z_B=−(64/9)Π+9k²Ξ`, `∥B∥≤36mk²/K`, then one-third coefficient budgets | `SourceBQuadraticCoefficients_source_budget` gives the actual two-diagonal whole-family bound. `SourceQuadraticMatrix.source_actual_operator_completion_universal_B_matrix` constructs the same actual macro points, coefficient vectors and global residual using that budget. Both relevant calls in `SourceActualCrossMetric.lean` use this theorem, so the route feeds the final theorem. |
| All local and cross edges, finite diameter and all-n embedding | `SourceActualCrossMetric`, `SourceActualSpectrum`, `SourceActualSeparation`, `SourceActualDiameter`, `SourceAllNEmbedding`, and `SourceFixedDimension670` carry the construction to every `n≥68000` in fixed dimension `458999`. |

The recorded standalone replay built the 54-module closure from zero project
`.olean` files and audited six declarations at `--trust=0`. It reused compiled
upstream imports; [the replay status](verification/fixed670/REPLAY_STATUS.md)
states that boundary. This table maps the paper to the checked source; it is
not an independent mathematical review of the exposition.
