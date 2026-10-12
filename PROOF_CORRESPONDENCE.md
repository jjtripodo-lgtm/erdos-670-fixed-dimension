# Revised paper and integrated final proof path

**Source:** owning development snapshot at
`35c67a69e009c9ca27267077608864987b7e2851`, with all 54 modules exported verbatim here. No access to the original repository is needed for the included checks.
**Paper baseline:** the corrected referee-readable paper at manuscript
checkpoint `11004a667ee7c0cd9934fbe7725f0c2c05a06644`, TeX SHA-256
`55ee3e18f29dfae31ca7326213412a94adccf22bd6f308fd799ffbb77b6d64f8`.
The new paper updates attribution, a forward-increment sign explanation,
formal correspondence, and reproduction wording; its theorem, coordinates,
estimates, and proof mathematics are unchanged.

| Paper step | Exact formal relationship |
| --- | --- |
| Macro Gram reserve, Lemma 2: direct `|N[x]| ≤ 2√(S₀S₂)Q[x] ≤ (√754/64)Q[x] ≤ Q[x]/2`, strict in the middle product step only for `x≠0` | `ColexReserveDirectCS.lean` proves the actual-source direct bound and strict nonzero case. `IncidenceBridge.flattened_colex_two_reserves` now calls `colex_incrementGram_ge_half_tridiagonal_direct`, so this route feeds the final theorem. `ColexReserve.lean` remains imported for other reserve lemmas. |
| Whole B matrix and completion, Lemmas 3–4: `Z_B=−(64/9)Π+9k²Ξ`, `∥B∥≤36mk²/K`, then one-third coefficient budgets | `SourceBQuadraticCoefficients_source_budget` gives the actual two-diagonal whole-family bound. `SourceQuadraticMatrix.source_actual_operator_completion_universal_B_matrix` constructs the same actual macro points, coefficient vectors and global residual using that budget. Both relevant calls in `SourceActualCrossMetric.lean` use this theorem, so the route feeds the final theorem. |
| All local and cross edges, finite diameter and all-n embedding | `SourceActualCrossMetric`, `SourceActualSpectrum`, `SourceActualSeparation`, `SourceActualDiameter`, `SourceAllNEmbedding`, and the unchanged `SourceFixedDimension670` carry the construction to every `n≥68000` in fixed dimension `458999`. |

The old anchored B completion remains in `SourceOperatorBridge.lean` as a
separate checked declaration. The integrated final theorem uses the new
universal completion. A focused affected-chain build and a six-declaration
trust-zero audit were recorded during source integration. The standalone
replay in this candidate checks the exported full import closure from zero
project `.olean` files while reusing pinned upstream compiled imports. Its
exact outcome belongs to this candidate's execution receipt.

The private historical scoped AI paper review applied to the corrected
baseline paper bytes above. It did not review the later reproduction wording,
the integrated source, or this candidate's new replay. Those later bytes
were separately checked as documented in the manuscript validation note;
independent human review remains outstanding.
