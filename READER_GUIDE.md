# Reader and review guide: separated distances in fixed dimension

**John Tripodo** · [ORCID 0009-0006-9180-4953](https://orcid.org/0009-0006-9180-4953)

## Where to start and what to cite

- **Selected formal R29 statement and proof:** [Palomar PALOMAR-2026-11-11-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-11-000002) and the [pinned public R29 source package](https://github.com/jjtripodo-lgtm/erdos-670-r29). The selected theorem gives **arbitrarily large** sizes in one fixed `R^29`, diameter `<(499/500)n²`, and an exact negation of the fixed-dimensional Formal Conjectures version. This does not formalize the all-size R29 corollary or the arbitrary-epsilon family, and registration does not certify novelty.
- **Separate public v2 Lean companions:** [R29 and epsilon-family source closures](validation/lean-2026-10-20/README.md), with separate pinned project environments and source-bound validation limits.
- **Current Hexagon preprint:** [*Separated distances in fixed dimension*, hexagon:2610.00254v2](https://hexagonmath.org/2610.00254v2). Hexagon is a moderated preprint archive, not peer review; it has not assigned a DOI.
- **Immutable GitHub manuscript:** [20 October 2026 PDF](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/12730b904260f3c10ff2259c49415a20df755ae7/paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf), with [source, exact certificates and instructions](paper/2026-10-20/README.md). Use this link when precise GitHub file version matters; a byte-for-byte identity comparison with the Hexagon-hosted PDF has not been established here.
- **Earlier, different theorem scope:** [hexagon:2610.00254v1](https://hexagonmath.org/2610.00254v1) is the earlier finite R^81794 / 0.735 result. It is superseded by v2 as the current Hexagon record but remains citable for its exact historical version. See [version history](VERSION_HISTORY.md).
- Former Zenodo deposits were **withdrawn** on 22 October 2026. Their DOIs are historical provenance, not current reading or citation destinations.

## Mathematical claims to examine

Under the maintained fixed-dimension interpretation of Erdős Problem #670, the work gives explicit point sets in a Euclidean dimension fixed independently of set size **n**, with unit separation of unordered edge lengths and diameter below `n^2`:

1. For each `0 < epsilon <= 1/2`, let `m = ceil(8192/epsilon)`. Every `n >= 4m` has a configuration in dimension `10m-1` with diameter below `(1/2+epsilon)n^2`. The dimension depends on epsilon, not on n.
2. In dimension 29, arbitrarily large selected sizes admit diameter below `0.998n^2`, with a prime-first Lean endpoint reported in the project status.
3. A **separate written** prime-interval corollary gives dimension-29 configurations for **every** `n >= 400000`, with diameter below `0.999n^2`. This all-size statement is **not** a Lean endpoint.

The earlier finite `R^81794` / `0.735n²` theorem has a distributed public Lean source closure and a separate exact Formal Conjectures statement adapter. The **20 October R29 and epsilon-family companion proofs are public** at [validation/lean-2026-10-20](validation/lean-2026-10-20/README.md); the separately registered [R29 Palomar package](https://github.com/jjtripodo-lgtm/erdos-670-r29) selects only the unbounded-subsequence and fixed-dimension-negation statements. The **every-n>=400000** R29 consequence is a written corollary, not a selected Palomar theorem. Consult [current status](PUBLIC_STATUS.md) and [source map](paper/2026-10-20/SOURCE_MAP.md) for claim-specific verification boundaries.

## Small, useful independent review tasks

A reviewer need not assess the entire paper at once. These separable questions would add value:

- Does the [R29 Palomar Challenge](https://github.com/jjtripodo-lgtm/erdos-670-r29/blob/main/Challenge.lean) genuinely match the fixed-dimensional [Formal Conjectures proposition](https://github.com/google-deepmind/formal-conjectures/blob/2f91d251c07fbbaf9435166d47c11e884a08a6cf/FormalConjectures/ErdosProblems/670.lean), and do the R29 proof and comparator reproduce independently under the permitted axioms?
- Can the rational geometric certificate and 15 positive pivots be independently reconstructed? See [20 October reproduction instructions](paper/2026-10-20/README.md).
- Does the **written** Dusart-based prime-interval step justify the claimed all-size threshold and the strict distance gaps?
- Does the fixed-dimension quantifier structure match the maintained version of Problem #670, and how does it differ from Ho's earlier growing-dimension result? See [prior-art notes](PRIOR_ART.md) and [statement bridge](verification/statement_bridge/README.md).

A negative result or a missing premise should be recorded as such. The finite controls are not a substitute for a universal proof, and a Lean compilation receipt is not independent human proof or a comprehensive priority review.

## Where external assessment or updates can be submitted

As of 18 November 2026, [Thomas Bloom's 6 October notice](https://terrytao.wordpress.com/2026/10/06/changes-to-the-erdos-problems-web-site/) governs the primary erdosproblems.com catalog: new per-problem comments and proof claims are paused and status labels are not shown; update suggestions and high-quality expositions may be sent through the notice's email route. The distinct [teorth/erdosproblems](https://github.com/teorth/erdosproblems) community database supplies the [third-party #670 status display](https://www.erdosproblemaday.com/problem/670), which was still based on an April 2026 database update when checked. [Erdős Problem a Day's #670 attempt form](https://erdosproblemaday.com/submit?problem=670) offers AI-assisted verification, explicitly not human mathematical refereeing. A submitted or posted claim is not presumed independently accepted. No outreach or external status-change action is reported by this documentation update.

## Other publicly posted papers

- [Asymptotically optimal degree for the double Hall property](https://github.com/jjtripodo-lgtm/double-hall-optimal-degree)
- [Projective-plane determinant bounds for sparse binary matrices](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants)

AI assistance is disclosed in the manuscript and Hexagon record. No external specialist review, journal acceptance, or independent novelty certification is claimed.
