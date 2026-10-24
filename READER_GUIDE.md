# Reader and review guide: separated distances in fixed dimension

**John Tripodo** · [ORCID 0009-0006-9180-4953](https://orcid.org/0009-0006-9180-4953)

## Where to start and what to cite

- **Current Hexagon preprint:** [*Separated distances in fixed dimension*, hexagon:2610.00254v2](https://hexagonmath.org/2610.00254v2). Hexagon is a moderated preprint archive, not peer review; it has not assigned a DOI.
- **Immutable GitHub manuscript:** [20 October 2026 PDF](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension/blob/12730b904260f3c10ff2259c49415a20df755ae7/paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf), with [source, exact certificates and instructions](paper/2026-10-20/README.md). Use this link when precise GitHub file version matters; a byte-for-byte identity comparison with the Hexagon-hosted PDF has not been established here.
- **Earlier, different theorem scope:** [hexagon:2610.00254v1](https://hexagonmath.org/2610.00254v1) is the earlier finite R^81794 / 0.735 result. It is superseded by v2 as the current Hexagon record but remains citable for its exact historical version. See [version history](VERSION_HISTORY.md).
- Former Zenodo deposits were **withdrawn** on 22 October 2026. Their DOIs are historical provenance, not current reading or citation destinations.

## Mathematical claims to examine

Under the maintained fixed-dimension interpretation of Erdős Problem #670, the work gives explicit point sets in a Euclidean dimension fixed independently of set size **n**, with unit separation of unordered edge lengths and diameter below `n^2`:

1. For each `0 < epsilon <= 1/2`, let `m = ceil(8192/epsilon)`. Every `n >= 4m` has a configuration in dimension `10m-1` with diameter below `(1/2+epsilon)n^2`. The dimension depends on epsilon, not on n.
2. In dimension 29, arbitrarily large selected sizes admit diameter below `0.998n^2`, with a prime-first Lean endpoint reported in the project status.
3. A **separate written** prime-interval corollary gives dimension-29 configurations for **every** `n >= 400000`, with diameter below `0.999n^2`. This all-size statement is **not** a Lean endpoint.

The earlier finite `R^81794` / `0.735n^2` theorem has a distributed public Lean source closure and a separate exact Formal Conjectures statement adapter. The **newer v2 Lean proof closures remain private**; the public record includes statement excerpts, audit receipts, written proofs, and exact-arithmetic programs. Review [current status](PUBLIC_STATUS.md) and [new-paper source map](paper/2026-10-20/SOURCE_MAP.md) before interpreting formalization claims.

## Small, useful independent review tasks

A reviewer need not assess the entire paper at once. These separable questions would add value:

- Can the rational geometric certificate and 15 positive pivots be independently reconstructed? See [20 October reproduction instructions](paper/2026-10-20/README.md).
- Does the **written** Dusart-based prime-interval step justify the claimed all-size threshold and the strict distance gaps?
- Does the fixed-dimension quantifier structure match the maintained version of Problem #670, and how does it differ from Ho's earlier growing-dimension result? See [prior-art notes](PRIOR_ART.md) and [statement bridge](verification/statement_bridge/README.md).

A negative result or a missing premise should be recorded as such. The finite controls are not a substitute for a universal proof, and a Lean compilation receipt is not independent human proof or a comprehensive priority review.

## Other publicly posted papers

- [Asymptotically optimal degree for the double Hall property](https://github.com/jjtripodo-lgtm/double-hall-optimal-degree)
- [Projective-plane determinant bounds for sparse binary matrices](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants)

AI assistance is disclosed in the manuscript and Hexagon record. No external specialist review, journal acceptance, or independent novelty certification is claimed.
