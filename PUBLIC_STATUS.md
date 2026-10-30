# Erdős #670: result and formalization status

> **29 October 2026 post-Hexagon research checkpoint.** New **private** research records distinguish (i) a **written, exact-computationally checked** R29 result for every `n>=253` with actual diameter `<0.99999 n²`; (ii) **scoped Lean-compiled** B48 finite cases `283<=n<=288` with all point-distance, genuinely unordered edge-gap and diameter conjuncts; and (iii) a separate **eventual** effective R29 coefficient `q=0.98660`, with the source proving bounds `<tau n²` for rational `tau>q` and sufficiently large `n`. The new all-size result is **not** a Lean endpoint, and these later results are **not** part of Hexagon v2. [Precise claims, checks and outstanding public-proof gates](research_updates/R29_2026-10-29.md).

Mathematical scope updated 20 October 2026; archive status corrected 22 October 2026. The [20 October GitHub paper](paper/2026-10-20/Separated_Distances_in_Fixed_Dimension.pdf) presents the two-circle and R29 constructions, also described by the current [Hexagon v2 preprint](https://hexagonmath.org/2610.00254v2). The earlier [Hexagon v1](https://hexagonmath.org/2610.00254v1) identifies the finite 0.735 theorem and remains permanently versioned. Both Zenodo deposits were voluntarily withdrawn on 22 October, so their DOIs are historical provenance rather than preferred citation links. See [version history](VERSION_HISTORY.md) and the [reader and scoped-review guide](READER_GUIDE.md). The 20 October R29 subsequence and epsilon-family Lean companion closures have already been released publicly at [validation/lean-2026-10-20](validation/lean-2026-10-20/README.md). The newer 28 October B48 finite proof closure remains private; Hexagon moderation does not imply independent mathematical review.

## What the 14 October finite result establishes

Erdős asked whether an n-point Euclidean configuration whose different
unordered edge lengths differ by at least one must have diameter at least
$(1-o(1))n^2$. Under the maintained interpretation, the dimension is fixed
before n tends to infinity; the error rate may depend on that dimension.
The original wording leaves the quantifier order implicit.

The [published finite theorem](https://hexagonmath.org/2610.00254?version=1)
gives, for **every integer n >= 36,354**, an injectively indexed configuration
in the same space **R^81,794**, with minimum point distance at least one,
unit separation between all genuinely different unordered edge lengths,
and actual set diameter **strictly below 0.735n²**.
That fixed dimension is independent of n. The gap below coefficient one
persists for arbitrarily large sizes, so this contradicts the maintained
fixed-dimensional lower bound.

Boon Suan Ho's [earlier construction](https://arxiv.org/abs/2604.15305v1)
already disproved the interpretation allowing dimension to grow with n and
was itself formalized in Lean. [His Remark 9](https://arxiv.org/html/2604.15305v1)
left the fixed-dimensional
question open. The contribution here is a fixed-dimensional counterexample,
not the first high-dimensional counterexample or the first Lean proof in
this problem's history. [Prior work and search limits](PRIOR_ART.md) give the
precise attribution and access boundaries.

## What has been formally checked

The public package includes the complete 66-module geometric proof closure
and a separate two-module [exact statement adapter](verification/statement_bridge/README.md).
The adapter converts the indexed construction to the upstream finite-set
predicate, proves the cardinality and actual diameter translation, and
derives the negation of the fixed-dimensional proposition extracted from
[Formal Conjectures at its pinned revision](https://github.com/google-deepmind/formal-conjectures/blob/c77fdd446d23539302aa73bcfae4a9fa962b8382/FormalConjectures/ErdosProblems/670.lean).

The contradiction uses epsilon = 1/4: the conjecture would eventually require
diameter at least 0.75n², while the construction gives strictly less than
0.735n² in that same fixed dimension. No unproved upstream theorem body is
imported. The final declaration is `Erdos670Bridge.erdos_670_negated`.

The [original adapter receipt](verification/statement_bridge/verification/BUILD_RECEIPT.json)
records a source build of all 68 local modules from zero local objects,
trust level zero, a full fresh official-kernel replay, and transitive axiom
audits of five endpoints. Every audited endpoint uses only `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or added conjectural axiom
appears in those reports.

A [later source-bound replay](verification/replay_20261017/README.md), reported
from an Anthropic container separate from the original provider, also passed
the 68-module build, full fresh official-kernel replay, and five-endpoint
axiom audit. Its receipt, normalized logs, original hashes, and initial
missing-zstd failure are now included. The logs support the scoped execution
outcomes; they do not independently attest physical host identity.

Both runs reuse pinned upstream compiled dependencies. Fresh replay uses
the official Lean kernel implementation, not a separately implemented
checker. The statement extraction is checked in the proof's pinned Lean
4.31.0-rc1 environment; it is not an accepted submission or full build of
the newer upstream Formal Conjectures project.

## Later constructions and their internal formalizations

These results have distinct public and private verification scopes. The 20 October R29 and epsilon-family **Lean companions are now public** under [validation/lean-2026-10-20](validation/lean-2026-10-20/README.md); the newer 28 October B48 finite endpoint remains private. None of these results is part of the earlier Hexagon v1 manuscript.
The current Hexagon v2 and the new GitHub paper present their written statements and proofs. Their Lean status
is reported here as internal formalization status, not as additional
publicly reproducible Lean certificates. [Exact statement excerpts and audit records](verification/internal_supplements/README.md)
identify each source and its verification scope without supplying a proof closure.

| Result | Exact quantifiers and bound | Recorded formal scope |
| --- | --- | --- |
| Dimension 29 | For every N, some n >= max(N,600) has an injective configuration in R^29 with minimum distance >= 1, unordered edge-length gaps >= 1, and actual diameter < (499/500)n² = 0.998n². | Exact fixed-dimensional statement negated at d=29 and epsilon=1/1000. The preferred 60-module package has a zero-local-object source build and a later full fresh official-kernel replay. This is an unbounded prime-first subsequence, not every n >= 600. |
| Arbitrary epsilon | For 0 < epsilon <= 1/2, put m = ceil(8192/epsilon). Every n >= 4m has an injective configuration in R^(10m-1), minimum distance >= 1, unordered edge-length gaps > 1, and actual diameter < (1/2+epsilon)n². | Complete geometric endpoint, with only the displayed numerical hypotheses. New modules compiled at trust zero with warnings as errors; final endpoint axioms standard-only. Historical and upstream imports were reused; no full fresh official-kernel replay or separate-machine run is claimed for this family. |
| Uniform dimension bound | For d >= 163840 and n >= 65536, the same separation properties hold in R^d with actual diameter < (1/2+102400/d+40960/n)n². | Corollary of the same internally formalized family, with the same verification limits. |

A separate written corollary in the new paper gives R^29 configurations for **every n >= 400000**, with minimum distance >= 1, unordered edge-length gaps > 1, and actual diameter < 0.999n². It combines the unchanged geometry with [Dusart, Proposition 6.8](https://arxiv.org/abs/1002.0442v1) and exact deletion/padding arithmetic. It has source-reviewed written support and exact arithmetic checks; it is **not a Lean endpoint**.

The dimension-29 companion is now included in the public Lean release described above. It also has a later successful replay record reported
from a separate provider. That record does not transfer to the epsilon-family.
The epsilon assembly review was
performed by a separate worker who also authored helper lemmas; it is not
a wholly independent review of the entire proof.

## Significance and remaining limits

The published result changes the answer to the maintained coefficient-one
fixed-dimensional question: it supplies a counterexample for all sufficiently
large sizes in one fixed dimension, rather than a finite numerical example.
The exact statement adapter makes that logical consequence explicit in Lean.
The prime-first dimension-29 theorem gives a much smaller fixed-dimensional
witness, with different size quantifiers and a weaker diameter coefficient.
Its separate all-size written corollary has the weaker coefficient 0.999.
The epsilon-family approaches the counting coefficient 1/2 by allowing the
fixed dimension to depend on epsilon.

These statements do not settle the plane, determine the least possible
dimension, or construct diameter $(1/2+o(1))n^2$ in one fixed dimension.
Formal verification of exact statements is separate from independent human
proof and priority review, journal acceptance, and recognition by problem
trackers. None of those forms of acceptance is asserted here.

The latest retained [ErdősProblems status](https://www.erdosproblems.com/670)
lists the problem as open and gives
17 April 2026 as its last edit, predating the October preprint. A direct
19 October fetch returned HTTP 403, so this update does not claim a fresh
live-status confirmation or an editorial decision on this work.

The [version history](VERSION_HISTORY.md) distinguishes the retained 0.735
theorem from the archived 0.74 theorem. Palomar production verification and
Prove2Me preflight evidence concern that older version only; they must not
be presented as acceptance of the current constants or later extensions.
