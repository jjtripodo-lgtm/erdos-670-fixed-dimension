# Theorem scope and source correspondence

20 October 2026. All bounds below are for actual set diameter and genuinely different unordered edges. All configurations have minimum point distance at least one.

| Result | Exact quantifiers and bound | Verification scope |
| --- | --- | --- |
| Two-circle family | 0 < epsilon <= 1/2; m=ceil(8192/epsilon); every integer n>=4m; dimension 10m-1; diameter<(1/2+epsilon)n²; edge gaps>1 | Written proof and internal Lean endpoint `Erdos670EpsilonFamily.epsilon_family`; recorded compilation reused checked imports. No new replay here. |
| Uniform form | d>=163840, n>=65536; dimension d; diameter<(1/2+102400/d+40960/n)n²; edge gaps>1 | Written corollary and `Erdos670EpsilonFamily.uniform_family`, same formal scope. |
| R29 prime-first | For every N, some n>=max(N,600); dimension29; diameter<(499/500)n²; formal edge gaps>=1 | `Erdos670R29.r29_unbounded_counterexamples`; finite-set transport and negation in `Erdos670R29Minimal.finite_set_counterexamples` and `not_fixedDimensionStatement_r29`. Written scalar estimates are strict. Existing source-bound build/replay records only. |
| R29 all-size | Every n>=400000; dimension29; diameter<(999/1000)n²; edge gaps>1 | Written geometry plus Dusart Proposition6.8 and exact padding. Not a Lean endpoint. |
| Earlier finite comparison | Every n>=36354; dimension81794; diameter<(147/200)n²; edge gaps>=1 | Existing complete public 66-module proof closure and separate statement adapter, unchanged. |

The first family lets dimension depend on epsilon. No single fixed dimension attaining coefficient 1/2+o(1), planar result, least-dimension or optimal-coefficient claim is made.

## Exact source identities

The paper reorganizes the 19 October readable draft, with the separate existing all-size consequence added. The finite macro appendix is unchanged mathematically. The references retain the earlier unrestricted-dimensional paper and deterministic-incidence result as prior work; those private manuscripts are not exported.

| Source object | Git blob identity |
| --- | --- |
| 19 October assembled draft | `01caeb269a7fc253067ed802bd113b2cd87f557a` |
| Two-circle written theorem | `63fdaf3adb4357e39781a9020d8815a4d0de4dca` |
| R29 written theorem | `68e8afd27a56310aa29f5c0c2bae656e45a41852` |
| Epsilon formal source | `0670e6c3af874912519aacaa79dd6a9b77f16e22` |
| R29 indexed formal source | `8d09609eef219795b3dce076f3dc10c50a901ee0` |
| R29 minimal adapter | `8ac23307f1491887b81d8a6edf67e80a709929fb` |
| R29 rational matrices | `0eea70459e28e7d23ea73f22edf202f37d6eea5c` |
| Original R29 checker | `b2ad16b30074bc80eccda015bcadbcf055f5ca71` |
| Existing all-size addendum | `baaac69c248034f10bb9c08ff7cd644389117a16` |
| Public finite manuscript | `a9117d055d977c8745211959e0638f1896a2331c` |
| Earlier growing-dimensional manuscript (citation only) | `281b3d3ee2ce45ff2f38e833b4c4c9ee75f04038` |
| Earlier deterministic-incidence theorem (citation only) | `fc556ffdd922ee4183c971ad644f1d1ea3903785` |

Git blob identities identify bytes, not an execution or independent-review receipt. The [existing public endpoint records](../../verification/internal_supplements/SOURCE_RECORDS.json) include full-source SHA-256 hashes and distinguish declarations, audit excerpts and replay provenance. Newer full proof closures remain private.

## Prime-interval input

Pierre Dusart, *Estimates of Some Functions Over Primes without R.H.*, [arXiv:1002.0442v1](https://arxiv.org/abs/1002.0442v1), Proposition6.8, printed page8, gives a prime x<p<=x(1+1/(25(log x)^2)) for x>=396738. The exact versioned PDF was retrieved and its page8 visually inspected on20 October2026. PDF SHA-256: `3f11eca84613ad00e6a447f99b318d5c3d76e360283efcc6d3eebdda25ff3923`.

At x=6ceil(n/6)>=400000, log(x)>2 gives the existing admissible-prime hypothesis. Deleting at most five points preserves separation. The exact margin 999/1000-(499/500)(1+5/400000)^2 is `3120159501/3200000000000`, positive. Dusart's theorem is a primary-literature input, not independently reproved or formally checked here.
