# Near-counting separated distances: an improved family and an optimal exponent within the current certificate

**Research note · 16 October 2026 · Erdős Problem 670 · manuscript-level derivation**

This note continues [the finite criterion in the current manuscript](../paper/fixed_dimension_670.tex), Section 5, and [the first near-counting derivation](FINITE670_SHARPENED_AND_NEAR_COUNTING_2026-10-16.md). Its main contributions are (i) improving the quantitative fixed-dimensional family with no increase in dimension, and (ii) proving that the exponent 5/2 cannot be beaten solely by tuning parameters in the same **five-condition certificate and stated diameter bound**. These deductions are *conditional on the validity of that finite criterion*, and the newly chosen parameters are **not Lean-verified**. No claims of external acceptance or independent specialist review are made.

The reproducible, standard-library-only rational arithmetic is in [`near_counting_tradeoff_certificate.py`](near_counting_tradeoff_certificate.py). It was run locally; no GitHub Actions or CI is required.

## 1. Stronger near-counting corollary

**Theorem 1 (conditional on the finite criterion).** For every integer `r >= 10` and integer `n >= 160*r^5`, there is a distance-separated `n`-point set `X` in the *single fixed space* `R^(360*r^5-1)` such that

```text
  diam(X) < (1/2 + 4/(3*r^2))*n^2.
```

Here *distance-separated* means that different unordered non-diagonal pairs have lengths differing by at least 1. In particular the dimension depends on `r` but **not** on `n`. This improves the prior `1/2+13/(5*r^2)` family without increasing the dimension or the threshold.

**Proof.** Fix `r >= 10`, and put `m0=80*r^5`. For every integer `m>=m0` use the following inputs to the manuscript's five-condition finite criterion:

| Input | Value |
| --- | --- |
| `s` | `1+13/(25*r^2)` |
| `a` | `6/(5*r)` |
| `L` | `3*r^2` |
| `C` | `(21/2)*r^3` |
| `K` | `42*r^3*m` |

Write `t=1/r^2` (`0<t<=1/100`), `kappa=1-1/L=1-t/3`, `gamma=1-a^2/8=1-9*t/50`, and `lambda=kappa*gamma`. The prescribed slope tolerance is `tau=sqrt(1-1/[s*(K+1)])`.

**(C1), digit separation.** Direct multiplication gives the exact polynomial

```text
  s*lambda = 1 + t/150 - 388*t^2/1875 + 39*t^3/1250.
```

For `0<t<=1/100`, discarding the positive cubic term and replacing `t^2` by the upper bound `t/100` gives

```text
  s*lambda >= 1+t*(1/150-388/187500) > 1+t/250.
```

Since `K=42*r^3*m>=3360*r^8`, `s>1` and `sqrt(1-z)>=1-z` on `[0,1]`,

```text
  tau >= 1-1/[s*(K+1)] > 1-t^4/3360 > 1-t/1000.
```

The last inequality follows from `t<=1/100`. Consequently

```text
  tau*s*lambda > (1-t/1000)*(1+t/250) > 1,
```

proving (C1) for **every** integer `r>=10`, not merely a sample.

**(C2), macro harmonic guard.** By Cauchy–Schwarz, for every integer `m>=2`,

```text
  H_m^2 <= m*sum_{j=1}^m 1/j^2 < 2*m,
```

where the strict upper bound uses `1/j^2 <= 1/[j(j-1)]` for `j>=2` and a telescoping series. Thus `16384*H_m^2 < 32768*m < 42000*m <= K`, and `K>=m`.

**(C3), radius shortening.** `K=42*r^3*m=4*C*m>4*C*m/s^3` because `s>1`.

**(C4), orthogonal completion.** For `r>=10`, `s<101/100`, hence `84*s^2<90`; also `a=6/(5*r)` and `K+m=(42*r^3+1)m<=43*r^3*m`. Squaring the positive sides, the required right-hand side is strictly below

```text
  (84*s^2/a)^2*(K+m) < (75*r)^2 * 43*r^3*m
                          = 241875*r^5*m.
```

In contrast, since `m>=80*r^5`,

```text
  (C*m)^2 = (441/4)*r^6*m^2 >= 8820*r^11*m
                                   > 241875*r^5*m.
```

This proves (C4).

**(C5), local ruler chords.** Directly,

```text
  C*a*gamma - 4L = (3/5)*r^2 - 567/250 > 0
```

for all `r>=10`.

All five conditions therefore hold for every `m>=m0` and every `k>=2`. The criterion gives `mk` distance-separated points in `R^(3m-1)` with diameter bounded by

```text
  [s^3*(42*r^3*m+m*(m-1)/2)+s^2/(2*tau)]*k^2.
```

Since `tau>1/2`, on division by `(mk)^2` we obtain, for all `m>=m0`, the *strict* bound

```text
  s^3*(1/2+42*r^3/m0) + s^2/m0^2.
```

For arbitrary `n>=2*m0`, put `k=floor(n/m0)>=2` and `m=ceil(n/k)`. Then `m0<=m<=3*m0/2=120*r^5` and `n<=mk<(1+1/m0)n`. Delete `mk-n` points, preserving distance separation, and pad coordinates to `R^(3*120*r^5-1)`.

Put `u=1/r` and define the following **explicit rational polynomial**:

```text
  beta(u) = [ (1+13*u^2/25)^3 * (1/2+21*u^2/40)
            +(1+13*u^2/25)^2 * u^10/6400 ]
            * (1+u^5/80)^2.
```

The resulting `n`-point set has diameter `<beta(1/r)*n^2`. Every coefficient of `beta(u)-1/2` is nonnegative, and the constant and linear terms vanish. Hence `(beta(u)-1/2)/u^2` is nondecreasing on `u>=0`. The exact rational certificate checks

```text
  beta(1/10) =
   13137230981515648942128611587115169
   /25600000000000000000000000000000000
   = 0.513173085215455...

  [1/2+(4/3)*(1/10)^2] - beta(1/10) =
   12307055453053173614165238654493
   /76800000000000000000000000000000000 > 0.
```

It follows uniformly for `0<u<=1/10` that `beta(u)<1/2+(4/3)u^2`, proving the theorem. QED.

For `r=10`, this provides the explicit paper-level claim `d=35,999,999`, `n>=16,000,000`, diameter `<(77/150)n^2 = 0.513333...n^2`. The dimension is very large, but independent of `n`.

## 2. The 5/2 exponent is unavoidable inside this certificate

Let the criterion's **stated normalized diameter guarantee** be

```text
  U(m,L,s,a,C,K) = [s^3*(K+m*(m-1)/2)+s^2/(2*tau)]/m^2.
```

**Theorem 2 (necessary parameter cost).** Suppose `m>=4`, `L>=3`, `s>1`, `0<a<=1`, `C,K>0` satisfy (C1)–(C5), with derived `tau` as in the criterion. If for some `0<epsilon<=1/4` this *particular bound* obeys `U<1/2+epsilon`, then

```text
  m > [75*sqrt(5)/4] * epsilon^(-5/2).
```

This is a quantitative lower bound for what **the current certificate can guarantee**. It is *not* a lower bound for the optimal diameter of all geometric configurations, nor for every analysis of our specific point set.

**Proof.** Write `delta=s-1>0`, `kappa=1-1/L`, and `gamma=1-a^2/8`. Because `tau<1`, (C1) implies `s*kappa*gamma>1`; separately `s*kappa>1` and `s*gamma>1`. Therefore

```text
  L > s/delta > 1/delta,
  a^2 < 8*delta/s < 8*delta.
```

By (C5), `C*a*gamma>4L`; since `gamma<=1`,

```text
  C > 4*L/a > sqrt(2)*delta^(-3/2).
```

Moreover (C5), `L>=3`, `a<=1`, and `gamma<=1` give `C>12`. The hypothesis `U<1/2+epsilon<=3/4`, together with nonnegative `K` and `m>=4`, implies

```text
  (s^3/2)*(1-1/m) <= U < 3/4,
  so s^3 < 2.
```

Using (C3), `K>=4Cm/s^3`, and dropping the positive terminal `s^2/(2*tau*m^2)` gives

```text
  U >= s^3/2 + (4*C-s^3/2)/m
    > s^3/2 + 3*C/m
    > 1/2 + (3/2)*delta + 3*sqrt(2)/(m*delta^(3/2)).
```

Here `s^3=(1+delta)^3>1+3delta`. Consequently

```text
  epsilon > (3/2)*delta + 3*sqrt(2)/(m*delta^(3/2)),
  0 < delta < (2/3)*epsilon.
```

Rearranging and setting `x=delta/epsilon`,

```text
  m > [3*sqrt(2)] /
      [epsilon^(5/2)*x^(3/2)*(1-3*x/2)].
```

On `0<x<2/3`, the function `x^(3/2)*(1-3x/2)` is maximal at `x=2/5` (differentiate its square, giving the factor `3*x^2*(1-3x/2)*(1-5x/2)`). Thus

```text
  m > 3*sqrt(2) * (5/2)^(5/2) * epsilon^(-5/2)
    = [75*sqrt(5)/4] * epsilon^(-5/2).
```

QED.

**Interpretation.** Theorem 1 supplies the **upper** dependence `m=O(epsilon^(-5/2))` with fixed `m` once the desired accuracy is chosen. Theorem 2 proves the **matching exponent lower bound** for any attempt to achieve that accuracy by tuning (C1)–(C5) while using the criterion's explicit diameter estimate. Accordingly, within this precise proof template, the exponent `5/2` is optimal. As the advertised ambient dimension is `3m-1`, this translates into the same exponent in dimension. Any breakthrough in the exponent requires a different geometric arrangement, a stronger distance comparison, or an improved certificate that escapes at least one of the forcing inequalities.

## 3. Further research

- **Geometry seam:** The bottleneck comes from the joint inequalities `L > 1/(s-1)`, `a < sqrt(8(s-1))`, `C > 4L/a`, and `K >= 4Cm/s^3`. Investigate alternative local rulers or local curves whose chord separation does not force `C` to grow as `(s-1)^(-3/2)`.
- **Dimension seam:** The theorem is sharp **for this bound**, not for all orthogonal-circle placements. A more precise upper diameter analysis of the same points could beat the obstruction without violating C1–C5.
- **Formalization seam:** Neither new corollary is covered by the existing hardcoded Lean proof of the `0.735` theorem. A parameterized Lean finite criterion and independent specialist review would be needed before upgrading the formal/public manuscript claims.

**Reproduce:** `python3 research/near_counting_tradeoff_certificate.py` from the repository root. This checks rational polynomial and gate inequalities and sampled instances for regression. Universal proofs are given in this note; the sample instances alone are not a substitute for the algebra.
