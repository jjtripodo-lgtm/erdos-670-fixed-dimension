> **Subsequent discovery (16 October 2026):** [An improved near-counting family and an optimal exponent within the current five-condition certificate](NEAR_COUNTING_SHARP_DIMENSION_TRADEOFF_2026-10-16.md) sharpen Theorem B below from `1/2+13/(5r^2)` to `1/2+4/(3r^2)` at the same dimension and threshold. The later note also proves that the exponent `5/2` is forced **within this certificate's stated diameter bound**. The new parameters are manuscript-level deductions, not part of the hardcoded Lean endpoint.

# Discovery: 0.656 in the original fixed dimension, and near-counting asymptotics

**16 October 2026 | paper-level corollaries of the existing finite criterion**

Theorem (Finite criterion) in [the manuscript](../paper/fixed_dimension_670.tex), Section 5, gives distance-separated mk-point configurations in R^(3m-1) whenever five scalar conditions (C1)-(C5) hold. This note proves two improved consequences by giving fresh exact parameters. The exact-rational audit is [here](exact_parameter_certificate.py).

**Status and scope:** These are mathematical deductions conditional on the correctness of the manuscript's five-condition criterion. The existing Lean endpoint is HARD-CODED to the older 0.735 parameters and has NOT been adapted to either new result. Do not describe these results as Lean-verified or externally accepted. No GitHub Actions are needed.

## A. Sharper explicit fixed-dimensional statement

**Proposition A.** For all integers n >= 36354 there exists a distance-separated n-point configuration in R^81794 with diameter strictly less than (82/125)n^2 = 0.656n^2.

*Proof.* Let m0=18177. For every integer m>=m0, use

| Variable | Value |
| --- | --- |
| s | 10557/10000 |
| a | 3/8 |
| L | 28 |
| C | 305 |
| K | 1037m |
| rational tolerance lower bound tau0 | 99999/100000 |

The criterion derives gamma=1-a^2/8=503/512, kappa=1-1/L=27/28, and lambda=kappa*gamma=13581/14336. Here tau=sqrt(1-1/[s(K+1)]).

The harmonic bound H_18177<16 follows by partitioning the sum into dyadic blocks. For m>=4, H_m>=2, hence

~~~
(H_(m+1)/H_m)^2 = (1+1/((m+1)H_m))^2
 <= 1+1/(m+1)+1/(4(m+1)^2) <= 1+1/m.
~~~

Thus H_m^2/m is nonincreasing, so for m>=m0 we have 16384 H_m^2 <= (16384*256/m0)m < 1037m=K. In addition K>=m, proving (C2).

All other margins are *exact rational* positive quantities:

~~~
1-tau0^2-1/(s*(1037*m0+1))
  = 793974817506013/39798939870000000000 > 0
tau0*s*lambda-1
  = 1318325383/14336000000000 > 0                   [C1]
1037*s^3-4*C
  = 113749004641/1000000000000 > 0                   [C3]
C^2*m0-(84*s^2/a)^2*1038
  = 7940540504479830652569/4882812500000 > 0       [C4, squared]
C*a*gamma-4*L
  = 1493/4096 > 0                                    [C5]
~~~

The first margin gives tau>tau0. For (C4), K+m=1038m and the squared inequality at m0 implies the same at all larger m. Hence the finite criterion applies for **every** integer m>=m0 and k>=2, supplying an mk-point set with diameter at most

~~~
[s^3*(1037m + m(m-1)/2) + s^2/(2tau)]*k^2.
~~~

Normalize by (mk)^2, use m>=m0 and tau>tau0. Given n>=2m0 choose k=floor(n/m0)>=2, m=ceil(n/k). Then

~~~
m0 <= m <= 27265,      n <= mk < (1+1/m0)n.
~~~

Delete mk-n points and pad coordinates to dimension 3*27265-1=81794. The resulting diameter is strictly below beta_A*n^2, where

~~~
beta_A
 = [s^3*(1/2+(1037-1/2)/m0)+s^2/(2tau0*m0^2)]*(1+1/m0)^2
 = 19630399020112743707436366691
   /29949319108555308142000000000
 = 0.6554539336590505... < 82/125.
~~~

Deletion preserves distance separation and does not increase diameter. This proves Proposition A, subject to the finite criterion. QED.

## B. Arbitrarily close to the counting bound, with polynomial dimension

**Theorem B.** For every integer r>=10 and every integer n>=160r^5, there is a distance-separated n-point configuration in R^(360r^5-1) of diameter strictly less than

~~~
(1/2+13/(5r^2))*n^2.
~~~

*Proof.* Fix r>=10. Let m0=80r^5 and for all m>=m0 take

~~~
s=1+1/r^2,  a=1/r,  L=4r^2,  C=20r^3,  K=80r^3*m.
~~~

Set t=1/r^2<=1/100. Then the C1 digit product is

~~~
s*lambda = (1+t)(1-t/4)(1-t/8)
         = 1+5t/8-11t^2/32+t^3/32 > 1+t/2.
~~~

The derived tolerance satisfies

~~~
tau = sqrt(1-1/(s*(K+1)))
    >= 1-1/(s*(K+1)) > 1-1/(6400r^8).
~~~

For r>=10, (1-1/(6400r^8))*(1+t/2)>1, proving (C1).

(C2): H_m<=1+log(m)<=2sqrt(m), hence 16384H_m^2<=65536m<=80r^3*m=K since r>=10. Also K>=m.

(C3): K=4Cm>4Cm/s^3 because s>1.

(C4): Since 84s^2<100 and K+m=(80r^3+1)m<=81r^3m,

~~~
(84s^2/a)^2*(K+m) < (100r)^2*(81r^3m)
                    =810000r^5m
                   <=(20r^3m)^2=(Cm)^2.
~~~

The last inequality follows from rm>=2025, automatic for m>=80r^5 and r>=10.

(C5): Ca*gamma=20r^2*(1-1/(8r^2))>16r^2=4L. Thus the criterion applies for all m>=m0 and k>=2, with tau>1/2.

Its diameter bound is strictly less than

~~~
[s^3*(80r^3*m+m^2/2)+s^2]*k^2.
~~~

Given n>=2m0, take k=floor(n/m0) and m=ceil(n/k). Then m0<=m<=120r^5, and n<=mk<(1+1/m0)n. Delete excess points and pad to R^(360r^5-1). With u=1/r, m0=80/u^5, and (80r^3)/m0=u^2, the normalized diameter is strictly below

~~~
beta(u) = ((1+u^2)^3*(1/2+u^2)
          +(1+u^2)^2*u^10/6400)*(1+u^5/80)^2.
~~~

All coefficients of beta(u)-1/2 are nonnegative, and its first nonzero term is of degree 2. Therefore (beta(u)-1/2)/u^2 is nondecreasing for u>=0. The exact rational endpoint comparison from the companion script is

~~~
beta(1/10) = 0.5254536413634017... < 0.526
           = 1/2 + 13/(5*10^2).
~~~

It follows for every u in (0,1/10] that beta(u)<1/2+(13/5)u^2. This proves Theorem B. QED.

**Consequence.** For every epsilon>0, choose any integer r>=10 satisfying 13/(5r^2)<epsilon. Then d=360r^5-1 and N=160r^5 are FINITE and independent of n, and every n>=N has diameter <(1/2+epsilon)n^2. In particular d=O(epsilon^(-5/2)). Writing Delta_d(n) for the infimum of diameters of n-point distance-separated subsets of R^d, the trivial counting bound Delta_d(n)>=n(n-1)/2 gives

~~~
inf_{finite d} limsup_{n->infty} Delta_d(n)/n^2 = 1/2.
~~~

**Important quantifier distinction:** Theorem B does not prove that any *single* fixed d attains 1/2+o(1); d is allowed to depend on epsilon, but never on n after epsilon is chosen.

## Reproduction and next mathematical work

Run with standard Python only:

~~~
python3 research/exact_parameter_certificate.py
~~~

The script verifies Proposition A with exact fractions and verifies the universal polynomial endpoint of Theorem B; a sample of integer r values is checked only for regression. The uniform C1-C5 proofs above, not the sample, establish the quantifiers. Next: generalize the hardcoded Lean construction to parameter inputs, prove these rational gates in Lean, and seek independent specialist scrutiny. Keep the existing certified 0.735 theorem intact until that work passes.
