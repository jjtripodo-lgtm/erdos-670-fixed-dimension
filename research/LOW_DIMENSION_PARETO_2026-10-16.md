# Erdős 670: a low-dimensional Pareto frontier from orthogonal circles

**Research note, 16 October 2026.** Mathematical discovery only; no GitHub Actions.

## Scope

These are new **paper-level corollaries** of the existing five-condition finite criterion in Section 5 of [the manuscript](../paper/fixed_dimension_670.tex). They are not new Lean-checked theorems. The unchanged Lean endpoint formalizes an older parameter choice; the independent specialist-review question remains open. The exact rational parameter checks are in [low_dimension_pareto_certificate.py](low_dimension_pareto_certificate.py), executed locally without CI.

## New fixed-dimensional bounds

Each row labeled **all n** yields a distance-separated n-point configuration in one fixed space R^d for **every** integer n >= n0, with diameter strictly less than c*n². Different unordered non-diagonal edges have lengths differing by at least one.

| Availability | Dimension d | n0 | Diameter coefficient c | Calculated rational upper bound (decimal display) |
| --- | ---: | ---: | ---: | ---: |
| n=1934k, every integer k>=2 | **5801** | 3868 on this subsequence | **1** | 0.999883902415 |
| All n | **8723** | **3878** | **1** | 0.999867017787 |
| All n | **8999** | **4000** | **197/200 = 0.985** | 0.984130313755 |
| All n | **9899** | **4400** | **47/50 = 0.940** | 0.939887782022 |
| All n | **35999** | **16000** | **361/500 = 0.722** | 0.720961004886 |
| All n | **46079** | **20480** | **699/1000 = 0.699** | 0.698471833230 |

The first row is an asymptotic counterexample in **R^5801**: infinitely many n, rather than every sufficiently large n, suffice to obtain liminf(Delta_5801(n)/n²) < 1. No least-dimension claim is made.

The 35,999-dimensional row improves all three numerical parameters (dimension, n threshold, diameter coefficient) relative to the older Lean-certified R^81794, n>=36354, coefficient 0.735 result. **This improvement is not itself Lean-certified.**

## Exact witness parameters

Every row uses a rational lower bound tau0=999999/1000000 for the derived tau=sqrt(1-1/[s(K+1)]). The script tests the strict inequality tau>tau0 at the smallest applicable m.

| Availability | m0 | L | s | a | C | K |
| --- | ---: | ---: | --- | --- | --- | --- |
| n=1934k only | 1934 | 19 | 1081495/1000000 | 219/500 | 889/5 | 1087364 |
| All n | 1939 | 19 | 108175/100000 | 4401/10000 | 177 | 561m |
| All n | 2000 | 19 | 108311/100000 | 451/1000 | 173 | 548m |
| All n | 2200 | 18 | 108677/100000 | 907/2000 | 163 | 510m |
| All n | 8000 | 20 | 107827/100000 | 109/250 | 188 | 600m |
| All n | 10240 | 23 | 2139/2000 | 53/125 | 222 | 726m |

## Proof: the criterion and all-parameter extension

For m>=4, integer L>=3, s>1, 0<a<=1, and positive C,K, define
gamma=1-a²/8, lambda=(1-1/L)*gamma and H_m=sum_(j=1)^m 1/j.
The manuscript's finite criterion assumes:

~~~
C1: tau*s*lambda > 1
C2: K >= max(m,16384*H_m^2)
C3: K >= 4*C*m/s^3
C4: C*m >= (84*s^2/a)*sqrt(K+m)
C5: C*a*gamma > 4*L.
~~~

Its conclusion, for **every k>=2**, is a distance-separated mk-point configuration in R^(3m-1) with diameter at most

~~~
[s^3*(K+m(m-1)/2)+s^2/(2*tau)]*k^2.
~~~

The accompanying Python program checks **every** rational inequality at the displayed base point, computing H_m as a finite exact rational sum. C4 is checked by squaring its positive sides.

### The fixed-m row

Take m=1934, K=1087364, and the first row's s,a,L,C. All five conditions hold with positive exact margins, and tau>tau0. For n=1934k, every integer k>=2, the finite criterion supplies points in R^(3*1934-1)=R^5801 with normalized diameter strictly below the rational quantity

~~~
[s^3*(K+1934*1933/2)+s^2/(2*tau0)]/1934^2
  = approximately 0.999883902415 < 1.
~~~

This proves the infinite-subsequence result, assuming the manuscript's finite criterion.

### Uniform m>=m0 for the five all-n rows

For any all-n row hold s,a,L,C,B fixed and choose K=Bm for **each** m>=m0. We now prove that the base conditions imply the conditions at every larger m.

* For C1, K increases with m, so the derived tau increases. Its strict lower bound tau0 at m0 continues to hold.
* For C2, H_m>=2 for m>=4 and
  (H_(m+1)/H_m)^2 = (1+1/[(m+1)H_m])^2
  <= (1+1/[2(m+1)])^2 < (m+1)/m.
  Therefore H_m²/m decreases as m increases. The exact base inequality B*m0 >= 16384*H_m0² implies B*m >= 16384*H_m² for every m>=m0. Also B>=1 gives K>=m.
* For C3, the base check B*s³ >= 4*C is independent of m.
* For C4, squaring positive sides and substituting K=Bm reduces the claim to C²*m >= (84*s²/a)²*(B+1), which becomes easier as m increases.
* C5 is independent of m.

Thus every all-n witness meets C1-C5 for all integer m>=m0.

### From mk points to arbitrary n

Fix n>=2m0. Set k=floor(n/m0)>=2 and m=ceil(n/k). Writing n=m0*k+b with 0<=b<m0 gives

~~~
m0 <= m <= m0+ceil((m0-1)/2)
n <= mk < (1+1/m0)*n.
~~~

The finite criterion supplies mk points. Delete any mk-n points and pad to

~~~
d = 3*(m0+ceil((m0-1)/2))-1
~~~

coordinates. Neither deletion nor zero padding spoils distance separation or increases diameter. Since m>=m0 and tau>tau0, the normalized diameter is strictly below

~~~
beta =
 [s^3*(1/2+(B-1/2)/m0)+s^2/(2*tau0*m0^2)]
 *(1+1/m0)^2.
~~~

For each all-n row, the script proves this **exact rational beta** is strictly smaller than its listed c. The claim follows.

## Research significance and limits

The original campaign concentrated on the diameter coefficient. The same construction contains a useful dimension/threshold/diameter **Pareto frontier**, including a sub-6000-dimensional asymptotic counterexample and an all-n counterexample under 9000 dimensions.

This does not lower the universal lower bound near 1/2, prove global dimension optimality, or establish any new independent geometric mechanism. The low-dimensional cases make the macro harmonic requirement C2 relatively tight; improving that macro input is a promising structural next step.

**Reproduction (standard library, no CI):**

~~~
python3 research/low_dimension_pareto_certificate.py
~~~

The original theorem statement, manuscript, pinned Lean proof and published verification records are unchanged.
