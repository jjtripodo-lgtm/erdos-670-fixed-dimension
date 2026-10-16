# Global chord monotonicity for orthogonal harmonics: a sharper dimension tradeoff

**Research note, 16 October 2026 | Erdős 670 | discovery, not a new Lean-certified theorem**

This continues [the multiharmonic construction](MULTIHARMONIC_NEAR_COUNTING_2026-10-16.md). Its previous local-chord argument imposed the angular-width restriction a <= 1/q because it required **every individual harmonic chord** to increase. That restriction is unnecessary: the **sum of the squared chords** is increasing, even where some individual harmonics are decreasing. An exact recurrence for binomial sine sums proves a uniform positive derivative for every harmonic order q.

The resulting paper-level construction improves the earlier bound

    d = O(epsilon^-2 * log(1/epsilon)^2 / loglog(1/epsilon))

to

    d = O(epsilon^-2 * log(1/epsilon) * loglog(1/epsilon)).

Both are conditional on the original manuscript's macro-simplex and ruler lemmas; the new construction is not covered by the existing hardcoded Lean endpoint. No GitHub Actions were used.

## 1. Main theorem

For every integer r >= 16 let q be the smallest integer q >= 2 with 8^q >= 16r, and set h=ceil(log_2(2q)). Every integer n >= 464*h*r^2 admits a distance-separated n-point set in R^d, where

    d=348*(2q+1)*h*r^2-1,

with

    diam(X) < (1/2 + 11/(5r))*n^2.

The configuration is injective, its distinct-point distances are >=1, and any two different unordered non-diagonal edges have lengths differing by >=1. The dimension depends on r but NOT on n. In particular, choosing r > 11/(5epsilon) gives d=O(epsilon^-2 log(1/epsilon) loglog(1/epsilon)) as epsilon tends to zero.

Examples (paper-level, not Lean-checked):

| r | q | h | n threshold | ambient d | coefficient cap |
|---:|---:|---:|---:|---:|---:|
| 16 | 3 | 3 | 356352 | 1870847 | 0.6375 |
| 64 | 4 | 3 | 5701632 | 38486015 | 0.534375 |
| 100 | 4 | 3 | 13920000 | 93959999 | 0.522 |
| 1000 | 5 | 4 | 1856000000 | 15311999999 | 0.5022 |

## 2. Exact positivity recurrence for the sine transform

Retain the harmonic coefficients of the earlier note:

    b_(q,j) = binom(2q,q+j)/binom(2q,q),      1<=j<=q,
    c_(q,j) = 2*(-1)^(j+1)*b_(q,j)/j,
    H_q = sum_(j=1)^q 1/j.

Write b_(q,0)=1, b_(q,j)=0 for j>q, and define the conjugate sine polynomial

    B_q(t) = 2*sum_(j=1)^q b_(q,j)*sin(jt),    B_0(t)=0,
    T_q(t) = B_q(t)/2.

The cosine polynomial

    A_q(t)=1+2*sum_(j=1)^q b_(q,j)*cos(jt)
          =(2+2*cos(t))^q/binom(2q,q)

obeys A_(q+1)=[(q+1)/(2q+1)]*(1+cos t)*A_q. Comparing the Fourier coefficients (or multiplying and using the sine addition law) gives the **exact recurrence**

    B_(q+1)(t)=[(q+1)/(2q+1)]*
               [(1+cos t)*B_q(t)+sin t].

For 0<t<=1 we have sin t>0, 1+cos t>0. Set v=(1+cos t)/2, so 0<v<1. Since (q+1)/(2q+1)>1/2, induction gives

    B_q(t) >= (sin t)/2 * sum_(j=0)^(q-1) v^j.

Writing e=1-v=sin^2(t/2), Bernoulli's inequality implies v^q=(1-e)^q<=1/(1+q*e), whence

    sum_(j=0)^(q-1) v^j >= q/(1+q*e)
                         >= q/(1+q*t^2/4).

Since sin t>=5t/6 on [0,1], we obtain the uniform, **strictly positive** lower bound

    T_q(t) >= [5*q*t]/[24*(1+q*t^2/4)]   (0<t<=1).

This also proves global local-chord monotonicity: positivity applies for every q, without requiring all j*t to lie in (0,1).

Two exact harmonic-weight identities will be used:

    sum_j |c_(q,j)| = H_q,
    sum_j j^2*|c_(q,j)| = q.

The second follows from sum_(j=1)^q j*b_(q,j)=q/2, itself an immediate telescoping consequence of

    j*binom(2q,q+j)
      =q*[binom(2q-1,q+j-1)-binom(2q-1,q+j)].

## 3. A uniform lower bound on local chord derivatives

Use the orthogonal-completion radii from the earlier multiharmonic note,

    R0=C*m*k^2,    R_j^2=|c_(q,j)|*H_q*R0^2.

For a single cluster the shared local chord metric, as a function of the angular difference t, is

    Phi_q(t)=2*sqrt(sum_j R_j^2*sin^2(j*t/2)).

Direct differentiation and the definition of T_q give

    Phi_q'(t)=2*H_q*R0^2*T_q(t)/Phi_q(t)   (t>0).

There are two independent upper bounds:

    Phi_q(t) <= R0*t*sqrt(q*H_q),
    Phi_q(t) <= 2*H_q*R0.

For 0<t<=1/sqrt(q), the recurrence bound gives T_q(t)>=q*t/6, hence

    Phi_q'(t) >= R0*sqrt(q*H_q)/3 >= R0/3.

For 1/sqrt(q)<=t<=1, we have q*t>=1 and t<=1, so
1+q*t^2/4 <= 5*q*t/4. The recurrence bound gives T_q(t)>=1/6, hence

    Phi_q'(t) >= R0/6.

Therefore the key **global chord-slope lemma** is

    Phi_q'(t) >= R0/6   for every q>=1 and 0<t<=1.

In the clustered quadratic-residue ruler, the angular difference for an integer ruler difference g is t=(a/k)*g/(L*p), and 0<t<a<=1. The prime obeys p<4mk. Hence

    d(Phi_q(t(g)))/dg
       >= (R0/6)*(a/(k*L*p))
       > C*a/(24L).

Thus the single sufficient local-separation guard

    (G5) C*a > 24L

replaces the old guard C*a>5L together with a<=1/q. The new constant is more conservative, but crucially it is **independent of the harmonic order q**. Different positive integer ruler gaps therefore produce lengths separated by >1, and the shortest local length is >1.

Furthermore Phi_q(t)<=2H_q R0, independent of q. The macro-offset condition K>=4H_q*C*m/s^3 gives cross lengths >s^3*K*k^2>=4H_q R0, so local and cross lengths cannot collide.

## 4. Improved multiharmonic finite criterion

Assume m>=4, k>=2, q>=1, L>=3 integers, s>1, 0<a<=1, C,K>0. Put

    kappa=1-1/L, gamma=1-(a^2/8)^q,
    lambda=kappa*gamma, tau=sqrt(1-1/[s*(K+1)]).

The following five inequalities suffice:

    (G1) tau*s*lambda > 1,
    (G2) K >= max(m,16384*H_m^2),
    (G3) K >= 4*H_q*C*m/s^3,
    (G4) C*m >= (84*s^2/a)*sqrt(K+m),
    (G5) C*a > 24L.

The conclusion is a separated mk-point configuration in R^((2q+1)m-1) with diameter at most

    [s^3*(K+m*(m-1)/2)+s^2/(2*tau)]*k^2.

Proof: the Fourier-flat digit formula F_q'(z)=1-alpha_q*(1-cos z)^q and
|z|<=a/2 imply the digit step bound lambda. The orthogonal completion in
the preceding note provides actual points with an exact cross-length
formula sqrt(nu^2+2nu*T); G2-G4 are unchanged, and the earlier
fine/carry/macro cross-gap comparisons follow from G1. Section 3 proves
all local and mixed edge gaps using G3 and G5. The same exact cross
envelope gives the diameter bound. No truncated Taylor approximation
is used.

## 5. Uniform parameter family

For each integer r>=16, choose q,h as in Section 1. For all m>=m0 use

    m0=232*h*r^2,
    s=1+1/r,   a=1,
    L=ceil(8r/7), C=29r,
    B=116*h*r, K=B*m.

For G5, L<8r/7+1, giving 29r-24L>(11/7)r-24>0 for r>=16.

For G3, H_q<=h, and B=4hC, so B>=4H_q C/s^3.

For G4, s<=17/16 implies 84s^2<100. Since K+m=(B+1)m, it suffices at m0 to compare

    C^2*m0 =195112*h*r^4
    > 1170000*h*r
    > (84*s^2)^2*(B+1).

For G2, H_8192<14 by dyadic grouping, and H_m^2/m is nonincreasing for m>=4; hence H_m^2<=m/32 for m>=8192. Since m0>=178176 and B>=5568>512, K>=16384*H_m^2 and K>=m.

For G1, let u=1/r<=1/16. The choice 8^q>=16r yields gamma>=1-u/16. Also kappa>=1-7u/8 and K=B*m>=B*m0>r^3 gives tau>1-u^3. Thus

    tau*s*lambda >
      (1-u^3)*(1+u)*(1-7u/8)*(1-u/16).

For 0<u<=1/16,

    (1+u)*(1-7u/8) >= 1+9u/128,
    (1-u^3)*(1-u/16) >= 1-17u/256,

whose product is >=1+u*(1/256-153u/32768)
               >=1+1895u/524288 > 1.
All five guards hold for **every** m>=m0, not merely sampled instances.

Given n>=2m0, take k=floor(n/m0), m=ceil(n/k). Then
m0<=m<=3m0/2 and n<=mk<(1+1/m0)n. Deleting excess points and
zero-padding coordinates yields d=(2q+1)*3m0/2-1.

Writing u=1/r, bounding tau>1/2 and m0>=232r^2 gives the universal normalized diameter polynomial

    beta(u)= [ (1+u)^4/2 +(1+u)^2*u^4/232^2 ]*(1+u^2/232)^2.

It has nonnegative nonconstant coefficients. The exact-rational checker confirms

    beta(1/16)
      =2029794867959681577249/3185310448046231781376
      =0.637236119074...
      <1/2+11/(5*16)=0.6375.

Therefore (beta(u)-1/2)/u is nondecreasing in u>=0 and
beta(u)<1/2+11*u/5 for all 0<u<=1/16. This proves Section 1's bound.

Finally q<=max(2,ceil(log_8(16r)))=O(log r), and h=ceil(log_2(2q))=O(loglog r). Thus d=O(r^2 log r loglog r), giving the advertised epsilon statement.

## 6. Evidence, scope, and next seam

- [Exact-rational and polynomial certificate](multiharmonic_global_chord_certificate.py): Fourier identities, sine-recurrence coefficients and harmonic moments for q=1,...,40; exact parameter checks at multiple r; universal rational coefficient comparison.
- [Small Euclidean reconstruction](multiharmonic_numerical_reconstruction.py): independent m=4,k=3,q=3, 27-dimensional Gram-deficit completion; checks all local/cross length identities and the >1 separation gaps numerically. This is a numerical sanity check, **not** a universal proof or independently authenticated Lean certificate.
- The original Lean 0.735 endpoint is unchanged, and the new theorem has not undergone independent specialist review.

The next opportunity is to improve the coarse uniform chord-slope constant R0/6 (the numerical data suggest it is very conservative), or to reduce the harmonic radius/amplitude cost H_q without sacrificing the exact mixed-distance cancellation. Claims of general lower bounds beyond the explicitly stated certificate remain out of scope.
