# Smoothed triangular-wave harmonic construction: O(epsilon^-2 log(1/epsilon)) dimension

**Erdős 670 discovery note | 16 October 2026 | paper-level construction**

This extends the [original orthogonal-circle finite criterion](../paper/fixed_dimension_670.tex) and improves the earlier [multiharmonic construction](MULTIHARMONIC_NEAR_COUNTING_2026-10-16.md). It replaces maximally-flat Fourier weights of growing total amplitude with a smoothed triangular wave whose Fourier coefficient absolute sum stays below 2, while obtaining exponentially small slope distortion on a fixed angular arc.

**Status:** Mathematical derivation, with locally run independent rational and numerical checks. This is not included in the hardcoded Lean endpoint and has not received independent specialist review. No GitHub Actions were used.

## Theorem (paper-level, conditional on the macro/ruler lemmas of the manuscript)

For every integer r >= 16, put

- v = ceil(log_2(16r)), D = 7v, and J = ceil(D/2);
- N = 12288 r^2 and d = 9216 (2J+1) r^2 - 1.

For every integer n >= N there is a distance-separated n-point subset X of R^d satisfying

    diam X < (1/2 + 9/(4r)) n^2.

In particular, for every epsilon>0 one may choose a sufficiently large integer r depending only on epsilon, obtaining a single fixed Euclidean dimension

    d = O(epsilon^(-2) log(1/epsilon))

and a threshold N = O(epsilon^(-2)) such that the diameter is below (1/2+epsilon)n^2 for all n>=N. Here the dimension depends on epsilon, *not* on n.

This improves the exponent-5/2 single-circle method and the previous O(epsilon^-2 log^2(1/epsilon)/loglog(1/epsilon)) multiharmonic family. It does not contradict the earlier lower bound, which applies only to the original five-condition certificate.

## 1. Smoothed triangular-wave digits

Let T(z)=arcsin(sin z), interpreted as a continuous 2pi-periodic odd function. It equals z on [-pi/2,pi/2], has derivative sign(cos z) almost everywhere, and has Fourier series

    T(z) = (4/pi) sum_{j>=1, j odd} (-1)^((j-1)/2) sin(jz)/j^2.

The coefficients follow directly by integrating the sine Fourier coefficient separately on [0,pi/2] and [pi/2,pi]. For integer D>=4 define the positive, normalized trigonometric kernel

    K_D(z) = [4^D/binom(2D,D)] cos^(2D)(z/2)/(2pi),

    b_D(j) = binom(2D,D+j)/binom(2D,D), 0<=j<=D.

The Fourier multipliers of K_D are b_D(|j|) for |j|<=D and zero above D. The convolution F_D=K_D*T is therefore the *finite* sine polynomial

    F_D(z)=sum_{1<=j<=D, j odd} c_j sin(jz),
    c_j=(4/pi)(-1)^((j-1)/2) b_D(j)/j^2.

Write A=sum_j |c_j|. The elementary inequality

    sum_{ell>=1}1/(2ell+1)^2
       <sum_{ell>=1}1/[4ell(ell+1)]=1/4

implies A < 5/pi < 2. Also c_1=(4/pi)D/(D+1)>1 when D>=4. Thus 1<A<2 independent of D.

### A uniform derivative guarantee

For every |z|<=1/2, if |t|<=1 then |z-t|<=3/2<pi/2, hence T'(z-t)=1. Since T' takes only the values +/-1 almost everywhere and K_D is a probability density,

    1 >= F_D'(z) >= 1-2 Pr_KD(|t|>1).

The elementary bound cos^2(1/2)<4/5 and the central-binomial estimate
4^D/binom(2D,D)<=2D+1 give

    Pr_KD(|t|>1) < (2D+1)(4/5)^D.

Let v=ceil(log_2(16r))>=8, D=7v. Since (4/5)^7<1/4, and
2(14v+1)<=2^v for every integer v>=8 (base v=8, then induction),

    2(2D+1)(4/5)^D < 2^(-v) <= 1/(16r).

Consequently

    1-1/(16r) < F_D'(z) <= 1     for |z|<=1/2.

Compared with the previous Fourier-flat family, the digit distortion is exponentially small in D while the coefficient amplitude A stays below 2.

## 2. A new positive local-chord derivative lemma

The main obstruction to using a fixed angular width is that individual high harmonics oscillate. Their *sum*, however, has a strictly positive derivative.

Consider the square wave V(z)=sign(sin z), with Fourier sine series

    V(z)=(4/pi) sum_{j>=1, j odd} sin(jz)/j.

Define U_D=K_D*V, so

    U_D(delta) = sum_j j |c_j| sin(j delta).

For 0<delta<pi the convolution equals

    U_D(delta)=2 integral_(delta-pi)^delta K_D(t)dt - 1.

Hence U_D(0)=0, and

    U_D'(delta)=2[K_D(delta)-K_D(pi-delta)] > 0
                                for 0<delta<pi/2.

Let Z_D=4^D/binom(2D,D). The Wallis product recurrence
Z_D/Z_(D-1)=2D/(2D-1) shows inductively that Z_D>=sqrt(D+1):
indeed (2D/(2D-1))^2 >= (D+1)/D.

For 0<=delta<=D^(-1/2),

    cos^(2D)(delta/2) >= (1-delta^2/4)^D >= 3/4,
    sin^(2D)(delta/2) <= (1/(4D))^D <= 1/4.

It follows that

    U_D'(delta) >= Z_D/(2pi) > sqrt(D)/8.

Since U_D increases up to pi/2, we have throughout 0<delta<=1 the uniform lower bound

    U_D(delta) >= (1/8) min(sqrt(D)*delta,1).

Now let R0>0 and assign an orthogonal circle radius R_j by

    R_j^2=|c_j| A R0^2.

The squared length of the multi-circle chord of angle difference delta is

    Phi(delta)^2=4 sum_j R_j^2 sin^2(j delta/2),

so direct differentiation yields the **exact identity**

    Phi'(delta) = A R0^2 U_D(delta)/Phi(delta).

As |sin x|<=|x| and sin^2 x<=1, we have

    Phi(delta) <= delta R0 sqrt(A E),
    Phi(delta) <= 2A R0,
    E=sum_j j^2|c_j|=(4/pi)sum_{odd j<=D}b_D(j)<=D

(the last bound holds for D>=2 because pi>3).

If 0<delta<=D^(-1/2), combine the first upper estimate with
U_D(delta)>=sqrt(D)*delta/8 to obtain

    Phi'(delta)>=R0 sqrt(A)/8 >=R0/8.

If D^(-1/2)<=delta<=1, combine the second upper estimate with
U_D(delta)>=1/8 to obtain

    Phi'(delta)>=R0/16.

Therefore, **uniformly in the harmonic degree D**,

    Phi'(delta)>=R0/16             (0<delta<=1).

This is the crucial new local-separation lemma. It does not require the
small-angle condition delta<=1/D used by the previous multiharmonic proof.

## 3. Orthogonal completion and exact cross distances

Reuse the macro simplex and its entire matrices F,G from the manuscript.
For cluster size k, take theta=a/k, a=1, scale S=s^3 k^2, and

    U_A=(s/theta)(F_A+sk G_A),       R0=C m k^2.

The manuscript's projection estimate yields ||U||_op<=R0 under

    Cm >= (84s^2/a) sqrt(K+m).                        (H4)

There are J=ceil(D/2) odd frequencies. Form the matrix with columns
c_j U_A. Weighted Cauchy-Schwarz, with radii R_j^2=|c_j| A R0^2,
gives for every vector z indexed by frequency and cluster

    ||V z||^2 <= R0^2 sum_A (sum_j c_j z_Aj)^2
              <= sum_Aj R_j^2 z_Aj^2.

Thus diag(R_j^2)-V^T V is positive semidefinite. Taking its PSD square
root completes all frequency directions into mutually orthogonal pairs.
The points lie in dimension

    (m-1)+Jm+Jm=(2J+1)m-1.

Let eta_A(z) be the sum of the resulting orthogonal circle vectors
at frequencies j. Because sum_j R_j^2=A^2 R0^2,

    ||eta_A(z)||=A R0,
    <eta_A(z),eta_B(w)>=0 when A!=B.

Choose macro squared distances shortened by 2rho^2, where rho=A R0/S.
The manuscript's macro lemma applies if

    K >= max(m,16384 H_m^2),                          (H2)
    K >= 4A C m/s^3.                                 (H3)

With the same clustered Sidon ruler as the manuscript, define
z_Ai=theta*t_Ai and x_Ai=S Q_A+eta_A(z_Ai).

For A<B, all cross terms cancel except the designed projections. The
cross length is **exactly**

    ||x_Ai-x_Bj|| = sqrt(nu^2+2nu T),
    nu=S (K+colex_label(A,B)),
    T=s^2 k f_Ai+s f_Bj,
    f_Ai=F_D(z_Ai)/theta.

By Section 1, the digits satisfy the manuscript's bounds with
kappa=1-1/L and lambda=kappa*(1-1/(16r)).

Inside one cluster every distance is Phi(delta) for ruler angle
difference delta=theta*g/(L*prime), 0<delta<a=1, with g a distinct
positive integer across all local edges. Since prime<4mk and
Phi'(delta)>=R0/16, differentiation with respect to g gives

    d Phi/dg > C a/(64 L).

Thus the guard

    C a > 64 L                                      (H5)

gives unit separation of every local length and minimum local distance
at least one.

The local length is at most 2A R0. Under (H3) the cross lengths exceed
s^3 K k^2 >=4A R0, so every cross length exceeds every local length by
more than one. The original fine/carry/macro comparisons for the *exact*
square-root cross map apply unchanged under

    tau*s*kappa*(1-1/(16r))>1,                       (H1)
    tau=sqrt(1-1/[s(K+1)]).

Therefore the point set is distance-separated and satisfies

    diam X <= [s^3(K+m(m-1)/2)+s^2/(2tau)] k^2.

No Taylor approximation to the square-root cross map is made.

## 4. Explicit uniform parameter family

For any integer r>=16, and every integer m>=m0, set

    m0=6144 r^2,      s=1+1/r,    a=1,
    L=4r,             C=320r,    B=2560r,
    K=B m,            D=7ceil(log_2(16r)), J=ceil(D/2).

The five guards hold for **all** m>=m0 and k>=2:

- H1: write u=1/r<=1/16. Since K>r^3, tau>1-u^3.
  Also (1+u)(1-u/4)>=1+47u/64 and
  (1-u^3)(1-u/16)>=1-17u/256. Their product is
  1+(171/256)u-(799/16384)u^2>1.
- H2: H_8192<14 by dyadic blocks, hence H_8192^2<8192/32.
  For all m>=4, H_m>=2 and
  (H_(m+1)/H_m)^2 <= (1+1/[2(m+1)])^2 <=1+1/m;
  therefore H_m^2/m is nonincreasing. Since m0>=8192,
  16384 H_m^2<=512m<=K. Also K>=m.
- H3: A<2, B=8C, and s>1, so Bm>4ACm/s^3.
- H4: s<=17/16 implies 84s^2<100, and for m>=m0,
  C^2 m >= C^2 m0 =629145600 r^4
  > 10000(2560r+1) > (84s^2/a)^2(B+1).
- H5: C a=320r>256r=64L.

Let n>=2m0 and k=floor(n/m0)>=2, m=ceil(n/k). Then
m0<=m<=3m0/2=9216r^2 and n<=mk<(1+1/m0)n.
Delete surplus points and pad coordinates up to
d=9216(2J+1)r^2-1.

Since tau>1/2 and B/m0=5/(12r), the normalized diameter
is strictly below beta(1/r), where

    beta(u) = [(1+u)^3(1/2+5u/12)
              +(1+u)^2*u^4/6144^2]
              *(1+u^2/6144)^2.

Every coefficient of beta(u)-1/2 is nonnegative; consequently
[beta(u)-1/2]/u increases for u>=0. At u=1/16 the exact rational
inequality is

    [1/2+9/(4*16)]-beta(1/16)
       =15129869248902868251967199
        /1566767862220559410419204096 >0.

Thus beta(1/r)<1/2+9/(4r) for every r>=16. This proves the theorem,
conditional on the original macro/ruler lemmas and on the mathematical
arguments of this note.

Illustrative parameter choices:

| r | frequency degree D | harmonic circles J | minimum n | dimension d | coefficient cap |
|--:|--:|--:|--:|--:|--:|
| 16 | 56 | 28 | 3,145,728 | 134,479,871 | 0.640625 |
| 64 | 70 | 35 | 50,331,648 | 2,680,160,255 | 0.53515625 |
| 100 | 77 | 39 | 122,880,000 | 7,280,639,999 | 0.5225 |

Since D=7ceil(log_2(16r)) and J=ceil(D/2), the dimension is
O(r^2 log r), while the minimum n is O(r^2). Taking r proportional to
epsilon^(-1) proves the asserted tradeoff.

## Evidence and next steps

The companion [exact-rational certificate](triangular_wave_near_counting_certificate.py)
checks the universal coefficient polynomial, the conservative kernel-tail
bounds and finite parameter inequalities for representative r. It also
runs numerical regression checks on F_D' and Phi'. These checks are not
a substitute for the *uniform proofs* above.

Next research seams: seek frequency kernels with smaller constants;
investigate whether an alternative finite-mode approximation can reduce
the residual O(log(1/epsilon)) factor; parameterize and formalize the
orthogonal completion and positive local-chord lemma in Lean. Preserve
the previously recorded 0.735 Lean result until these claims have been
separately formalized and reviewed.
