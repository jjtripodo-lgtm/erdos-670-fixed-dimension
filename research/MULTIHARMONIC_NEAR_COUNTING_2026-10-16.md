# Multiharmonic orthogonal circles: near-quadratic dimension for separated distances

**Discovery note | 2026-10-16 | Erdős 670 | paper-level theorem, not a new Lean endpoint**

This construction modifies the orthogonal-circle proof in [the manuscript](../paper/fixed_dimension_670.tex), reusing its macro-simplex and clustered-ruler lemmas while replacing one circle in each cluster with a sum of orthogonal harmonic circles. Its quantitative dimension dependence improves the existing single-circle certificate's exponent 5/2. The proof is mathematical, not an independently reviewed or Lean-compiled result. No GitHub Actions were run.

## Main theorem

For each integer r >= 16, let q be the smallest integer q >= 2 satisfying

~~~text
(8*q*q)^q >= 16*r,
~~~

and h=ceil(log_2(2q)). For all integers n >= 384*h*q*r^2, there is an n-point distance-separated set in

~~~text
R^d,  d = 288*(2q+1)*h*q*r^2-1
~~~

with diameter strictly below

~~~text
(1/2 + 9/(4*r))*n^2.
~~~

Distance-separated means that the lengths of different unordered non-diagonal edges differ by at least one. Importantly, r (hence d) is chosen first; d is independent of n.

The choice q=O(log r/loglog r), h=O(loglog r) yields

~~~text
d = O(epsilon^(-2) * log(1/epsilon)^2 / loglog(1/epsilon))
~~~

for any desired small coefficient excess epsilon>0, taking r of order epsilon^(-1).

| r | q | h | minimum n | ambient dimension d | upper coefficient |
|--:|--:|--:|--:|--:|--:|
|16|2|2|393216|1474559|0.640625|
|64|2|2|6291456|23592959|0.53515625|
|100|3|3|34560000|181439999|0.5225|
|1000|3|3|3456000000|18143999999|0.50225|

These are paper-level consequences, not changes to the original Lean-certified 0.735 endpoint.

## 1. Fourier-flat digits

For integer q>=1, define for 1<=j<=q

~~~text
b[q,j] = binom(2q,q+j)/binom(2q,q),
c[q,j] = 2*(-1)^(j+1)*b[q,j]/j,
F_q(z) = sum_{j=1}^q c[q,j]*sin(j*z).
~~~

Write alpha_q=2^q/binom(2q,q), which lies in (0,1]. Expanding (1-cos z)^q into its cosine Fourier modes gives the **exact identity**

~~~text
F_q'(z) = 1-alpha_q*(1-cos z)^q.
~~~

In particular, on |z|<=a/2,

~~~text
1-(a^2/8)^q <= F_q'(z) <= 1.
~~~

For q=2, F_2(z)=(4/3)sin(z)-(1/6)sin(2z), and its derivative is 1-(2/3)(1-cos z)^2. This cancels quadratic digit distortion and replaces it with quartic distortion. General q yields distortion of order a^(2q).

The coefficients also obey the **exact amplitude identity**

~~~text
S_q := sum_j |c[q,j]| = H_q = sum_{j=1}^q 1/j.
~~~

Proof: set b[q-1,q]=0. The factorial identity b[q-1,j]=b[q,j]*(1-j^2/q^2) implies

~~~text
S_q-S_(q-1)=(2/q^2)*sum_{j=1}^q j*b[q,j].
~~~

Since j*binom(2q,q+j)=q*(binom(2q-1,q+j-1)-binom(2q-1,q+j)), the sum telescopes to q/2 after division by binom(2q,q). Hence S_q-S_(q-1)=1/q, and S_0=0 proves S_q=H_q. Finally c[q,1]=2q/(q+1)>=1.

## 2. Orthogonal completion simultaneously for all harmonics

Take macro points Q_A and projection matrices F,G from the manuscript's macro lemma. Let theta=a/k and set

~~~text
U_A=(s/theta)*(F_A+s*k*G_A),
R0=C*m*k^2,
R_j^2=|c[q,j]|*H_q*R0^2.
~~~

The macro lemma guarantees ||U||_op <= R0 under

~~~text
Cm >= (84*s^2/a)*sqrt(K+m).
~~~

Let V be the (m-1) by (qm) matrix with columns c[q,j]*U_A and D the diagonal matrix of radii R_j repeated over clusters. For any real vector v indexed by (A,j), weighted Cauchy-Schwarz yields

~~~text
||Vv||^2 <= ||U||_op^2 * sum_A (sum_j c[q,j]*v_(A,j))^2
        <= R0^2 * (sum_j c[q,j]^2/R_j^2)
                 * sum_(A,j) R_j^2*v_(A,j)^2
         = sum_(A,j) R_j^2*v_(A,j)^2.
~~~

The last identity uses sum_j |c[q,j]|=H_q. Thus D^2-V^T V is positive semidefinite. Let W=(D^2-V^T V)^(1/2), and take orthogonal harmonic directions

~~~text
a_(A,j)=(c[q,j]*U_A, W*e_(A,j), 0),
b_(A,j)=(0,0,R_j*e_(A,j)).
~~~

Their norms both equal R_j and every distinct pair of directions is orthogonal. They live in R^(m-1) + R^(qm) + R^(qm), a total of (2q+1)m-1 coordinates. Define

~~~text
eta_A(z)=sum_j[a_(A,j)*sin(jz)+b_(A,j)*cos(jz)].
~~~

Every eta_A has constant norm H_q*R0, and eta_A(z) is orthogonal to eta_B(w) for A!=B.

As in the original construction let S=s^3*k^2, D_AB=K+colex_label(A,B) and choose Q_A with macro squared distances D_AB^2-2rho^2, where rho=H_q*R0/S=H_q*C*m/s^3. The macro lemma applies if

~~~text
K >= max(m,16384*H_m^2),    K >= 4*H_q*C*m/s^3.
~~~

With the original clustered ruler positions t_(A,i), put x_(A,i)=(S*Q_A,0,0)+eta_A(theta*t_(A,i)) and f_(A,i)=F_q(theta*t_(A,i))/theta.

For A<B, expansion of squared distances cancels 2(H_q R0)^2 against the macro shortening. The remaining cross projections are the same coarse and fine digits, now with F_q instead of sin. This gives the **exact** formula

~~~text
||x_(A,i)-x_(B,j)|| = sqrt(nu^2+2*nu*T),
nu=S*D_AB,
T=s^2*k*f_(A,i)+s*f_(B,j).
~~~

No linear approximation to this square root is needed.

## 3. Local chords remain an exact shared ruler function

Inside any single cluster, orthogonality gives the translation-invariant distance function

~~~text
Phi(delta) = 2*sqrt(sum_{j=1}^q R_j^2*sin^2(j*delta/2)).
~~~

For ruler difference g>0, delta=theta*g/(L*p)<a<=1/q. The same function Phi applies in **every** cluster, and all ruler differences g from distinct local edges are distinct positive integers.

For y=j*delta/2 in (0,1/2), y*cot(y)>=cos(y)>=7/8. Setting v_j=2R_j sin(j*delta/2), we have (v_j'/v_j)*delta>=7/8, hence

~~~text
Phi'(delta)>=(7/8)*Phi(delta)/delta.
~~~

Also Phi(delta)>=2R_1 sin(delta/2)>=(23/24)*R_1*delta and R_1>=R0, because c[q,1]>=1 and H_q>=1. Therefore

~~~text
Phi'(delta)>=(161/192)*R0>(4/5)*R0.
~~~

Since p<4mk and theta=a/k, the derivative of the local metric as a function of the integer ruler difference g is strictly larger than C*a/(5L). Thus the guard C*a>5L guarantees all local lengths are at least one and any two distinct local lengths differ by more than one.

The local metric also satisfies, since sin(y)<=y and j<=q,

~~~text
Phi(delta) <= delta*sqrt(sum_j j^2*R_j^2)
            <= delta*q*H_q*R0
            < a*q*H_q*R0 <= H_q*R0.
~~~

The cross lengths, by the original digit-envelope estimate, exceed s^3*K*k^2. If K>=4H_q*C*m/s^3, this is at least 4H_q*R0, giving a strict local-cross gap greater than one.

## 4. Multiharmonic finite criterion

Assume integers m>=4, k>=2, q>=1, L>=3 and real s>1, 0<a<=1/q, C,K>0. Put

~~~text
kappa=1-1/L,
gamma=1-(a^2/8)^q,
lambda=kappa*gamma,
tau=sqrt(1-1/[s*(K+1)]).
~~~

Five sufficient conditions are

~~~text
(H1) tau*s*lambda > 1,
(H2) K >= max(m,16384*H_m^2),
(H3) K >= 4*H_q*C*m/s^3,
(H4) Cm >= (84*s^2/a)*sqrt(K+m),
(H5) Ca > 5L.
~~~

**Finite criterion conclusion:** the multiharmonic geometry supplies mk points in R^((2q+1)m-1), with distinct unordered edge lengths separated by at least one, minimum pair distance at least one, and diameter at most

~~~text
[s^3*(K+m*(m-1)/2)+s^2/(2*tau)]*k^2.
~~~

Proof: Sections 1–3 give the points, exact local lengths, their separation, and the exact cross-length expression. The new digit derivative is in [gamma,1], so the manuscript's clustered-ruler digit bounds hold with lambda replacing its earlier kappa*(1-a^2/8). H1 implies s*kappa>=s*lambda>1/tau; consequently the manuscript's fine-step, carry-step, and macro-step comparisons apply unchanged to the exact increasing map T->sqrt(nu^2+2nu*T). In particular 2*T_max<s^2*k^2, every consecutive cross length increases by more than one, and the cross-length displacement from its baseline is at most T_max/tau. H3 separates cross from local lengths using Section 3. The same displacement bound proves the stated diameter. No unbounded Taylor error is discarded.

## 5. Uniform choice of parameters

For each r>=16 let q be the least integer satisfying (8q^2)^q>=16r, put h=ceil(log_2(2q)), and set

~~~text
m0=192*h*q*r^2,  s=1+1/r,  a=1/q,
L=4*r,           C=24*q*r,  B=96*h*q*r,  K=B*m
~~~

for every integer m>=m0.

Because H_q<=1+log_2 q<=h, H3 holds (B>=4H_q*C, s>1). H5 is 24r>20r.

For H4, s<=17/16 implies 84s^2<100. Also B+1<=97hqr. The squared radius guard follows from

~~~text
C^2*m0 = 110592*h*q^3*r^4
       > 970000*h*q^3*r
       > (84*s^2/a)^2*(B+1).
~~~

For H2, H_m^2/m is nonincreasing for m>=4 (because H_m>=2). The dyadic bound H_8192<14 implies H_m^2<=m/32 whenever m>=8192. Here m0>=196608 and B>=6144>512, so K=Bm>=16384*H_m^2 and K>=m.

To check H1, write u=1/r<=1/16. By the choice of q,

~~~text
gamma=1-(1/(8q^2))^q >=1-u/16.
~~~

Since K>=B*m0=18432*h^2*q^2*r^3>r^3, we have tau>1-u^3. Therefore

~~~text
tau*s*lambda>(1-u^3)*(1+u)*(1-u/4)*(1-u/16)>1.
~~~

The final inequality holds for 0<u<=1/16: (1+u)(1-u/4)>=1+47u/64; the other two factors multiply to at least 1-17u/256; their product exceeds one.

Consequently H1–H5 hold for **every** integer m>=m0 and k>=2.

Given any integer n>=2m0, set k=floor(n/m0), m=ceil(n/k). Then m0<=m<=3m0/2, n<=mk<(1+1/m0)n. Delete the surplus points and pad with zero coordinates to dimension (2q+1)*3m0/2-1=288(2q+1)hqr^2-1. Separation is preserved and diameter cannot increase.

Since tau>1/2, the normalized bound (even before deletion) is strictly below

~~~text
s^3*(1/2+B/m0)+s^2/m0^2.
~~~

Using B/m0=1/(2r) and m0>=192r^2, a universal rational polynomial upper bound for the final coefficient is, with u=1/r,

~~~text
beta(u)=[(1+u)^3*(1/2+u/2)+(1+u)^2*u^4/192^2]
        *(1+u^2/192)^2.
~~~

Every nonconstant coefficient of beta is nonnegative, so (beta(u)-1/2)/u increases with u>=0. At u=1/16 the exact positive gap is

~~~text
[1/2+(9/4)*(1/16)]-beta(1/16)
=5056939392489651935/1494186269970473680896 > 0.
~~~

This proves the claimed diameter coefficient for all integers r>=16.

## 6. Growth of harmonic order

Let v=ceil(log_2 r)>=4 and w=floor(log_2 v)>=2. The candidate q0=ceil(v/w) suffices: for integer w>=2, 8*2^(w/2)>=w^2 (check 2,...,6, then induct by w->w+2). Since q0>=2^w/w, we obtain 8q0^2>=2^(3w/2), hence

~~~text
(8q0^2)^q0 >=2^(3v/2).
~~~

For v>=8, the right side is >=2^(v+4)>=16r. The cases v=4,5,6,7 satisfy (8q0^2)^q0>=16*2^v directly. The minimal admissible q therefore obeys q<=q0=O(log r/loglog r), and h=O(loglog r). Substitution into the explicit dimension formula gives the asserted near-quadratic tradeoff.

## Scope and reproduction

Run [multiharmonic_near_counting_certificate.py](multiharmonic_near_counting_certificate.py) using standard Python. It checks exact polynomial identities for q=1,...,24, the amplitude identity, exact rational parameter margins at selected integer r, and the universal coefficient polynomial. The **general** conclusion rests on the mathematical proof above, not a finite test list.

The existing Lean files and originally published theorem have not been modified. Neither independent kernel verification nor specialist review is claimed for the new multiharmonic theorem. Further work: formalize the new completion lemma and local-chord monotonicity; investigate whether wider arcs or non-colex macro geometry can reduce the remaining logarithmic overhead.
