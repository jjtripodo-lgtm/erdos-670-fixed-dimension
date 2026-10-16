#!/usr/bin/env python3
"""Exact-rational discovery checks for harmonic-separated-distance construction.

This is a reproducible algebra and inequality certificate, not a Lean proof,
not a verification of the macro lemma, and not a GitHub Actions workflow.
The accompanying research note supplies the uniform mathematical proof.
"""
from fractions import Fraction as Q
from math import comb


def plus(p, q):
    out = [Q(0)] * max(len(p), len(q))
    for i, v in enumerate(p):
        out[i] += v
    for i, v in enumerate(q):
        out[i] += v
    return out


def scale(p, c):
    return [c * v for v in p]


def mul(p, q):
    out = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            out[i+j] += a*b
    return out


def power(p, n):
    out = [Q(1)]
    for _ in range(n):
        out = mul(out, p)
    return out


def evaluate(p, u):
    return sum((v*u**i for i, v in enumerate(p)), Q(0))


def trim(p):
    while len(p)>1 and not p[-1]:
        p.pop()
    return p


def coefficients(q):
    return [Q(2*(-1)**(j+1)*comb(2*q, q+j), j*comb(2*q,q))
            for j in range(1, q+1)]


def verify_fourier_identity(q):
    """As polynomials in x=cos z: f'_q(z)=1-alpha*(1-x)^q."""
    cs=coefficients(q)
    T0, T1 = [Q(1)], [Q(0), Q(1)]
    lhs=[Q(0)]
    for j,c in enumerate(cs,1):
        lhs=plus(lhs,scale(T1,j*c))
        T0,T1 = T1, plus(mul([Q(0),Q(2)],T1),scale(T0,-1))
    alpha=Q(2**q,comb(2*q,q))
    rhs=plus([Q(1)],scale(power([Q(1),Q(-1)],q),-alpha))
    Hq=sum((Q(1,j) for j in range(1,q+1)),Q(0))
    assert trim(lhs)==trim(rhs), ("Fourier identity",q)
    assert sum(map(abs,cs),Q(0))==Hq, ("amplitude identity",q)
    assert cs[0]==Q(2*q,q+1)
    assert Q(0)<alpha<=1
    return Hq


def universal_coefficient_bound():
    # u=1/r, and m0 >= 192*r*r. This is an upper bound, not equality.
    leading = mul(power([Q(1),Q(1)],3),[Q(1,2),Q(1,2)])
    overhead = mul(power([Q(1),Q(1)],2),[Q(0)]*4+[Q(1,192**2)])
    beta=mul(plus(leading,overhead),power([Q(1),Q(0),Q(1,192)],2))
    assert beta[0]==Q(1,2) and all(c>=0 for c in beta[1:])
    # Hence (beta(u)-1/2)/u is increasing for u>=0.
    end=evaluate(beta,Q(1,16))
    gap=Q(1,2)+Q(9,4*16)-end
    assert gap>0
    print("POLYNOMIAL: exact universal endpoint PASS")
    print("  beta_upper(1/16) =",end,"=",float(end))
    print("  target gap =",gap)
    return beta


def check_family(r,beta):
    assert r>=16
    # Smallest harmonic order sufficient for gamma >= 1-1/(16*r).
    # The note proves q=O(log(r)/loglog(r)), uniformly for r >= 16.
    q=2
    while (8*q*q)**q < 16*r:
        q+=1
    h=(2*q-1).bit_length()         # ceil(log_2(2q))
    Hq=verify_fourier_identity(q)
    assert Hq<=h
    m0=192*h*q*r*r
    mmax=3*m0//2
    L=4*r
    a=Q(1,q)
    s=1+Q(1,r)
    C=24*q*r
    B=96*h*q*r
    K=B*m0
    kappa=1-Q(1,L)
    gamma=1-(a*a/8)**q
    tau_lower=1-Q(1)/(s*(K+1))
    gates={
        "H1 conservative lower":tau_lower*s*kappa*gamma-1,
        "H2 harmonic via H_m^2 <= m/32":Q(B-512),
        "H3 radius/shortening":B*s**3-4*Hq*C,
        "H4 squared completion":Q(C*C*m0)-(84*s*s/a)**2*(B+1),
        "H5 chord derivative":Q(C)*a-5*L,
    }
    for name, margin in gates.items():
        assert margin>0, (r,q,name,margin)
    coefficient=(s**3*(Q(1,2)+Q(B,m0)) +s*s/(2*tau_lower*m0*m0))*(1+Q(1,m0))**2
    target=Q(1,2)+Q(9,4*r)
    assert coefficient<target, (r,coefficient,target)
    u=Q(1,r)
    assert coefficient<evaluate(beta,u)<target
    d=(2*q+1)*mmax-1
    print(f"r={r:>7d} q={q:<3d} h={h:<3d} n_min={2*m0:<19d} d={d:<23d}",
          f"coefficient={float(coefficient):.12f} cap={float(target):.12f}")
    return gates


if __name__ == "__main__":
    print("FOURIER: exact polynomial identities and S_q=H_q")
    for q in range(1,25):
        verify_fourier_identity(q)
    print("  PASS for q=1..24 (uniform identities proved in research note)")
    beta=universal_coefficient_bound()
    for r in [16,17,31,32,33,64,100,256,1000,4096,65536]:
        check_family(r,beta)
    print("PASS: sampled integer families + symbolic polynomial checks")
    print("Scope: paper-level general construction; no new Lean compilation")
