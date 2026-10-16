#!/usr/bin/env python3
"""Exact-rational audit of the global-chord multiharmonic Erdős 670 claim.

The universal sine-sum lower bound is proved in the accompanying research
note. This program checks the Fourier identities and harmonic moments in
finitely many degrees, symbolic coefficient positivity, and sample parameter
margins, without GitHub Actions or a Lean build.
"""
from fractions import Fraction as Q
from math import comb


def add(a, b):
    out = [Q(0)] * max(len(a), len(b))
    for i, v in enumerate(a):
        out[i] += v
    for i, v in enumerate(b):
        out[i] += v
    return out


def mul(a, b):
    out = [Q(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return out


def power(a, n):
    out = [Q(1)]
    for _ in range(n):
        out = mul(out, a)
    return out


def evaluate(a, x):
    return sum((v*x**i for i, v in enumerate(a)), Q(0))


def harmonics(q):
    b = [Q(comb(2*q, q+j), comb(2*q, q)) for j in range(1, q+1)]
    c = [Q(2*(-1)**(j+1), j)*b[j-1] for j in range(1, q+1)]
    H = sum((Q(1, j) for j in range(1, q+1)), Q(0))
    assert sum(map(abs, c), Q(0)) == H
    assert sum((j*j*abs(c[j-1]) for j in range(1, q+1)), Q(0)) == q
    assert sum((j*b[j-1] for j in range(1, q+1)), Q(0)) == Q(q, 2)
    assert c[0] == Q(2*q, q+1)
    return b, c, H


def check_fourier(q):
    # Check the derivative as a polynomial in x=cos(t).
    b, c, H = harmonics(q)
    T0, T1 = [Q(1)], [Q(0), Q(1)]
    derivative = [Q(0)]
    for j in range(1, q+1):
        derivative = add(derivative, [j*c[j-1]*v for v in T1])
        T0, T1 = T1, add(mul([Q(0), Q(2)], T1), [-v for v in T0])
    rhs = add([Q(1)], [
        -Q(2**q, comb(2*q,q))*v
        for v in power([Q(1), Q(-1)], q)
    ])
    assert derivative == rhs, q

    # Check the binomial sine recurrence
    # B_(q+1)=((q+1)/(2q+1))[(1+cos t)B_q+sin t].
    if q > 1:
        bp, _, _ = harmonics(q-1)
        for j in range(1, q+1):
            middle = bp[j-1] if j <= q-1 else Q(0)
            left = Q(1) if j == 1 else bp[j-2]
            right = bp[j] if j+1 <= q-1 else Q(0)
            expected = Q(q, 2*q-1)*(middle+(left+right)/2)
            assert b[j-1] == expected, (q, j)
    return H


def check_coefficient():
    # beta(u)=[(1+u)^4/2+(1+u)^2*u^4/232^2]*(1+u^2/232)^2.
    lead = [v/2 for v in power([Q(1), Q(1)], 4)]
    extra = mul(power([Q(1), Q(1)], 2),
                [Q(0)]*4 + [Q(1, 232**2)])
    beta = mul(add(lead, extra), power([Q(1),Q(0),Q(1,232)], 2))
    assert beta[0] == Q(1,2) and all(v >= 0 for v in beta[1:])
    at16 = evaluate(beta, Q(1,16))
    gap = Q(1,2) + Q(11,5*16) - at16
    assert gap > 0
    # Uniform H1 lower bound:
    # [(1+u)(1-7u/8)]*[(1-u^3)(1-u/16)]
    # >= [1+9u/128]*[1-17u/256]
    # >= 1+(1895/524288)*u, 0<u<=1/16.
    assert Q(1,256) - Q(153,32768*16) == Q(1895,524288)
    print("Universal beta endpoint:", at16, "=", float(at16))
    print("Exact positive gap:", gap)
    return beta


def check_family(r, beta):
    assert r >= 16
    q = 2
    while 8**q < 16*r:
        q += 1
    h = (2*q-1).bit_length()  # ceil(log_2(2q))
    Hq = check_fourier(q)
    assert Hq <= h
    u = Q(1,r)
    s = 1+u
    L = (8*r+6)//7  # ceil(8r/7)
    C = 29*r
    B = 116*h*r
    m0 = 232*h*r*r
    gamma = 1-Q(1,8)**q
    kappa = 1-Q(1,L)
    tau_low = 1-Q(1)/(s*(B*m0+1))
    margins = {
        "G1 fine-digit guard": tau_low*s*kappa*gamma-1,
        "G2 harmonic macro bound": Q(B-512),
        "G3 radius shortening": B*s**3-4*Hq*C,
        "G4 squared completion": Q(C*C*m0)-(84*s*s)**2*(B+1),
        "G5 global local-chord": Q(C-24*L)
    }
    for name, margin in margins.items():
        assert margin > 0, (r, q, name, margin)
    bound = (
        s**3*(Q(1,2)+Q(B,m0))
        +s*s/(2*tau_low*m0*m0)
    )*(1+Q(1,m0))**2
    target = Q(1,2)+Q(11,5*r)
    assert bound < evaluate(beta,u) < target
    d = 348*(2*q+1)*h*r*r-1
    print(f"r={r:>6d} q={q} h={h} n_min={2*m0} d={d} "
          f"computed_bound={float(bound):.12f} cap={float(target):.12f}")


if __name__ == "__main__":
    for q in range(1,41):
        check_fourier(q)
    print("PASS: Fourier identity, binomial recurrence, harmonic moments q=1..40")
    beta = check_coefficient()
    for r in [16,17,31,32,33,64,100,256,1000,4096,65536]:
        check_family(r, beta)
    print("PASS: exact rational sample checks; uniform proof in research note")
