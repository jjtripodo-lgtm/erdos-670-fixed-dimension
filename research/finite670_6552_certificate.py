#!/usr/bin/env python3
"""Exact rational checks for improved finite-criterion witness (no Lean replay)."""
from fractions import Fraction as Q
m0,L,C,B=18177,28,303,1031
s,a,t=Q(1055725,1000000),Q(3763,10000),Q(999999,1000000)
gamma=1-a*a/8
lam=(1-Q(1,L))*gamma
margins={
 "tau lower bound":1-t*t-1/(s*(B*m0+1)),
 "C1":t*s*lam-1,
 "C2 at base":B*m0-16384*16**2,
 "C3":B*s**3-4*C,
 "C4 squared":C*C*m0-(84*s*s/a)**2*(B+1),
 "C5":C*a*gamma-4*L,
}
for name,margin in margins.items():
    assert margin>0,(name,margin)
    print(name,margin)
beta=(s**3*(Q(1,2)+(Q(B)-Q(1,2))/m0)+s*s/(2*t*m0*m0))*(1+Q(1,m0))**2
assert beta<Q(819,1250)
print("padded coefficient",beta,float(beta))
print("target margin",Q(819,1250)-beta)
print("PASS: exact rational witness, not a Lean proof")
