#!/usr/bin/env python3
"""Exact rational checks for a sharper finite Erdős 670 parameter witness."""
from fractions import Fraction as Q

m0, L, C, B = 18177, 28, 305, 1038
s, a, t = Q(2639,2500), Q(3,8), Q(999999,1000000)
gamma = 1-a*a/8
lam = (1-Q(1,L))*gamma
checks = {
    'tau > rational bound': 1-t*t-1/(s*(B*m0+1)),
    'C1': t*s*lam-1,
    'C2 base harmonic': B*m0-16384*16**2,
    'C3': B*s**3-4*C,
    'C4 squared': C*C*m0-(84*s*s/a)**2*(B+1),
    'C5': C*a*gamma-4*L,
}
for name, margin in checks.items():
    assert margin > 0, (name,margin)
    print(name, margin)
beta=(s**3*(Q(1,2)+(Q(B)-Q(1,2))/m0)+s*s/(2*t*m0*m0))*(1+Q(1,m0))**2
assert beta < Q(3277,5000)
print('padded beta',beta,float(beta))
print('target margin',Q(3277,5000)-beta)
print('PASS: exact-rational witness; does not replay Lean')
