"""Exact reconstruction of the three matrices in the dimension-29 proof."""
from fractions import Fraction as F
import json

K, H, eta, sigma = F(457,25), F(569,500), F(533,500), F(138,125)
a, b, r0, r1 = F(519,1000), F(879,500), F(507,100), F(1131,100)
t, C, m = F(971,1000), F(101,100), 6
labels = [[0,3,5,7,14,15], [3,0,2,4,13,12], [5,2,0,1,11,10],
          [7,4,1,0,9,8], [14,13,11,9,0,6], [15,12,10,8,6,0]]
D = [[K+H*labels[i][j] if i != j else F(0)
      for j in range(m)] for i in range(m)]
E = [[D[i][j]**2-2*(r0*r0+r1*r1) if i != j else F(0)
      for j in range(m)] for i in range(m)]
B = [[(E[0][i]+E[0][j]-E[i][j])/2 for j in range(1,m)]
     for i in range(1,m)]
PG = [[D[i][j] if i<j else F(0) for j in range(m)]
      for i in range(m)]
PF = [[D[i][j]-PG[i][j] for j in range(m)] for i in range(m)]
TG = [[PG[A][0]-PG[A][j] for A in range(m)] for j in range(1,m)]
TF = [[PF[A][0]-PF[A][j] for A in range(m)] for j in range(1,m)]

def pivots(matrix):
    R = [row[:] for row in matrix]
    result = []
    for k in range(len(R)):
        p = R[k][k]
        if p <= 0:
            raise ValueError("nonpositive pivot")
        result.append(p)
        for i in range(k+1,len(R)):
            for j in range(i,len(R)):
                R[j][i] -= R[i][k]*R[j][k]/p
                R[i][j] = R[j][i]
    return result

matrices = {"B": B}
for name,x in [("M(0)",F(0)), ("M(1/100)",F(1,100))]:
    T = [[sigma*TG[i][j]+eta*x*TF[i][j] for j in range(m)]
         for i in range(m-1)]
    matrices[name] = [[B[i][j]-sum(T[i][h]*T[j][h] for h in range(m))/(a*r0)**2
                      for j in range(m-1)] for i in range(m-1)]

def simple_lower_bound(v):
    q = F(1)
    while q >= v:
        q /= 2
    return q

rows = {name: {"pivots": list(map(str,pivots(A))),
               "lower_bounds": list(map(str,map(simple_lower_bound,pivots(A))))}
        for name,A in matrices.items()}
z, gamma = b/2, 1-a*a/8
sinlo, sinhi = z-z**3/6, z-z**3/6+z**5/120
coslo = 1-z*z/2+z**4/24-z**6/720
margins = [1-sigma/(K+H)-t*t, t*eta*gamma-1,
           sigma*gamma-eta, t*eta-1, H-sigma/t,
           (sigma-eta)/t, eta/t-1,
           (r1*b*coslo/(2*C*m))**2/(1+(r0*a/(r1*sinlo))**2)-1,
           r1*sinlo*100-1,
           F(18)**2-((r0*a)**2+(2*r1*sinhi)**2),
           (K+H)*t-F(37,2),
           F(499,500)-(K+15*H+sigma/(2*t))/36]
if any(v <= 0 for v in margins):
    raise ValueError("nonpositive scalar margin")
if sorted(labels[i][j] for i in range(m) for j in range(i+1,m)) != list(range(1,16)):
    raise ValueError("wrong macro labels")
print(json.dumps({"status":"PASS", "matrices":rows,
                  "positive_scalar_margins":list(map(str,margins))},indent=2))
