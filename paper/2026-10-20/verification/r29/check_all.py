"""Exact rational certificate for the prime-controlled noncolex dimension29 endpoint. No assert needed."""
from fractions import Fraction as F
from pathlib import Path
import json,hashlib
r=Path(__file__).parent
m=6;K=F(457,25);H=F(569,500);eta=F(533,500);sigma=F(138,125);a=F(519,1000);b=F(879,500);r0=F(507,100);r1=F(1131,100);k0=100;t=F(971,1000);C=F(101,100)
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def sha(x):return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(',',':')).encode()).hexdigest()
LABELS=[[0, 3, 5, 7, 14, 15], [3, 0, 2, 4, 13, 12], [5, 2, 0, 1, 11, 10], [7, 4, 1, 0, 9, 8], [14, 13, 11, 9, 0, 6], [15, 12, 10, 8, 6, 0]]
require(sorted(LABELS[i][j]for j in range(1,m)for i in range(j))==list(range(1,m*(m-1)//2+1)),'label permutation')
D=[[F(0)if i==j else K+H*LABELS[i][j] for j in range(m)]for i in range(m)]
rho2=r0*r0+r1*r1
E=[[D[i][j]**2-2*rho2 if i!=j else F(0) for j in range(m)]for i in range(m)]
B=[[(E[0][i]+E[0][j]-E[i][j])/2 for j in range(1,m)]for i in range(1,m)]
P=[[D[i][j] if i<j else F(0) for j in range(m)]for i in range(m)]
TG=[[P[i][0]-P[i][j] for i in range(m)]for j in range(1,m)]
TF=[[(D[i][0]-P[i][0])-(D[i][j]-P[i][j]) for i in range(m)]for j in range(1,m)]
def ldl(A):
 A=[z[:] for z in A];piv=[]
 for k in range(len(A)):
  p=A[k][k];require(p>0,'nonpositive pivot '+str(k));piv.append(p)
  for i in range(k+1,len(A)):
   for j in range(i,len(A)):
    A[j][i]-=A[i][k]*A[j][k]/p;A[i][j]=A[j][i]
 return piv
matrices={'macro':B}
for name,x in [('completion_infinity',F(0)),('completion_k0',F(1,k0))]:
 T=[[sigma*TG[i][j]+eta*x*TF[i][j]for j in range(m)]for i in range(m-1)]
 matrices[name]=[[B[i][j]-(1/(a*r0))**2*sum(T[i][h]*T[j][h] for h in range(m)) for j in range(m-1)]for i in range(m-1)]
rows=[]
for name,A in matrices.items():
 piv=ldl(A);rows.append(dict(name=name,positive_pivots=len(piv),pivots_sha256=sha(list(map(str,piv))),matrix_sha256=sha([[str(v)for v in row]for row in A]),minimum_pivot=str(min(piv))))
# Alternating Taylor enclosures at b/2 in(0,1); sine concavity handles the full arc.
z=b/2
sinlo=z-z**3/6
sinhi=sinlo+z**5/120
coslo=1-z*z/2+z**4/24-z**6/720
gamma=1-a*a/8
checks={
 'tau_valid':1-sigma/(K+H)-t*t,
 'fine_gap':t*eta*gamma-1,
 'carry_leading':sigma*gamma-eta,
 'carry_constant':t*eta-1,
 'macro_leading':H-sigma/t,
 'macro_linear':(sigma-eta)/t,
 'macro_constant':eta/t-1,
 'local_derivative_squared':(r1*b*coslo/(2*C*m))**2/(1+(r0*a/(r1*sinlo))**2)-1,
 'minimum_local_at_k0':r1*sinlo*k0-1,
 'local_upper_18':F(18)**2-((r0*a)**2+(2*r1*sinhi)**2),
 'cross_lower_18':(K+H)*t-F(37,2),
 'mixed_gap_at_k0':F(k0*k0,2)-1,
 'diameter_subsequence':F(499,500)-(K+H*F(m*(m-1),2)+sigma/(2*t))/m**2,
 'diameter_covers_local':K+H*F(m*(m-1),2)+sigma/(2*t)-18,
 'padding_at_n_10000':F(999,1000)-F(499,500)*(1+F(5,10000))**2,
}
for name,v in checks.items():require(v>0,name)
require(sigma>=eta,'T range bound')
# Negative scalar control: removing ruler radius fails local derivative.
bad_r=F(1)
bad=(bad_r*b*coslo/(2*C*m))**2/(1+(r0*a/(bad_r*sinlo))**2)-1
require(bad<0,'negative control was not rejected')
result=dict(status='PASS_EXACT_SCOPED',parameters={x:str(globals()[x])for x in ['m','K','H','eta','sigma','a','b','r0','r1','k0','t','C']},matrix_rows=rows,scalar_positive_margins={k:str(v)for k,v in checks.items()},negative_controls={'ruler_radius_one_rejected':True},scope='Universal written argument plus exact finite rational macro and scalar obligations; no Lean or specialist review')
print(json.dumps(result,sort_keys=True,indent=2))
(r/'EXACT_RECEIPT.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
(r/'MATRICES.json').write_text(json.dumps({name:[[str(x)for x in row]for row in A]for name,A in matrices.items()},sort_keys=True,indent=2)+'\n')
