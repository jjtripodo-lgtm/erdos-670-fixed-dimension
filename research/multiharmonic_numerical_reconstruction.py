#!/usr/bin/env python3
"""Numerical stress test of explicit orthogonal multiharmonic Euclidean points.

Checks all 66 pair lengths for m=4,k=3,q=3 by building the actual
macro Gram matrix, incidence projections and PSD defect completion.
This is a floating-point sanity check, NOT a general proof or Lean audit.
Requires numpy. No GitHub Actions.
"""
import math
from itertools import combinations
from math import comb
import numpy as np


def run(m=4, k=3, q=3, L=19, p=29, K=1500000, C=40000, r=16):
    assert 2*m*k < p < 4*m*k
    s, theta = 1+1/r, 1/k
    S = s**3*k*k
    R0 = C*m*k*k
    Hq = sum(1/j for j in range(1,q+1))
    rho = Hq*R0/S
    assert K >= 4*rho
    D = np.zeros((m,m))
    for B in range(1,m):
        for A in range(B):
            D[A,B] = D[B,A] = K+B*(B-1)//2+A+1
    squared = D**2-2*rho**2
    np.fill_diagonal(squared,0)
    gram = np.array([[(squared[0,i]+squared[0,j]-squared[i,j])/2
                      for j in range(1,m)] for i in range(1,m)])
    assert np.linalg.eigvalsh(gram).min()>0
    macro = np.column_stack([np.zeros(m-1), np.linalg.cholesky(gram).T])
    F,G = np.zeros((m-1,m)),np.zeros((m-1,m))
    for A in range(m):
        Js = [j for j in range(m) if j!=A]
        directions = np.vstack([macro[:,A]-macro[:,J] for J in Js])
        F[:,A] = np.linalg.solve(directions, [D[A,J] if J<A else 0 for J in Js])
        G[:,A] = np.linalg.solve(directions, [D[A,J] if J>A else 0 for J in Js])
    U=(s/theta)*(F+s*k*G)
    assert np.linalg.norm(U,2)<=R0
    c=[2*(-1)**(j+1)*comb(2*q,q+j)/(j*comb(2*q,q)) for j in range(1,q+1)]
    radii=np.array([R0*math.sqrt(abs(cj)*Hq) for A in range(m) for cj in c])
    V=np.column_stack([c[j]*U[:,A] for A in range(m) for j in range(q)])
    deficit=np.diag(radii**2)-V.T@V
    eig,ev=np.linalg.eigh(deficit)
    assert eig.min()>-1e-5*radii.min()**2
    W=(ev*np.sqrt(np.maximum(eig,0)))@ev.T
    assert np.linalg.norm(V.T@V+W.T@W-np.diag(radii**2))/np.linalg.norm(np.diag(radii**2))<1e-10
    dims=(2*q+1)*m-1
    offset,second=m-1,m-1+q*m
    points,angles,digits={},{},{}
    h=(k-(1-1/L))/2
    for A in range(m):
        for i in range(k):
            y=L*p*i+(i*i+2*k*A*i)%p
            z=theta*(y/(L*p)-h)
            angles[A,i]=z
            digits[A,i]=sum(c[j-1]*math.sin(j*z) for j in range(1,q+1))/theta
            x=np.zeros(dims)
            x[:m-1]=S*macro[:,A]
            for jj,cj in enumerate(c):
                idx=A*q+jj
                x[:m-1]+=cj*U[:,A]*math.sin((jj+1)*z)
                x[offset:second]+=W[:,idx]*math.sin((jj+1)*z)
                x[second+idx]+=radii[idx]*math.cos((jj+1)*z)
            points[A,i]=x
    lengths,local,cross,errors=[],[],[],[]
    for (A,i),(B,j) in combinations(points,2):
        distance=np.linalg.norm(points[A,i]-points[B,j])
        lengths.append(distance)
        if A==B:
            delta=angles[A,i]-angles[A,j]
            expected=2*math.sqrt(sum(radii[A*q+v]**2*math.sin((v+1)*delta/2)**2
                                     for v in range(q)))
            local.append(distance)
        else:
            if A>B:
                A,B=B,A
                i,j=j,i
            nu=S*D[A,B]
            T=s*s*k*digits[A,i]+s*digits[B,j]
            expected=math.sqrt(nu**2+2*nu*T)
            cross.append(distance)
        errors.append(abs(distance-expected))
    minimum_gap=min(b-a for a,b in zip(sorted(lengths),sorted(lengths)[1:]))
    print("dimension",dims,"edges",len(lengths),"max formula error",max(errors))
    print("minimum pair length",min(lengths),"minimum edge gap",minimum_gap)
    print("maximum local",max(local),"minimum cross",min(cross))
    assert max(errors)<1e-5
    assert min(lengths)>1 and minimum_gap>1


if __name__=="__main__":
    run()
