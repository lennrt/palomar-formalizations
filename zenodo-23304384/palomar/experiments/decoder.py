#!/usr/bin/env python3
"""Exact two-batch decoder for lossy distance-shell tomography.

Python 3.9+; standard library only. Import recover_two_batches and call
    recover_two_batches(first, second, n, h, p)
with two iterables of n-entry integer report vectors, the leg-length bound n,
the per-vertex count bound h, and p as fractions.Fraction in (0, 1). The result
is a sorted pair of population tuples. Only aggregate reports are used.

Auxiliary storage is O(n) scalar values; integer bit lengths can grow with the
round count. The probability guarantee requires independent rounds and batches
with the budgets and assumptions stated in the paper. This module does not
choose a sample budget. See check_streaming.py for exact reconstruction checks.
"""
from fractions import Fraction as F
from math import comb, isqrt


def landing(i,k,p):
    return comb(i-1,k-1)*p**k*(1-p)**(i-k) if 1<=k<=i else F(0)


def joint(i,j,k,l,p):
    if i==j: return landing(i,k,p) if k==l else F(0)
    if i>j: return joint(j,i,l,k,p)
    return landing(i,k,p)*comb(j-i-1,l-k-1)*p**(l-k)*(1-p)**(j-i-l+k) if 1<=l-k<=j-i else F(0)


def covariance_entry(u,k,l,p):
    """One entry, computed on demand; no covariance matrix is stored."""
    n=len(u)
    mk=sum(u[i-1]*landing(i,k,p) for i in range(1,n+1))
    ml=sum(u[i-1]*landing(i,l,p) for i in range(1,n+1))
    return sum(u[i-1]*u[j-1]*joint(i,j,k,l,p) for i in range(1,n+1) for j in range(1,n+1))-mk*ml


def nearest(x):
    return (2*x.numerator+x.denominator)//(2*x.denominator)


def _checked(rounds,n,h):
    for r in rounds:
        r=tuple(r)
        if len(r)!=n or any(not isinstance(x,int) or not 0<=x<=2*h for x in r):
            raise ValueError('Each round must have n integer entries in [0,2h].')
        yield r


def recover_two_batches(first,second,n,h,p):
    """Return unordered words. Invalid decoded candidates use the zero-pair fallback.

    Input errors raise ValueError. The second iterator is not consumed when the
    first phase concludes a=b or an invalid candidate; this can save rounds.
    Auxiliary storage contains O(n) scalar values; integer bit lengths grow with
    the number of observed rounds. Runtime uses direct polynomial finite sums.
    """
    p=F(p)
    if n<1 or h<1 or not 0<p<1: raise ValueError('Require n,h>=1 and 0<p<1.')
    fallback=((0,)*n,(0,)*n)
    S=[0]*n; T=[0]*n; N=0
    for r in _checked(first,n,h):
        N+=1
        for k in range(n): S[k]+=r[k]; T[k]+=r[k]**2
    if N==0: raise ValueError('The first batch is empty.')
    mu=[F(x,N) for x in S]; c=[0]*n
    for k in reversed(range(n)):
        c[k]=nearest((mu[k]-sum(c[i]*landing(i+1,k+1,p) for i in range(k+1,n)))/p**(k+1))
    if any(not 0<=x<=2*h for x in c): return fallback
    m=None; top=None
    for k in range(n):
        phi=2*(F(T[k],N)-mu[k]**2)-covariance_entry(c,k+1,k+1,p)
        if phi>p**n*(1-p**(k+1))/2: m,top=k,phi
    d=[0]*n
    if m is not None:
        square=nearest(top/(p**(m+1)*(1-p**(m+1))))
        if square<=0: return fallback
        d[m]=isqrt(square)
        if d[m]**2!=square: return fallback
        S=[0]*(m+1); T=[0]*(m+1); N=0
        for r in _checked(second,n,h):
            N+=1
            for k in range(m+1): S[k]+=r[k]; T[k]+=r[k]*r[m]
        if N==0: raise ValueError('A nontrivial first phase requires a nonempty second batch.')
        for k in reversed(range(m)):
            cov=F(T[k],N)-F(S[k]*S[m],N*N)
            phi=2*cov-covariance_entry(c,k+1,m+1,p)
            d[k]=nearest((phi/(d[m]*p**(m+1))+sum(d[i]*landing(i+1,k+1,p) for i in range(k+1,m+1)))/(1-p**(k+1)))
    if any((x+y)%2 or (x-y)%2 for x,y in zip(c,d)): return fallback
    a=tuple((x+y)//2 for x,y in zip(c,d)); b=tuple((x-y)//2 for x,y in zip(c,d))
    if any(not 0<=x<=h for x in a+b): return fallback
    return tuple(sorted([a,b]))
