#!/usr/bin/env python3
"""Finite exact checks of the paper's variance and reconstruction identities.

Run from the supplemental-materials directory:
    python3 scripts/check_sampling.py
Python 3.9+; standard library only. Do not use -O: verification uses assertions.
The script prints a JSON summary to stdout and writes no result files.

Checks fixed finite cases of closed-form moments, the prefix-survival support
identity, variance bounds, the testing-overlap formula, and reconstruction under
bounded perturbations. Integer stress cases use a fixed random seed. The dense
reference decoder here is used only for verification; decoder.py implements the
two-batch decoder with O(n) scalar accumulators. This is a regression check of
proved statements, not a search for conjectures or a sampling-performance study.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, isqrt
from collections import defaultdict
import json, random


def landing(i, k, p):
    return comb(i-1,k-1)*p**k*(1-p)**(i-k) if 1<=k<=i else F(0)


def joint(i,j,k,l,p):
    if i==j: return landing(i,k,p) if k==l else F(0)
    if i>j: return joint(j,i,l,k,p)
    return landing(i,k,p)*comb(j-i-1,l-k-1)*p**(l-k)*(1-p)**(j-i-l+k) if 1<=l-k<=j-i else F(0)


def covariance(u,p):
    n=len(u)
    mu=[sum(u[i-1]*landing(i,k,p) for i in range(1,n+1)) for k in range(1,n+1)]
    return [[sum(u[i-1]*u[j-1]*joint(i,j,k,l,p) for i in range(1,n+1) for j in range(1,n+1))-mu[k-1]*mu[l-1] for l in range(1,n+1)] for k in range(1,n+1)]


def law(u,p):
    n=len(u); ans=defaultdict(F)
    for bits in product([0,1],repeat=n):
        r=tuple([x for x,b in zip(u,bits) if b]+[0]*(n-sum(bits)))
        ans[r]+=p**sum(bits)*(1-p)**(n-sum(bits))
    return dict(ans)


def pair_law(a,b,p):
    ans=defaultdict(F)
    for x,px in law(a,p).items():
        for y,py in law(b,p).items():
            ans[tuple(xx+yy for xx,yy in zip(x,y))]+=px*py
    return dict(ans)


def stats(dist):
    n=len(next(iter(dist)))
    mu=[sum(v*r[k] for r,v in dist.items()) for k in range(n)]
    C=[[sum(v*(r[k]-mu[k])*(r[l]-mu[l]) for r,v in dist.items()) for l in range(n)] for k in range(n)]
    return mu,C


def nearest(x):
    return (2*x.numerator+x.denominator)//(2*x.denominator)


def decode(mu,C,p,h):
    """Polynomial arithmetic decoder; exact rational p and statistics."""
    n=len(mu); c=[0]*n; d=[0]*n
    for k in reversed(range(n)):
        c[k]=nearest((mu[k]-sum(c[i]*landing(i+1,k+1,p) for i in range(k+1,n)))/p**(k+1))
    qc=covariance(c,p)
    phi=[[2*C[k][l]-qc[k][l] for l in range(n)] for k in range(n)]
    active=[k for k in range(n) if phi[k][k]>p**n*(1-p**(k+1))/2]
    if active:
        m=max(active)
        square=nearest(phi[m][m]/(p**(m+1)*(1-p**(m+1))))
        if square<=0: return None
        d[m]=isqrt(square)
        if d[m]**2!=square: return None
        for k in reversed(range(m)):
            d[k]=nearest((phi[k][m]/(d[m]*p**(m+1))+sum(d[i]*landing(i+1,k+1,p) for i in range(k+1,m+1)))/(1-p**(k+1)))
    if any((x+y)%2 or (x-y)%2 for x,y in zip(c,d)): return None
    a=tuple((x+y)//2 for x,y in zip(c,d)); b=tuple((x-y)//2 for x,y in zip(c,d))
    if any(x<0 or x>h for x in a+b): return None
    return tuple(sorted([a,b]))


def check_case(a,b,p,rng):
    n=len(a); h=max(1,*a,*b); D=2*h; dist=pair_law(a,b,p)
    mu,C=stats(dist); c=[x+y for x,y in zip(a,b)]
    assert sum(dist.values())==1
    assert decode(mu,C,p,h)==tuple(sorted([tuple(a),tuple(b)]))
    qa,qb=covariance(a,p),covariance(b,p)
    assert C==[[qa[k][l]+qb[k][l] for l in range(n)] for k in range(n)]
    for k in range(n):
        s=1-p**(k+1)
        assert C[k][k] <= 2*D**2*s
        # Direct support event: every mask with both prefixes alive fixes hop k.
        for aa in product([0,1],repeat=n-k-1):
            for bb in product([0,1],repeat=n-k-1):
                ta=[x for x,z in zip(a,(1,)*(k+1)+aa) if z]
                tb=[x for x,z in zip(b,(1,)*(k+1)+bb) if z]
                assert ta[k]+tb[k]==c[k]
        for l in range(n):
            ez2=sum(v*((r[k]-mu[k])*(r[l]-mu[l]))**2 for r,v in dist.items())
            assert ez2-C[k][l]**2<=2*D**4*(1-p**(min(k,l)+1))
    # Arbitrary bounded perturbations in the proved good event. These need not
    # be realizable empirical samples; correctness is asserted on a larger box.
    alpha=[p**n*(1-p**(k+1))/5 for k in range(n)]
    for trial in range(16):
        e=[rng.choice([-1,0,1])*x for x in alpha]
        E=[[F(0)]*n for _ in range(n)]
        for k in range(n):
            for l in range(k,n): E[k][l]=E[l][k]=rng.choice([-1,0,1])*alpha[min(k,l)]
        ch=[[C[k][l]+E[k][l]-e[k]*e[l] for l in range(n)] for k in range(n)]
        assert decode([x+y for x,y in zip(mu,e)],ch,p,h)==tuple(sorted([tuple(a),tuple(b)]))
    return len(dist)


def main():
    rng=random.Random(20261011); cases=[]
    # Exhaust all unordered binary pairs through length 3, at boundary-near
    # and ordinary probabilities; random integer cases reach length 5.
    for n in range(1,4):
        words=list(product(range(2),repeat=n))
        for i,a in enumerate(words):
            for b in words[i:]:
                for p in [F(1,5),F(1,2),F(2*n,2*n+1)]:
                    cases.append((a,b,p))
    for _ in range(30):
        n=rng.randint(1,5)
        a=tuple(rng.randrange(4) for _ in range(n)); b=tuple(rng.randrange(4) for _ in range(n))
        cases.append((a,b,rng.choice([F(1,10),F(2,3),F(9,10),F(2*n,2*n+1)])))
    supports=[check_case(a,b,p,rng) for a,b,p in cases]
    lower=[]
    for p in [F(1,10),F(1,3),F(1,2),F(4,5),F(20,21)]:
        q=1-p; A=pair_law((1,1),(0,0),p); B=pair_law((1,0),(0,1),p)
        overlap=sum(min(A.get(x,0),B.get(x,0)) for x in A.keys()|B.keys())
        assert overlap==1-2*p*p*q
        assert overlap>=p*p
        lower.append({'p':str(p),'overlap':str(overlap),'tv':str(1-overlap)})
    print(json.dumps({'status':'pass','exact_population_probability_cases':len(cases),'bounded_error_decodes':16*len(cases),'max_report_support':max(supports),'lower_bound_laws':lower,'claims_checked':['closed-form covariance vs exhaustive masks','prefix-survival support lemma','coordinate and centered-product variance bounds','exact and adversarially perturbed reconstruction','two-point testing overlap formula'],'limitations':'Finite checks supplement the written proof; they do not prove the general probability bound or constitute Lean verification.'},indent=2))

if __name__=='__main__': main()
