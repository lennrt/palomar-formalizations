#!/usr/bin/env python3
"""Check the two-batch decoder using exact empirical-distribution fixtures.

Run from the supplemental-materials directory:
    python3 scripts/check_streaming.py
Python 3.9+; standard library only. Keep decoder.py and check_sampling.py beside
this file. Do not use -O: verification uses assertions. The script prints a JSON
summary to stdout and writes no result files.

Fixed finite cases include a fixed-seed integer-count set. Each batch reproduces
an enumerated report law exactly. These are deterministic correctness fixtures,
not iid trials or estimates of the paper's statistical success probability.
"""
from fractions import Fraction as F
from itertools import product, repeat, chain
from random import Random
from math import lcm
import json
from check_sampling import pair_law
from decoder import recover_two_batches


def batch(dist):
    den=lcm(*(v.denominator for v in dist.values()))
    return chain.from_iterable(repeat(r,int(v*den)) for r,v in dist.items())


def main():
    rng=Random(11102026); cases=[]
    for n in range(1,4):
        words=list(product([0,1],repeat=n))
        cases.extend((a,b,F(1,2)) for i,a in enumerate(words) for b in words[i:])
    for _ in range(24):
        n=rng.randint(1,4)
        a=tuple(rng.randrange(4) for _ in range(n)); b=tuple(rng.randrange(4) for _ in range(n))
        cases.append((a,b,F(1,2)))
    cases.extend([((1,1),(0,0),F(4,5)),((1,0),(0,1),F(4,5)),((1,3,0),(2,0,2),F(2,3))])
    for a,b,p in cases:
        dist=pair_law(a,b,p)
        result=recover_two_batches(batch(dist),batch(dist),len(a),max(1,*a,*b),p)
        assert result==tuple(sorted([a,b])),(a,b,p,result)
    print(json.dumps({'status':'pass','exact_empirical_distribution_cases':len(cases),'implementation':'decoder.recover_two_batches','scope':'Deterministic reconstruction with exact empirical moments, including the selected covariance column. These repeated-law fixtures are not an iid sampling experiment.'},indent=2))

if __name__=='__main__': main()
