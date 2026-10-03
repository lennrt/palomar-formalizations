#!/usr/bin/env python3
"""Exact checks accompanying the Cartesian-trades and distance-moments section.

Run `python3 experiments/verify_moments.py` from the project root. Only the
Python standard library is required; output is deterministic JSON. Checks cover
single-moment/marginal kernel equality, optimal cube interpolation, sharp parity
and paired-trade witnesses, and literal finite-population/grid comparisons.
These bounded computations supplement, and do not replace, the general proofs
in paper/moments.tex. No floating-point arithmetic or optimizer is used.
"""
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
from math import comb, factorial
import json


def rank(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    if not a:
        return 0
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        v = a[r][c]
        a[r] = [x / v for x in a[r]]
        for i in range(len(a)):
            if i != r and a[i][c]:
                v = a[i][c]
                a[i] = [x - v * y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def hamming(x, y):
    return sum(a != b for a, b in zip(x, y))


def moment_matrix(alphabets, k):
    vertices = list(product(*(range(q) for q in alphabets)))
    return vertices, [[hamming(s, x) ** k for x in vertices] for s in vertices]


def marginal_matrix(vertices, k):
    d = len(vertices[0])
    rows = []
    for size in range(min(k, d) + 1):
        for inds in combinations(range(d), size):
            for vals in sorted({tuple(x[i] for i in inds) for x in vertices}):
                rows.append([int(tuple(x[i] for i in inds) == vals) for x in vertices])
    return rows


def moment(pop, vertices, k):
    return tuple(sum(hamming(s, x) ** k for x in pop) for s in vertices)


def parity_populations(d, active):
    pos, neg = [], []
    for bits in product(range(2), repeat=active):
        (pos if sum(bits) % 2 == 0 else neg).append(bits + (0,) * (d - active))
    return pos, neg


def paired_populations(d, k):
    pos, neg = [], []
    for bits in product(range(2), repeat=k):
        point = tuple(v for b in bits for v in (b, 1 - b)) + (0,) * (d - 2 * k)
        (pos if sum(bits) % 2 == 0 else neg).append(point)
    return pos, neg


def cube_sampling(d, k):
    vertices, matrix = moment_matrix([2] * d, k)
    small = [i for i, s in enumerate(vertices) if sum(s) <= k]
    expected = sum(comb(d, j) for j in range(k + 1))
    assert len(small) == expected
    assert rank(matrix) == expected == rank([matrix[i] for i in small])
    # Deterministic signed input: verify the explicit inversion numerically.
    z = [(7 * i * i + 3 * i + 2) % 11 - 5 for i in range(len(vertices))]
    f = {s: sum(a * b for a, b in zip(row, z)) for s, row in zip(vertices, matrix)}
    coeff = {}
    for size in range(k + 1):
        for inds in combinations(range(d), size):
            value = 0
            for subsize in range(size + 1):
                for sub in combinations(inds, subsize):
                    point = tuple(int(i in sub) for i in range(d))
                    value += (-1) ** (size - subsize) * f[point]
            coeff[inds] = value
    for s in vertices:
        assert f[s] == sum(a for inds, a in coeff.items() if all(s[i] for i in inds))
    return {"d": d, "k": k, "rank_and_sensors": expected}


def grid_signature(pop, a, b, corner_count):
    field = tuple(sum(abs(s-x) + abs(t-y) for x, y in pop)
                  for s in range(a) for t in range(b))
    bags = [tuple(sorted(x + y for x, y in pop))]
    if corner_count == 2:
        bags.append(tuple(sorted(x + b - 1 - y for x, y in pop)))
    return (field, *bags)


def main():
    report = {"arithmetic": "exact integers/Fraction; Python standard library only"}
    checks = []
    for alphabets in ([2], [2, 2], [2, 3], [2, 2, 2], [2, 3, 2], [3, 3, 3]):
        for k in range(len(alphabets) + 2):
            vertices, mm = moment_matrix(alphabets, k)
            marg = marginal_matrix(vertices, k)
            mr = rank(mm)
            assert mr == rank(marg) == rank(mm + marg)
            checks.append({"alphabets": alphabets, "k": k, "common_row_rank": mr})
    report["single_moment_marginal_equivalence"] = checks
    report["cube_sampling"] = [cube_sampling(d, k) for d in range(1, 6) for k in range(d + 1)]
    parity = []
    for d in range(1, 8):
        vertices = list(product(range(2), repeat=d))
        for k in range(d):
            p, n = parity_populations(d, k + 1)
            assert len(p) == len(n) == 2**k
            assert moment(p, vertices, k) == moment(n, vertices, k)
            parity.append({"d": d, "k": k, "ambiguous_mass": len(p)})
    report["capacity_obstructions"] = parity
    sharp = []
    for k in range(1, 4):
        for d in range(2*k, 2*k+3):
            vertices = list(product(range(2), repeat=d))
            p, n = paired_populations(d, k)
            mp, mn = moment(p, vertices, k), moment(n, vertices, k)
            diff = tuple(a-b for a, b in zip(mp, mn))
            expected = []
            for s in vertices:
                value = factorial(k)
                for i in range(k):
                    value *= 2*(s[2*i] - s[2*i+1])
                expected.append(value)
            assert diff == tuple(expected)
            distance = sum(v != 0 for v in diff)
            assert distance == 2**(d-k)
            sharp.append({"d": d, "k": k, "mass": len(p), "distance": distance})
    report["sharp_paired_trade_distance"] = sharp
    # Literal exhaustive population checks, including multiplicities.
    exhaustive = []
    for d, k, h in ((2,1,1), (3,2,3), (4,2,3)):
        vertices = list(product(range(2), repeat=d))
        signatures = {}
        for pop in combinations_with_replacement(vertices, h):
            sig = moment(pop, vertices, k)
            assert sig not in signatures, (d,k,h,pop,signatures.get(sig))
            signatures[sig] = pop
        exhaustive.append({"d":d,"k":k,"mass":h,"populations_checked":len(signatures)})
    report["exhaustive_unique_populations"] = exhaustive
    grid_checks = []
    for a,b,c,h in ((3,3,1,2), (4,4,2,3)):
        signatures = set()
        for pop in combinations_with_replacement(list(product(range(a),range(b))), h):
            sig = grid_signature(pop,a,b,c)
            assert sig not in signatures
            signatures.add(sig)
        grid_checks.append({"a":a,"b":b,"full_corners":c,"mass":h,"populations_checked":len(signatures)})
    p3,n3=[(0,1),(1,2),(2,0)],[(0,2),(1,0),(2,1)]
    p4,n4=[(3,2),(2,0),(1,3),(0,1)],[(3,1),(2,3),(1,0),(0,2)]
    assert grid_signature(p3,3,3,1)==grid_signature(n3,3,3,1)
    assert grid_signature(p4,4,4,2)==grid_signature(n4,4,4,2)
    report["grid_hybrid"]={"unique_checks":grid_checks,"mass3_witness":[p3,n3],"mass4_witness":[p4,n4]}
    report["status"]="all checks passed"
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
