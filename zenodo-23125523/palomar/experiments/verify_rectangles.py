"""Exact finite checks for rectangular tomography and additive-field topology.

Only exact integer and rational arithmetic is used. These computations supplement the general
Lean proofs; finite exhaustion is not substituted for the infinite results.
"""
from collections import deque
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, product
import json


def vertices(M, N):
    return list(product(range(M + 2), range(N + 2)))


def boundary_columns(M, N):
    return sorted(product((0, M + 1), range(N + 2)))


def cuts(M, N):
    return [(a, b, k) for k in range(1, min(M, N) + 1)
            for a in range(M - k + 1) for b in range(N - k + 1)]


def detects_cut(p, cut):
    a, b, k = cut
    return (a < p[0] <= a + k) != (b < p[1] <= b + k)


def bag(pop, sensor):
    return tuple(sorted(abs(p[0] - sensor[0]) + abs(p[1] - sensor[1]) for p in pop))


def literal_erasure_check(M, N):
    V, S = vertices(M, N), boundary_columns(M, N)
    pops = [()] + [(p,) for p in V] + list(combinations_with_replacement(V, 2))
    codes = [tuple(bag(pop, sensor) for sensor in S) for pop in pops]
    for erased in range(len(S)):
        remaining = [code[:erased] + code[erased + 1:] for code in codes]
        assert len(set(remaining)) == len(pops)
    for cut in cuts(M, N):
        assert sum(detects_cut(s, cut) for s in S) == 2 * cut[2]
    return {"M": M, "N": N, "vertices": len(V), "sensors": len(S),
            "populations_mass_at_most_two": len(pops), "erasure_patterns": len(S),
            "interval_cuts": len(cuts(M, N))}


def minimum_check(M, N):
    """Exclude every corner-containing set one below the claimed minimum.

    The property is monotone under adding sensors, so excluding this size also
    excludes all smaller sets that contain the four corners.
    """
    assert N <= M and 5 * N <= 3 * M
    C = {(0, 0), (0, N + 1), (M + 1, 0), (M + 1, N + 1)}
    extra = sorted(set(vertices(M, N)) - C)
    target = 2 * N + 4
    checked = 0
    if target > 4:
        all_cuts = cuts(M, N)
        for chosen in combinations(extra, target - 5):
            S = C | set(chosen)
            assert any(sum(detects_cut(s, cut) for s in S) < 2 for cut in all_cuts)
            checked += 1
    optimal = 0
    if 5 * N < 3 * M:
        all_cuts = cuts(M, N)
        for chosen in combinations(extra, target - 4):
            S = C | set(chosen)
            if not all(sum(detects_cut(s, cut) for s in S) >= 2 for cut in all_cuts):
                continue
            optimal += 1
            rows = [sum(s[0] == r for s in S) for r in range(1, M + 1)]
            columns = [sum(s[1] == c for s in S) for c in range(1, N + 1)]
            assert 0 in rows
            assert all(degree == 2 for degree in columns)
            assert all(s in C for s in S if s[1] in (0, N + 1))
            assert sum(degree > 0 for degree in rows) <= N
        assert optimal > 0
    return {"M": M, "N": N, "minimum": target,
            "smaller_placements_exhausted": checked,
            "optimal_placements_rigidity_checked": optimal}


def connected(A, B, edges):
    adj = [[] for _ in range(A + B)]
    for r, c in edges:
        adj[r].append(A + c)
        adj[A + c].append(r)
    reached = {0}
    todo = deque([0])
    while todo:
        for v in adj[todo.popleft()]:
            if v not in reached:
                reached.add(v)
                todo.append(v)
    return len(reached) == A + B


def rank(rows, columns):
    """Exact rational Gaussian elimination for the observation map."""
    mat = [[Fraction(x) for x in row] for row in rows]
    rank = 0
    for col in range(columns):
        pivot = next((i for i in range(rank, len(mat)) if mat[i][col]), None)
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        lead = mat[rank][col]
        mat[rank] = [x / lead for x in mat[rank]]
        for i in range(rank + 1, len(mat)):
            scale = mat[i][col]
            if scale:
                mat[i] = [x - scale * y for x, y in zip(mat[i], mat[rank])]
        rank += 1
    return rank


def topology_check(A, B):
    positions = list(product(range(A), range(B)))
    minimum_disconnecting_erasure = len(positions)
    for mask in range(1 << len(positions)):
        E = [p for i, p in enumerate(positions) if mask >> i & 1]
        rows = [[int(j == r or j == A + c) for j in range(A + B)] for r, c in E]
        full_rank = rank(rows, A + B) == A + B - 1
        assert full_rank == connected(A, B, E)
        if not full_rank:
            minimum_disconnecting_erasure = min(minimum_disconnecting_erasure, len(positions) - len(E))
    assert minimum_disconnecting_erasure == min(A, B)
    return {"rows": A, "columns": B, "observation_patterns": 1 << len(positions),
            "minimum_disconnecting_erasure": minimum_disconnecting_erasure}


def main():
    literal = [literal_erasure_check(M, N) for M, N in
               [(0, 0), (2, 1), (4, 2), (5, 3), (8, 4), (12, 2)]]
    minima = [minimum_check(M, N) for M, N in [(0, 0), (2, 1), (3, 1), (4, 2)]]
    topology = [topology_check(A, B) for A, B in [(1, 1), (1, 3), (2, 2), (2, 3), (3, 3)]]
    print(json.dumps({"status": "passed", "arithmetic": "exact integers and rational ranks",
                      "literal_population_checks": literal, "exhaustive_minimum_checks": minima,
                      "additive_field_topology": topology}, indent=2))


if __name__ == "__main__":
    main()
