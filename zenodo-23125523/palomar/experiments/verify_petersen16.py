"""Defect certificate and independent enumeration for P(16,5)."""
from itertools import combinations
from pathlib import Path
import json

n, step = 16, 5
neighbors = [set() for _ in range(2 * n)]
for i in range(n):
    for a, b in ((i, (i + 1) % n), (i, n + i),
                 (n + i, n + (i + step) % n)):
        neighbors[a].add(b)
        neighbors[b].add(a)

P = {i for i in range(n) if i % 2 == 0} | {
    n + i for i in range(n) if i % 2 == 1}
Q = set(range(2 * n)) - P
assert len(P) == len(Q) == 16
assert all(len(neighbors[i]) == 3 and neighbors[i] <= (Q if i in P else P)
           for i in range(2 * n))

w = [0, 2, 0, -3, 0, 3, 0, -1, 0, -1, 0, 3, 0, -3, 0, 2,
     -1, 0, 1, 0, 0, 0, -2, 0, 2, 0, -2, 0, 0, 0, 1, 0]
assert [sum(w[j] for j in row) for row in neighbors] == [3] + [0] * 31
assert sum(w) == 1 and all(w[i] == 0 for i in P)
assert w[1] == w[n + 8] == 2

def rotate_vertex(v, shift):
    return (v // n) * n + ((v % n + shift) % n)

# For every possible uncovered x, certify a weighting supported in its own
# bipartition, of total weight1, with w(x)=2 and each neighborhood sum divisible3.
for x in range(2 * n):
    shift = ((x % n) - (1 if x < n else 8)) % n
    wx = [0] * (2 * n)
    for v in range(2 * n):
        wx[rotate_vertex(v, shift)] = w[v]
    assert wx[x] == 2 and sum(wx) == 1
    support_part = P if x in P else Q
    assert all(wx[v] == 0 for v in set(range(2 * n)) - support_part)
    assert all(sum(wx[j] for j in row) % 3 == 0 for row in neighbors)

packing = {i for i in range(n) if i % 4 in (0, 1)}
assert len(packing) == 8
assert len(set().union(*(neighbors[i] for i in packing))) == 24

# A size-five packing in a part would have five disjoint triples covering15
# vertices in the other part. Its one missing vertex violates the above weights.
# Independently check the 2*binomial(16,5)=8736 potential size-five packings.
checked = 0
for part in (P, Q):
    for C in combinations(sorted(part), 5):
        checked += 1
        assert len(set().union(*(neighbors[i] for i in C))) < 15
assert checked == 8736
report = {"graph": "P(16,5)", "weights": w,
          "packing": sorted(packing), "bipartition": [sorted(P), sorted(Q)],
          "part_size_five_subsets_checked": checked,
          "open_packing_number": 8, "double_total_domination_number": 24,
          "Zhao_Wei_Conjecture_3_2_prediction": 22}
print(json.dumps(report, indent=2))
