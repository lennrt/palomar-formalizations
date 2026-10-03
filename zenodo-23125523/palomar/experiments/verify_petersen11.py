"""Independent, standard-library certificate verifier for the P(11,4) example.

Labels 0..10 are outer u_i; 11..21 are inner v_i. This is the
opposite u/v naming convention to Zhao--Wei (2017), with identical graph.
The exhaustive check is supplementary: the modular certificate is the proof.
"""
from itertools import combinations
import json
from pathlib import Path

N, STEP = 11, 4
neighbors = [set() for _ in range(2 * N)]
for i in range(N):
    for a, b in ((i, (i + 1) % N), (i, N + i),
                 (N + i, N + (i + STEP) % N)):
        neighbors[a].add(b)
        neighbors[b].add(a)
assert all(len(row) == 3 for row in neighbors)

weights = [-22, 26, 17, -16, 2, 5, 5, 2, -16, 17, 26,
           17, 5, -10, -19, 11, -7, -7, 11, -19, -10, 5]
products = [sum(weights[v] for v in row) for row in neighbors]
assert products == [69] + [0] * 21
assert sum(weights) == 23
assert all(w % 23 != 0 for w in weights)

packing = {0, 5, 8, 13, 14, 19}
assert sum(len(neighbors[i]) for i in packing) == len(set().union(
    *(neighbors[i] for i in packing))) == 18
dominating = set(range(22)) - packing
counts = [len(row & dominating) for row in neighbors]
assert len(dominating) == 16 and min(counts) == 2

neighborhood_masks = [sum(1 << v for v in row) for row in neighbors]
subsets_checked = 0
for candidates in combinations(range(22), 7):
    subsets_checked += 1
    covered = 0
    for v in candidates:
        if covered & neighborhood_masks[v]:
            break
        covered |= neighborhood_masks[v]
    else:
        raise AssertionError(("unexpected packing of size seven", candidates))
assert subsets_checked == 170544

report = {
    "graph": {"name": "P(11,4)", "order": 22, "degree": 3,
              "neighbors": [sorted(row) for row in neighbors]},
    "modulus": 23,
    "certificate_integer_weights": weights,
    "certificate_modular_weights": [w % 23 for w in weights],
    "adjacency_times_integer_weights": products,
    "integer_weight_sum": sum(weights),
    "packing": sorted(packing),
    "packing_neighborhoods": [sorted(neighbors[i]) for i in sorted(packing)],
    "double_total_dominating_set": sorted(dominating),
    "dominating_neighbor_counts": counts,
    "seven_subsets_checked": subsets_checked,
    "open_packing_number": 6,
    "double_total_domination_number": 16,
    "Zhao_Wei_Conjecture_3_1_prediction": 15,
}
print(json.dumps(report, indent=2))
