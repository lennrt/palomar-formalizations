#!/usr/bin/env python3
"""Exact integer certificate for Rubalcaba's Class-I conjecture counterexample.

All four witnesses are binary vectors, but optimality is proved for the full
real-valued fractional faces: closed-neighborhood rows 3 and 5 sum to the all-ones
row. Thus every fractional dominating vector has mass >=2 and every fractional
packing vector has mass <=2. No LP solver or enumeration of fractional points is
used or needed. This verifier uses only the Python standard library.
"""
import json


def verify():
    order = 6
    edges = [(0, 4), (0, 5), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]
    adjacency = [set() for _ in range(order)]
    for u, v in edges:
        assert u != v
        adjacency[u].add(v)
        adjacency[v].add(u)
    reached, pending = {0}, [0]
    while pending:
        for v in adjacency[pending.pop()]:
            if v not in reached:
                reached.add(v)
                pending.append(v)
    assert reached == set(range(order))
    closed = [[int(u == v or u in adjacency[v]) for u in range(order)]
              for v in range(order)]
    partition = [closed[3][u] + closed[5][u] for u in range(order)]
    assert partition == [1] * order

    supports = {"efficient": [3, 5], "domination_only": [0, 4],
                "packing_only": [1, 5], "packing_other": [2, 5]}
    records = {}
    domination_support, packing_support = set(), set()
    for name, support in supports.items():
        vector = [int(v in support) for v in range(order)]
        loads = [sum(a * b for a, b in zip(row, vector)) for row in closed]
        mass = sum(vector)
        assert mass == 2 and loads[3] + loads[5] == mass
        dominating, packing = min(loads) >= 1, max(loads) <= 1
        # Equality with the universal bounds certifies fractional optimality.
        if dominating:
            domination_support.update(support)
        if packing:
            packing_support.update(support)
        records[name] = {"support": support, "vector": vector, "mass": mass,
                         "closed_neighborhood_loads": loads,
                         "minimum_fractional_dominating": dominating,
                         "maximum_fractional_packing": packing}
    assert records["efficient"]["minimum_fractional_dominating"]
    assert records["efficient"]["maximum_fractional_packing"]
    assert records["domination_only"]["minimum_fractional_dominating"]
    assert not records["domination_only"]["maximum_fractional_packing"]
    assert records["packing_only"]["maximum_fractional_packing"]
    assert not records["packing_only"]["minimum_fractional_dominating"]
    assert records["packing_other"]["maximum_fractional_packing"]
    # Every coordinate is positive on at least one optimal face, so none can be
    # identically zero on both faces. This proves the required negation directly.
    assert domination_support | packing_support == set(range(order))
    coordinate_witness = {}
    for v in range(order):
        for name, record in records.items():
            if v in record["support"]:
                face = ("minimum_fractional_domination" if record["minimum_fractional_dominating"]
                        else "maximum_fractional_packing")
                coordinate_witness[str(v)] = {"witness": name, "face": face, "coordinate": 1}
                break
    return {
        "graph": {"order": order, "edges": edges, "connected": True,
                  "closed_neighborhood_matrix": closed},
        "fractional_optimality_certificate": {
            "partition_rows": [3, 5], "row_sum": partition,
            "domination_mass_lower_bound": 2, "packing_mass_upper_bound": 2,
            "valid_for_all_real_feasible_vectors": True},
        "witnesses": records,
        "class_I": {"faces_intersect": True,
                    "minimum_face_not_subset_of_maximum_face": True,
                    "maximum_face_not_subset_of_minimum_face": True},
        "coordinate_nonnull_witnesses": coordinate_witness,
        "no_joint_domination_and_packing_null_vertex": True,
        "refutes": "Rubalcaba (2005), Conjecture 5.2.5",
        "source": "https://etd.auburn.edu/handle/10415/1030",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
