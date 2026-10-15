#!/usr/bin/env python3
"""Exact finite checks for the marker-cell decompression construction.

Run with Python 3.9+: python3 check_invariants.py. Standard library only.
Assertions must be enabled. No files are written.

Checks capacity, packet roundtrips, Voronoi geometry, component recognition,
and incidence accounting on fixed graph fixtures. This is not an implementation
of the imported one-bit LOCAL orientation algorithm and does not replace the
universal proofs in the paper or Lean project.
"""

from collections import deque
from random import Random
import json


def graph(n, edges):
    adjacency = [set() for _ in range(n)]
    for u, v in edges:
        assert u != v and 0 <= u < n and 0 <= v < n
        adjacency[u].add(v)
        adjacency[v].add(u)
    return adjacency


def distances(g, v, limit=None):
    result = {v: 0}
    queue = deque([v])
    while queue:
        u = queue.popleft()
        if limit is not None and result[u] == limit:
            continue
        for w in sorted(g[u]):
            if w not in result:
                result[w] = result[u] + 1
                queue.append(w)
    return result


def components(g):
    remaining = set(range(len(g)))
    while remaining:
        component = set(distances(g, min(remaining)))
        yield component
        remaining -= component


def packet_roundtrip(k, s, advice, payload):
    degree = 2 * k - 1
    q = 2**k - 1
    length = (degree * s + 1) // 2
    assert 2 ** (1 + length) <= q ** (s - 1)
    assert advice in (0, 1) and 0 <= payload < 2**length
    packed = 2 * payload + advice
    digits, rest = [], packed
    for _ in range(s - 1):
        rest, digit = divmod(rest, q)
        digits.append(digit)
    assert rest == 0
    labels = [0] + [digit + 1 for digit in digits]
    assert [j for j, label in enumerate(labels) if label == 0] == [0]
    assert all(0 <= label < 2**k for label in labels)
    recovered = sum((label - 1) * q**j for j, label in enumerate(labels[1:]))
    assert recovered % 2 == advice
    assert recovered // 2 == payload


def check_graph(g, k, ids):
    degree = 2 * k - 1
    radius = 16 * (k + 1)
    assert len(set(ids)) == len(g)
    assert all(len(ns) <= degree for ns in g)
    all_edges = [(u, v) for u, ns in enumerate(g) for v in sorted(ns) if u < v]
    cell_count = small_count = 0
    for component in components(g):
        for v in component:
            assert (len(component) <= radius) == (len(distances(g, v, radius)) <= radius)
        if len(component) <= radius:
            small_count += 1
            edge_count = sum(u in component for u, _ in all_edges)
            assert edge_count <= k * len(component)
            continue
        roots = []
        covered = set()
        for v in sorted(component, key=ids.__getitem__):
            if v not in covered:
                roots.append(v)
                covered.update(distances(g, v, 2 * radius))
        dists = {root: distances(g, root) for root in roots}
        for root in roots:
            assert all(root == other or dists[root][other] > 2 * radius for other in roots)
        owner = {v: min(roots, key=lambda root: (dists[root][v], ids[root])) for v in component}
        for root in roots:
            cell = {v for v in component if owner[v] == root}
            cell_count += 1
            assert radius + 1 <= len(cell)
            assert set(distances(g, root, radius)) <= cell
            assert all(dists[root][v] <= 2 * radius for v in cell)
            # Every nonroot has a shortest-path predecessor in its own cell.
            assert all(v == root or any(w in cell and dists[root][w] + 1 == dists[root][v]
                                       for w in g[v]) for v in cell)
            internal = sum(u in cell and v in cell for u, v in all_edges)
            boundary = sum((u in cell) != (v in cell) for u, v in all_edges)
            assert 2 * internal + boundary == sum(len(g[v]) for v in cell)
            assert internal + (boundary + 1) // 2 <= (degree * len(cell) + 1) // 2
            # All roots relevant to assigning a boundary endpoint are locally visible.
            view = set(distances(g, root, 4 * radius + 2))
            for v in cell:
                assert v in view and owner[v] in view
                assert all(owner[w] in view for w in g[v])
    return cell_count, small_count


def main():
    random = Random(20261011)
    packets = 0
    for k in (2, 3, 4, 8, 16):
        radius = 16 * (k + 1)
        for s in (radius + 1, radius + 2, radius + 17, 2 * radius + 1):
            length = ((2 * k - 1) * s + 1) // 2
            for advice in (0, 1):
                for payload in (0, 1, 2**length - 1, random.randrange(2**length)):
                    packet_roundtrip(k, s, advice, payload)
                    packets += 1

    fixtures = [
        ("isolated", 2, graph(1, [])),
        ("K4", 2, graph(4, [(u, v) for u in range(4) for v in range(u + 1, 4)])),
        ("K3,3", 2, graph(6, [(u, v) for u in range(3) for v in range(3, 6)])),
        ("path500", 2, graph(500, [(v, v + 1) for v in range(499)])),
        ("cycle300", 2, graph(300, [(v, (v + 1) % 300) for v in range(300)])),
        ("prism600", 2, graph(600, [(v, (v // 300) * 300 + (v + 1) % 300)
                                    for v in range(600)] + [(v, v + 300) for v in range(300)])),
        ("mixed", 2, graph(505, [(v, v + 1) for v in range(499)] + [(500, 501), (502, 503)])),
        ("degree5", 3, graph(500, [(v, (v + step) % 500) for v in range(500) for step in (1, 2)]
                              + [(v, v + 250) for v in range(250)])),
    ]
    checks = []
    for name, k, g in fixtures:
        for ordering in ("increasing", "permuted"):
            ids = list(range(1, len(g) + 1))
            if ordering == "permuted":
                random.shuffle(ids)
            cells, small = check_graph(g, k, ids)
            checks.append(dict(graph=name, identifiers=ordering, large_cells=cells, small_components=small))
    print(json.dumps(dict(status="pass", packet_cases=packets, graph_cases=checks,
                         scope="Finite checks of geometry, capacity and codec; no implementation of the LOCAL orientation oracle."), indent=2))


if __name__ == "__main__":
    main()
