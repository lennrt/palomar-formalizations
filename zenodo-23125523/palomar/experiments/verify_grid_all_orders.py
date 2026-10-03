#!/usr/bin/env python3
"""Exact checks for the all-order grid theorems; integers and literal bags only.

1. Leaf-star placements: for every interior size 1 <= m <= 40 the placement has
   ceil((3m+9)/2) sensors, contains the corners, has odd interior line degrees,
   and meets every equal-length interval detector at least twice. For m <= 7
   one-erasure recovery of every population of mass at most two is re-checked
   from literal distance bags, independently of the interval criterion.
2. Tiny exhaustive optima with corners (m <= 3) agree with the formula.
3. Corner dipoles: the detector set of {(0,1)} versus {(1,0)} is exactly the two
   sides through the corner, without the corner itself.
4. Unrestricted optimum: the proved lower bound L(n) and stored corner-free
   placements. The placements were found by integer programming, but their
   robustness is verified here from literal bags, and optimality follows from
   the proved lower bound, so no solver output is trusted. The stored range is
   3 <= n <= 20. For n = 3 and 4,
   where the optimum exceeds L(n), all smaller placements are enumerated.
"""
import itertools
import json
from pathlib import Path


def corners(m):
    return {(0, 0), (0, m + 1), (m + 1, 0), (m + 1, m + 1)}


def parameters(m):
    q, r = divmod(m, 4)
    return {0: (q, q - 1, 3, 1), 1: (q, q, 1, 1), 2: (q, q, 2, 2), 3: (q + 1, q, 2, 0)}[r]


def leaf_star(m):
    a, b, rho, kappa = parameters(m)
    assert a >= 0 and b >= 0 and rho >= 1
    assert a + 3 * b + rho == m == 3 * a + b + kappa
    sensors = set(corners(m))
    for i in range(a):
        for t in range(3):
            sensors.add((1 + i, 1 + 3 * i + t))
    for i in range(rho):
        sensors.add((a + 1 + i, 0))
    for j in range(b):
        for t in range(3):
            sensors.add((a + rho + 1 + 3 * j + t, 3 * a + kappa + 1 + j))
    for j in range(kappa):
        sensors.add((0, 3 * a + 1 + j))
    assert len(sensors) == 3 * a + 3 * b + rho + kappa + 4
    return sensors


def minimum_cut(m, sensors):
    least = None
    for k in range(1, m + 1):
        for a in range(m - k + 1):
            for b in range(m - k + 1):
                cut = sum(1 for x, y in sensors if (a < x <= a + k) != (b < y <= b + k))
                least = cut if least is None else min(least, cut)
    return least


def populations(n):
    cells = [(x, y) for x in range(n) for y in range(n)]
    return ([()] + [(v,) for v in cells] +
            [tuple(p) for p in itertools.combinations_with_replacement(cells, 2)])


def bag(population, s):
    return tuple(sorted(abs(s[0] - v[0]) + abs(s[1] - v[1]) for v in population))


def robust(n, sensors, pops=None):
    """One-erasure recovery from literal bags, for all populations of mass <= 2."""
    sensors = sorted(sensors)
    if len(sensors) < 2:
        return False
    pops = pops or populations(n)
    signatures = [tuple(bag(p, s) for s in sensors) for p in pops]
    for erased in range(len(sensors)):
        seen = set()
        for signature in signatures:
            reduced = signature[:erased] + signature[erased + 1:]
            if reduced in seen:
                return False
            seen.add(reduced)
    return True


def corner_formula(m):
    return (3 * m + 10) // 2


def unrestricted_lower_bound(n):
    m = n - 2
    return (3 * m + 3) // 2 + (1 if m % 4 == 0 and m >= 4 else 0)


DATA = Path(__file__).resolve().parent / 'data' / 'grid_corner_free_placements.json'


def load_corner_free():
    """Stored placements, n -> list of cells. Found by integer programming;
    nothing about them is trusted until re-verified below."""
    raw = json.loads(DATA.read_text())
    return {int(n): [tuple(cell) for cell in cells] for n, cells in raw.items()}


def main():
    report = {'status': 'running', 'arithmetic': 'exact integers and literal distance bags'}

    rows = []
    for m in range(1, 41):
        n = m + 2
        sensors = leaf_star(m)
        assert len(sensors) == corner_formula(m) == -(-3 * (n + 1) // 2)
        assert corners(m) <= sensors and all(0 <= x < n and 0 <= y < n for x, y in sensors)
        for line in range(1, m + 1):
            assert sum(1 for x, _ in sensors if x == line) % 2 == 1
            assert sum(1 for _, y in sensors if y == line) % 2 == 1
        cut = minimum_cut(m, sensors)
        assert cut >= 2
        literal = robust(n, sensors) if m <= 7 else None
        assert literal in (True, None)
        if m <= 5:
            # negative control: the placement is optimal, so deleting any
            # noncorner sensor must destroy literal recovery
            for s in sensors - corners(m):
                assert not robust(n, sensors - {s})
        rows.append({'m': m, 'n': n, 'sensors': len(sensors), 'minimum_interval_cut': cut,
                     'literal_recovery_checked': bool(literal)})
    report['leaf_star_placements'] = rows

    tiny = []
    for m in (1, 2, 3):
        n = m + 2
        cells = [(x, y) for x in range(n) for y in range(n) if (x, y) not in corners(m)]
        pops = populations(n)
        optimum = None
        for extra in range(len(cells) + 1):
            for chosen in itertools.combinations(cells, extra):
                sensors = corners(m) | set(chosen)
                if minimum_cut(m, sensors) >= 2:
                    assert robust(n, sensors, pops)
                    optimum = len(sensors)
                    break
                # interval cuts are necessary, so failing placements are not robust
            if optimum:
                break
        assert optimum == corner_formula(m)
        tiny.append({'m': m, 'exhaustive_corner_optimum': optimum})
    report['exhaustive_corner_optima'] = tiny

    for n in range(3, 11):
        cells = [(x, y) for x in range(n) for y in range(n)]
        detectors = {s for s in cells if bag(((0, 1),), s) != bag(((1, 0),), s)}
        expected = {(0, y) for y in range(1, n)} | {(x, 0) for x in range(1, n)}
        assert detectors == expected
    report['corner_dipole_detectors_checked_for_n'] = list(range(3, 11))

    unrestricted = []
    for n, placement in sorted(load_corner_free().items()):
        sensors = set(placement)
        assert len(sensors) == len(placement)
        assert all(0 <= x < n and 0 <= y < n for x, y in sensors)
        assert not (sensors & corners(n - 2)) or n <= 4
        pops = populations(n)
        assert robust(n, sensors, pops), n
        bound = unrestricted_lower_bound(n)
        exact = len(sensors)
        if n >= 5:
            assert exact == bound, (n, exact, bound)
            source = 'proved lower bound attained'
            if n <= 9:
                # negative control consistent with optimality
                for s in sensors:
                    assert not robust(n, sensors - {s}, pops)
        else:
            cells = [(x, y) for x in range(n) for y in range(n)]
            for smaller in range(exact):
                for chosen in itertools.combinations(cells, smaller):
                    assert not robust(n, chosen, pops)
            source = 'exhaustive enumeration of all smaller placements'
        m = n - 2
        boundary = sum(1 for x, y in sensors if (x in (0, n - 1)) != (y in (0, n - 1)))
        corner_count = len(sensors & corners(m))
        slack = 4 * exact - 6 * m - boundary - 4 * corner_count
        assert slack >= 0, 'charging bound'
        for cx, cy in corners(m):
            side_cells = ({(cx, y) for y in range(n)} | {(x, cy) for x in range(n)}) - {(cx, cy)}
            assert len(sensors & side_cells) >= 2, 'corner dipole'
        unrestricted.append({'n': n, 'unrestricted_optimum': exact, 'proved_lower_bound': bound,
                             'corner_constrained_optimum': corner_formula(m),
                             'boundary_sensors': boundary, 'corner_sensors': corner_count,
                             'charging_slack': slack,
                             'optimality': source, 'placement': sorted(sensors)})
    report['unrestricted_optima'] = unrestricted
    report['unrestricted_lower_bound_attained_for_n'] = [row['n'] for row in unrestricted
                                                          if row['n'] >= 5]
    assert report['unrestricted_lower_bound_attained_for_n'] == list(range(5, 21))
    report['status'] = 'passed'
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
