"""Integer checks supplementing the all-order even-bishop proof."""
from itertools import combinations
import json


def adjacent(p, q):
    return p != q and abs(p[0]-q[0]) == abs(p[1]-q[1])


def dominates(vs, selected):
    s = set(selected)
    return all(v in s or sum(adjacent(v, u) for u in s) >= 2 for v in vs)


counts = {}
for n in (2, 4, 6):
    vs = [(x, y) for x in range(n) for y in range(n) if (x+y) % 2 == 0]
    # Monotonicity means excluding n-1 excludes all smaller selected sets.
    checked = 0
    for s in combinations(vs, n-1):
        assert not dominates(vs, s)
        checked += 1
    counts[n] = checked
for n in range(2, 42, 2):
    vs = [(x, y) for x in range(n) for y in range(n)]
    selected = [(x, y) for x in (0, n-1) for y in range(n)]
    assert len(set(selected)) == 2*n and dominates(vs, selected)
    even_border = [p for p in vs if sum(p) % 2 == 0 and
                   (p[0] in (0, n-1) or p[1] in (0, n-1))]
    assert len(even_border) == 2*(n-1)
    assert all(s != 2*n-2-s for s in range(0, 2*n-1, 2))
print(json.dumps({"minimum_component_checks": counts,
                  "upper_bound_even_orders_checked": [2, 40],
                  "boundary_count_and_fixed_point_parity_checked": True}, indent=2))
