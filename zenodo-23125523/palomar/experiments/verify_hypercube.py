"""Independent exact checks of the prefix construction and its Q12 witness."""
from itertools import combinations
import json


def verify(n):
    centers = [(1 << (2*j))-1 for j in range(n//2)]
    even = [x for x in range(1 << n) if x.bit_count() % 2 == 0]
    assert len(set(centers)) == n//2
    assert all(s.bit_count() % 2 == 0 for s in centers)
    assert all(any((x ^ s).bit_count() == n//2 for s in centers) for x in even)
    return centers, even


for n in (4, 8, 12, 16):
    verify(n)
n = 12
centers, even = verify(n)
outside = [x for x in even if x not in centers]
checked = 0
for x, y in combinations(outside, 2):
    differing = x ^ y
    if differing == (1 << n)-1:
        z = next(s for s in centers if (s ^ x).bit_count() == n//2)
    else:
        bits = [i for i in range(n) if differing >> i & 1]
        z = x
        for i in bits[:len(bits)//2]:
            z ^= 1 << i
        if z.bit_count() % 2 == 0:
            free = next(i for i in range(n) if not (differing >> i & 1))
            z ^= 1 << free
        assert z.bit_count() % 2 == 1
    assert (z.bit_count() % 2 == 1 or z in centers)
    assert (x ^ z).bit_count() == (y ^ z).bit_count()
    checked += 1
print(json.dumps({"dimension": n, "prefix_centers": centers,
                  "equalizer_size": 2048+len(centers), "conjectured_size": 2064,
                  "outside_pairs_checked": checked,
                  "balancing_dimensions_checked": [4, 8, 12, 16]}, indent=2))
