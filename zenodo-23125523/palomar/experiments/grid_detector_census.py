#!/usr/bin/env python3
"""Census of two-target detector sets on small grids; exact and exhaustive.

For n = 5, 6, 7 this lists the detector sets D(X, Y) of pairs of distinct
mass-two populations that contain neither an interval detector D(I, J) nor the
detector set of a single-target dipole. Their inclusion-minimal members are
counted up to the eight symmetries of the square. These are the boundary
families that a corner-free analogue of the interval-cut criterion would have
to control; with four corners present they are irrelevant, because every pair
is then either detected by two corners or contains an interval detector.
"""
import itertools
import json


def census(n):
    cells = [(x, y) for x in range(n) for y in range(n)]
    singles = [(v,) for v in cells]
    doubles = [tuple(p) for p in itertools.combinations_with_replacement(cells, 2)]

    def bag(population, s):
        d = sorted(abs(s[0] - v[0]) + abs(s[1] - v[1]) for v in population)
        return d[0] * 64 + (d[1] if len(d) > 1 else 63)

    reports = {p: [bag(p, s) for s in cells] for p in singles + doubles}

    def detector_sets(populations):
        found = set()
        for p, q in itertools.combinations(populations, 2):
            rp, rq = reports[p], reports[q]
            mask = 0
            for i in range(len(cells)):
                if rp[i] != rq[i]:
                    mask |= 1 << i
            found.add(mask)
        return found

    dipoles = detector_sets(singles)
    two_target = detector_sets(doubles)
    m = n - 2
    intervals = set()
    for k in range(1, m + 1):
        for a in range(m - k + 1):
            for b in range(m - k + 1):
                mask = 0
                for i, (x, y) in enumerate(cells):
                    if (a < x <= a + k) != (b < y <= b + k):
                        mask |= 1 << i
                intervals.add(mask)
    assert intervals <= two_target, 'every interval detector is realised by a skinny trade'

    def minimal(masks):
        kept = []
        for d in sorted(masks, key=lambda v: v.bit_count()):
            if not any(d & e == e for e in kept):
                kept.append(d)
        return kept

    base = minimal(dipoles | intervals)
    uncovered = [d for d in two_target if not any(d & e == e for e in base)]
    minimal_uncovered = minimal(uncovered)

    def canonical(mask):
        best = None
        for t in range(8):
            image = 0
            for i, (x, y) in enumerate(cells):
                if mask >> i & 1:
                    a, b = x, y
                    if t & 1:
                        a = n - 1 - a
                    if t & 2:
                        b = n - 1 - b
                    if t & 4:
                        a, b = b, a
                    image |= 1 << (a * n + b)
            best = image if best is None else min(best, image)
        return best

    classes = {canonical(d) for d in minimal_uncovered}
    return {'n': n, 'interval_detectors': len(intervals),
            'minimal_dipole_or_interval_detectors': len(base),
            'two_target_detector_sets': len(two_target),
            'two_target_sets_containing_no_dipole_or_interval_detector': len(uncovered),
            'inclusion_minimal_among_them': len(minimal_uncovered),
            'symmetry_classes': len(classes),
            'smallest_size': min(d.bit_count() for d in minimal_uncovered)}


def main():
    rows = [census(n) for n in (5, 6, 7)]
    assert [row['symmetry_classes'] for row in rows] == [12, 28, 62]
    print(json.dumps({'status': 'passed', 'arithmetic': 'exact integers', 'census': rows}, indent=2))


if __name__ == '__main__':
    main()
