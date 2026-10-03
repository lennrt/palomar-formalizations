#!/usr/bin/env python3
"""Exact small-dimension checks for the hypercube lower-bound theory.

Checks, with integers only and exhaustive enumeration:
  * parity orthogonality for products of fewer than n integer linear forms;
  * odd sign vectors are never balanced by even words when 4 | n;
  * the quantitative balancing bound mu(B) >= D_t for every admissible size in
    dimensions 4 and 8, for |B| <= 2 in dimension 12, and its equality cases;
  * gamma(Omega_4) = 1 and gamma(Omega_8) = 4, with the exact minimum numbers of
    undominated classes for every smaller size in dimension 8;
  * the independent minimum dominating set of Omega_8 and the isolate identity;
  * the deficit-one rigidity formula in dimension 4.
These supplement the dimension-uniform proofs; they are not a Lean certificate.
"""
import itertools
import json
from math import comb
import random


def weight(x):
    return x.bit_count()


def even_words(n):
    return [x for x in range(1 << n) if weight(x) % 2 == 0]


def class_reps(n):
    return [x for x in range(1 << (n - 1)) if weight(x) % 2 == 0]


def sign(x, n):
    return [-1 if x >> i & 1 else 1 for i in range(n)]


def dot(a, b):
    return sum(u * v for u, v in zip(a, b))


def stability_bound(n, size):
    t = n // 2 - 1 - size
    return max(sum(comb(n, j) for j in range(0, t + 1) if j % 2 == p) for p in (0, 1))


def unbalanced_classes(n, centres):
    return [x for x in class_reps(n)
            if all(weight(x ^ b) != n // 2 for b in centres)]


def undominated_classes(n, centres):
    return [x for x in class_reps(n)
            if all(weight(x ^ b) not in (0, n // 2, n) for b in centres)]


def check_parity_orthogonality(rng):
    cases = 0
    for n in (4, 6, 8):
        points = [sign(x, n) for x in range(1 << n)]
        chi = [1 if weight(x) % 2 == 0 else -1 for x in range(1 << n)]
        for forms in range(0, n):
            for _ in range(6):
                coefficients = [[rng.randint(-5, 5) for _ in range(n)] for _ in range(forms)]
                total = 0
                for y, c in zip(points, chi):
                    value = 1
                    for row in coefficients:
                        value *= dot(row, y)
                    total += c * value
                assert total == 0, (n, forms)
                cases += 1
        # a product of n forms can have a nonzero top coefficient
        total = 0
        for y, c in zip(points, chi):
            value = 1
            for i in range(n):
                value *= y[i]
            total += c * value
        assert total == 1 << n
    return cases


def check_odd_nonvanishing():
    for n in (4, 8, 12):
        evens = even_words(n)[: 64]
        odds = [x for x in range(1 << n) if weight(x) % 2][: 512]
        for b in evens:
            for x in odds:
                assert (n - 2 * weight(b ^ x)) % 4 == 2
    return True


def minimum_over_sets(n, size, measure):
    """Exhaustive minimum of len(measure(n, B)) over size-subsets of classes.
    One member is translated to the zero word when size > 0."""
    reps = class_reps(n)
    if size == 0:
        return len(measure(n, [])), []
    best = None
    for rest in itertools.combinations(reps[1:], size - 1):
        centres = (0,) + rest
        value = len(measure(n, centres))
        if best is None or value < best[0]:
            best = (value, list(centres))
    return best


def main():
    rng = random.Random(20261002)
    report = {'status': 'running', 'arithmetic': 'exact integers'}
    report['parity_orthogonality_cases'] = check_parity_orthogonality(rng)
    report['odd_points_never_balanced'] = check_odd_nonvanishing()

    stability = {}
    for n, sizes in ((4, (0, 1)), (8, (0, 1, 2, 3)), (12, (0, 1, 2))):
        rows = []
        for size in sizes:
            bound = stability_bound(n, size)
            minimum, witness = minimum_over_sets(n, size, unbalanced_classes)
            assert minimum >= bound, (n, size, minimum, bound)
            if size <= 1:
                assert minimum == bound, 'equality case'
            rows.append({'centres': size, 'bound': bound,
                         'exact_minimum_unbalanced_classes': minimum, 'witness': witness})
        stability[str(n)] = rows
    report['quantitative_balancing'] = stability
    assert stability_bound(12, 4) == 12 and stability_bound(16, 6) == 16

    assert len(class_reps(4)) == 4 and not undominated_classes(4, [0])
    domination8 = []
    for size in (1, 2, 3, 4):
        minimum, witness = minimum_over_sets(8, size, undominated_classes)
        domination8.append({'centres': size, 'minimum_undominated': minimum, 'witness': witness})
    assert [row['minimum_undominated'] for row in domination8] == [28, 12, 4, 0]
    report['omega8_domination'] = domination8
    report['gamma_omega4'] = 1
    report['gamma_omega8'] = 4

    independent = [0, 0b011, 0b101, 0b110]
    assert not undominated_classes(8, independent)
    assert all(weight(a ^ b) == 2 for a, b in itertools.combinations(independent, 2))
    report['omega8_independent_minimum_dominating_set'] = independent
    prefixes8 = [(1 << (2 * i)) - 1 for i in range(4)]
    assert not undominated_classes(8, prefixes8) and not unbalanced_classes(8, prefixes8)

    # isolate identity: for dominating sets, unbalanced classes = isolated selected classes
    reps8 = class_reps(8)
    checked = 0
    for rest in itertools.combinations(reps8[1:], 3):
        centres = (0,) + rest
        if undominated_classes(8, centres):
            continue
        isolated = [b for b in centres
                    if all(weight(b ^ c) != 4 for c in centres if c != b)]
        assert sorted(unbalanced_classes(8, centres)) == sorted(isolated)
        checked += 1
    report['omega8_dominating_four_sets_checked_for_isolate_identity'] = checked

    # deficit-one rigidity in dimension four: B = {0}
    n = 4
    U = [0, 15]
    for y in range(1 << n):
        sy = sign(y, n)
        left = dot(sign(0, n), sy)
        right = 0
        for u in U:
            su = sign(u, n)
            fu = dot(sign(0, n), su)
            inner = 0
            for k in range(0, n // 2):
                for subset in itertools.combinations(range(n), k):
                    term = 1
                    for i in subset:
                        term *= su[i] * sy[i]
                    inner += term
            right += fu * inner
        assert left * (1 << (n - 1)) == right
    report['deficit_one_rigidity_dimension_four'] = True

    report['status'] = 'passed'
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
