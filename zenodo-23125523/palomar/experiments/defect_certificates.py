#!/usr/bin/env python3
"""Exact modular certificates for residual defects of binary incidence covers.

No third-party dependencies or floating point are used.  For an r-by-c incidence
matrix A and binary choice x satisfying Ax <= 1, the residual e = 1 - Ax obeys
W e = W 1 whenever W A = 0 (all equations modulo a prime).  An exhaustive search
of small residual SUPPORTS can therefore exclude packing sizes, without searching
all choices x.  This is a necessary condition, not a sufficiency claim.

Reusable API: rref_mod, nullspace_mod, left_kernel, verify_check_matrix,
syndrome, enumerate_residual_supports, regular_packing_bound.
Run this file to verify and print the P(11,4) and P(16,5) examples as JSON.
"""
from itertools import combinations
from math import comb, isqrt
import json


def _prime(p):
    if not isinstance(p, int) or p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("modulus must be prime")


def _shape(a):
    if not a or not a[0] or any(len(row) != len(a[0]) for row in a):
        raise ValueError("matrix must be nonempty and rectangular")
    if any(not isinstance(x, int) for row in a for x in row):
        raise ValueError("matrix entries must be integers")
    return len(a), len(a[0])


def rref_mod(a, p):
    """Return reduced row echelon form and pivot-column indices over F_p."""
    _prime(p)
    rows, cols = _shape(a)
    b = [[x % p for x in row] for row in a]
    pivots, active = [], 0
    for col in range(cols):
        pivot = next((i for i in range(active, rows) if b[i][col]), None)
        if pivot is None:
            continue
        b[active], b[pivot] = b[pivot], b[active]
        inverse = pow(b[active][col], -1, p)
        b[active] = [(x * inverse) % p for x in b[active]]
        for i in range(rows):
            if i != active and b[i][col]:
                factor = b[i][col]
                b[i] = [(x - factor * y) % p for x, y in zip(b[i], b[active])]
        pivots.append(col)
        active += 1
        if active == rows:
            break
    return b, pivots


def nullspace_mod(a, p):
    """A basis of {x: Ax=0}, represented as row vectors."""
    b, pivots = rref_mod(a, p)
    cols = len(a[0])
    basis = []
    for free in range(cols):
        if free not in pivots:
            vector = [0] * cols
            vector[free] = 1
            for row, pivot in enumerate(pivots):
                vector[pivot] = -b[row][free] % p
            basis.append(vector)
    return basis


def left_kernel(a, p):
    """A basis of row checks w with wA=0 for a rectangular matrix."""
    _shape(a)
    return nullspace_mod([list(col) for col in zip(*a)], p)


def verify_check_matrix(a, checks, p):
    """Check every entry of WA exactly; reject malformed checks."""
    _prime(p)
    rows, cols = _shape(a)
    if any(len(w) != rows or any(not isinstance(x, int) for x in w) for w in checks):
        raise ValueError("every check must be an integer vector indexed by matrix rows")
    return all(sum(w[i] * a[i][j] for i in range(rows)) % p == 0
               for w in checks for j in range(cols))


def syndrome(checks, support, p):
    """Syndrome of the zero-one vector whose support is given."""
    _prime(p)
    support = tuple(support)
    if len(set(support)) != len(support):
        raise ValueError("support contains repeated coordinates")
    if checks and any(i < 0 or i >= len(checks[0]) for i in support):
        raise ValueError("support coordinate outside check matrix")
    return [sum(w[i] for i in support) % p for w in checks]


def enumerate_residual_supports(a, checks, p, size, max_subsets=100000):
    """Enumerate all supports of a specified size satisfying We=W1.

    The returned enumeration is complete; an oversized request raises an error
    rather than returning a truncated list that might be mistaken for a proof.
    """
    rows, _ = _shape(a)
    if not isinstance(size, int) or not 0 <= size <= rows:
        raise ValueError("invalid residual size")
    if not verify_check_matrix(a, checks, p):
        raise ValueError("check matrix does not annihilate incidence matrix")
    count = comb(rows, size)
    if count > max_subsets:
        raise ValueError(f"{count} residual supports exceed limit {max_subsets}")
    target = syndrome(checks, range(rows), p)
    allowed = [list(s) for s in combinations(range(rows), size)
               if syndrome(checks, s, p) == target]
    return {"size": size, "supports_checked": count,
            "target_syndrome": target, "compatible_supports": allowed}


def regular_packing_bound(a, checks, p, max_residual_size=2, max_subsets=100000):
    """Prove a packing upper bound for zero-one A with constant column sum.

    Starts from the counting bound floor(number_of_rows / column_sum), and tests
    its residual cardinality.  Only completely enumerated forbidden residual
    sizes improve the bound.  It is safe to return the original bound when a
    requested residual search is beyond the stated budget.
    """
    rows, cols = _shape(a)
    if any(x not in (0, 1) for row in a for x in row):
        raise ValueError("packing incidence matrix must be zero-one")
    degrees = [sum(a[i][j] for i in range(rows)) for j in range(cols)]
    if len(set(degrees)) != 1 or degrees[0] == 0:
        raise ValueError("positive constant column sum is required")
    if not verify_check_matrix(a, checks, p):
        raise ValueError("invalid check matrix")
    degree = degrees[0]
    initial = min(cols, rows // degree)
    bound, exclusions = initial, []
    while bound >= 0:
        defect = rows - degree * bound
        if defect > max_residual_size or comb(rows, defect) > max_subsets:
            break
        record = enumerate_residual_supports(a, checks, p, defect, max_subsets)
        if record["compatible_supports"]:
            break
        exclusions.append({"packing_size": bound, **record})
        bound -= 1
    return {"column_sum": degree, "counting_bound": initial,
            "certified_packing_upper_bound": bound, "excluded_candidates": exclusions}


def petersen_adjacency(n, step):
    """Outer cycle labels 0..n-1; inner star labels n..2n-1."""
    if n < 3 or not (1 <= step and 2 * step < n):
        raise ValueError("requires n>=3 and 1<=step<n/2")
    a = [[0] * (2 * n) for _ in range(2 * n)]
    for i in range(n):
        for u, v in ((i, (i + 1) % n), (i, n + i),
                     (n + i, n + (i + step) % n)):
            a[u][v] = a[v][u] = 1
    assert all(sum(row) == 3 for row in a)
    return a


def _demo(a, checks, p):
    assert verify_check_matrix(a, checks, p)
    basis = left_kernel(a, p)
    assert verify_check_matrix(a, basis, p)
    # Rank-nullity and RREF construction are independently inspectable.
    _, pivots = rref_mod(a, p)
    assert len(basis) == len(a) - len(pivots)
    return {"modulus": p, "rows": len(a), "columns": len(a[0]),
            "check_matrix": checks,
            "computed_left_kernel_basis": basis,
            "rank_mod_prime": len(pivots),
            "left_kernel_dimension": len(basis),
            "check_matrix_annihilates_incidence": True,
            "target_syndrome": syndrome(checks, range(len(a)), p),
            "residual_enumeration": [enumerate_residual_supports(a, checks, p, k)
                                     for k in range(3)],
            **regular_packing_bound(a, checks, p)}


def examples():
    a11 = petersen_adjacency(11, 4)
    integer_w = [-22, 26, 17, -16, 2, 5, 5, 2, -16, 17, 26,
                 17, 5, -10, -19, 11, -7, -7, 11, -19, -10, 5]
    ex11 = _demo(a11, [[x % 23 for x in integer_w]], 23)
    assert ex11["certified_packing_upper_bound"] == 6
    ex11["integer_check"] = integer_w
    ex11["integer_check_times_adjacency"] = [sum(integer_w[i] * a11[i][j] for i in range(22)) for j in range(22)]
    assert ex11["integer_check_times_adjacency"] == [69] + [0] * 21
    ex11["incidence_matrix"] = a11
    ex11["double_total_domination_lower_bound"] = 22 - 6

    a16 = petersen_adjacency(16, 5)
    parts = [[v for v in range(32) if ((v % 16) + v // 16) % 2 == color]
             for color in (0, 1)]
    checks = [
        [[1, 2, 2, 1, 1, 2, 2, 1, 1, 0, 2, 0, 1, 0, 2, 0],
         [1, 1, 2, 2, 1, 1, 2, 2, 0, 1, 0, 2, 0, 1, 0, 2]],
        [[1, 1, 2, 2, 1, 1, 2, 2, 1, 0, 2, 0, 1, 0, 2, 0],
         [2, 1, 1, 2, 2, 1, 1, 2, 0, 1, 0, 2, 0, 1, 0, 2]],
    ]
    ex16 = []
    for color in (0, 1):
        rows, cols = parts[1 - color], parts[color]
        a = [[a16[u][v] for v in cols] for u in rows]
        ex = _demo(a, checks[color], 3)
        assert ex["certified_packing_upper_bound"] == 4
        ex.update({"row_vertices": rows, "candidate_vertices": cols,
                   "incidence_matrix": a})
        ex16.append(ex)
    return {"method": "exact modular residual-support certificates",
            "P(11,4)": ex11,
            "P(16,5)": {"bipartite_checks": ex16,
                         "certified_packing_upper_bound": 8,
                         "double_total_domination_lower_bound": 24}}


def _self_test():
    # Rectangular case with NONZERO target syndrome, so the engine must compare
    # with W1 rather than incorrectly assuming every defect syndrome is zero.
    a = [[1, 0, 1], [0, 0, 0]]
    checks = left_kernel(a, 5)
    assert checks == [[0, 1]]
    record = enumerate_residual_supports(a, checks, 5, 1)
    assert record["target_syndrome"] == [1]
    assert record["compatible_supports"] == [[1]]
    assert enumerate_residual_supports(a, checks, 5, 0)["compatible_supports"] == []
    assert not verify_check_matrix(a, [[1, 0]], 5)
    for invalid in (1, 4, 9):
        try:
            rref_mod(a, invalid)
        except ValueError:
            pass
        else:
            raise AssertionError("composite modulus was accepted")
    try:
        enumerate_residual_supports(a, checks, 5, 1, max_subsets=1)
    except ValueError:
        pass
    else:
        raise AssertionError("an incomplete support search was accepted")


if __name__ == "__main__":
    _self_test()
    print(json.dumps(examples(), indent=2))
