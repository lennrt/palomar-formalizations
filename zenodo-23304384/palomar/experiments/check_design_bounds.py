#!/usr/bin/env python3
"""Finite exact checks of the paper's two-batch bound coefficients.

Run from the supplemental-materials directory:
    python3 scripts/check_design_bounds.py
Python 3.9+; standard library only. Do not use -O: verification uses assertions.
The script prints a JSON summary to stdout and writes no result files.

All assertions use fractions.Fraction. A fixed grid of n, survival probabilities,
count bounds and confidences checks the stated algebraic identities and bounds;
no parameter is fitted or selected by a search. Logarithms and probabilities of
empirical events are not approximated. These finite regression checks supplement
the written universal proof and do not establish the probability guarantee.
"""
from fractions import Fraction as F
import json


def main():
    counts = dict(prefix_scale_inequalities=0, rational_design_bounds=0,
                  finite_tail_sums=0, bernstein_denominators=0,
                  batch_budget_coefficients=0, lower_overlap_identities=0)
    samples = []
    confidences = [F(1, 2), F(1, 4), F(1, 10), F(1, 100), F(1, 1000)]
    for n in range(1, 101):
        pstar = F(2*n, 2*n+1)
        probabilities = [F(1, 100), F(1, 5), F(1, 2), F(4, 5), F(99, 100), pstar]
        for p in probabilities:
            t = p**n
            sn = 1-t
            for k in range(1, n+1):
                sk = 1-p**k
                # Core weighted-union inequality; no floating point.
                assert n*sk >= k*sn
                assert sk >= k*(1-p)*p**(n-1)
                counts['prefix_scale_inequalities'] += 1
                for h in (1, 2, 10):
                    d = 2*h
                    alpha = t*sk/5
                    vprod, bprod = 2*d**4*sk, 2*d**2
                    vmean, bmean = 2*d**2*sk, d
                    product_denom = 2*(vprod+bprod*alpha/3)
                    mean_denom = 2*(vmean+bmean*alpha/3)
                    assert product_denom <= 5*d**4*sk
                    assert mean_denom <= 5*d**4*sk
                    assert alpha**2/product_denom >= t*t*sk/(125*d**4)
                    assert alpha**2/mean_denom >= t*t*sk/(125*d**4)
                    counts['bernstein_denominators'] += 1
            # General per-batch budget = coefficient * L, L=log(1+8/delta).
            # Multiplying this coefficient by the Bernstein exponent scale
            # produces L exactly, independently of the value of L.
            coefficient = F(2000*n, 1)/(t*t*sn)  # h=1; h^4 cancels.
            exponent_scale = t*t*sn/F(2000*n, 1)
            assert coefficient*exponent_scale == 1
            counts['batch_budget_coefficients'] += 1

        z = pstar**n
        assert F(1, 2) < z <= F(2, 3)
        assert z >= 1-n*(1-pstar)
        assert (1/pstar)**n >= F(3, 2)
        assert z*z*(1-z) >= F(1, 8)
        # Therefore 16000 h^4 n * L is at least the general batch budget.
        assert F(16000*n, 1)*z*z*(1-z)/F(2000*n, 1) >= 1
        counts['rational_design_bounds'] += 1
        q = 1-pstar
        common = 1-2*pstar*pstar*q
        assert 0 < common < 1
        assert common-pstar*pstar == q*q*(1+2*pstar)
        assert common >= pstar*pstar
        assert 2*(1/pstar-1) == F(1, n)
        counts['lower_overlap_identities'] += 1
        for delta in confidences:
            # At a=L, r=exp(-a)=delta/(delta+8).  An exponent a>=L only
            # reduces these tails.  Two statistics at each k give factor4.
            r = delta/(delta+8)
            finite = sum((r**k for k in range(1, n+1)), F(0))
            infinite = r/(1-r)
            assert finite == r*(1-r**n)/(1-r)
            assert finite <= infinite == delta/8
            assert 4*finite <= delta/2
            assert 2*(4*finite) <= delta
            counts['finite_tail_sums'] += 1
        if n in (1, 2, 10, 100):
            samples.append({'n': n, 'p': str(pstar),
                            'design_coefficient_verified': bool(8*z*z*(1-z) >= 1)})
    print(json.dumps({
        'status': 'pass',
        'arithmetic': 'fractions.Fraction; no floating-point assertions',
        'n_range': [1, 100],
        'counts': counts,
        'sample_design_values': samples,
        'claims_checked': [
            '(1-p^k) >= (k/n)(1-p^n)',
            'bounded-variable Bernstein denominator constants',
            'p=2n/(2n+1) gives 1/2 < p^n <= 2/3',
            'p^(2n)(1-p^n) >= 1/8 for the rational design',
            '16000 h^4 n log(1+8/delta) dominates the general batch bound',
            'finite geometric union of index-dependent tails is <=delta/2 per batch',
            'common-law mass exceeds p^2 and rational log-bound coefficient equals1/n'
        ],
        'limitations': 'Finite algebraic checks only. Bernstein concentration, infinite-tail summation, rounding correctness, and the general sample theorem require the written proof; this script does not establish universal or Lean claims.'
    }, indent=2))


if __name__ == '__main__':
    main()
