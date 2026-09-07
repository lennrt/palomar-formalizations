# Distance-shell tomography: universal grid recovery

Lennart Rudolph. Companion to *Distance-Shell Tomography on Graphs: Integer Trades
and Optimal Grid Sensing*, published as version 1.0.0 at
[10.5281/zenodo.22404456](https://doi.org/10.5281/zenodo.22404456).

General integer-trade criterion and full-factor Cartesian-product kernel/recovery theorem; the all-order grid lower bound; and, for every n ≥ 6, the complete four-parameter integer grid kernel, exact threshold n−2 for odd n and n−3 for even n, optimal n−2 sensor count throughout 2 ≤ h < threshold, and unique four-parameter description of equal-observation populations.

The compared statements use actual graph shortest-path distances, full labelled
multisets, unrestricted integer parameters and arbitrary grid orders n ≥ 6.
The intended audience includes researchers in discrete tomography, graph
identification, integer inverse problems, and channels with multiset outputs.
[COVERAGE.md](COVERAGE.md) maps each declaration to the paper; [NOTABILITY.md](NOTABILITY.md)
explains the motivating recovery problem and the substantive research contribution.

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

Lean 4.30.0 and Mathlib v4.30.0 are pinned. Challenge imports only Mathlib and supplies
its definitions directly. Its eight theorem placeholders specify the comparison;
Solution and its dependency graph contain no placeholders or nonstandard axioms.
The full proof development shipped with the Zenodo release is present unchanged;
the eight declarations are the paper-facing interface rather than the complete
inventory of supporting lemmas.
The independent comparison checks all eight declarations and replays proof terms
with both Lean and NanoDa. See [VERIFICATION.md](VERIFICATION.md) for executed checks.

The uniform proof uses Laurent-polynomial row identities, an exact tridiagonal
inverse, support restrictions and a structural minimum-mass bound. It does not
extrapolate from ranks or finite orders. This is a strong formalization of the
paper's integer core, not a theorem-complete formalization of every written claim.
The rational-rank clauses, detector/coding/capacity reformulations, two-sensor
cycle theorem, coefficient census, rational fibre normalization, and executable
decoder guarantees have no corresponding paper-level Lean theorem in this release.

Lean includes three benign endpoint extensions recorded in `COVERAGE.md`: the
trade criterion at mass bound zero, the product clauses for an empty sensor-label
type, and vacuous small-grid cases of the lower-bound theorem. The substantive
grid theorems retain the paper's hypothesis `n ≥ 6`.

Metadata: `formalization.yaml`. License: MIT. The included reports document local
verification; they do not constitute an official Palomar registry decision.
