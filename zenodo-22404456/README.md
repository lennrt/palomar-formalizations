# Distance-Shell Tomography on Graphs: Integer Trades and Optimal Grid Sensing

DOI: [10.5281/zenodo.22404456](https://doi.org/10.5281/zenodo.22404456)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)),
the sole author of record on the cited Zenodo deposit.

Formalization: Lennart Rudolph.

This directory contains the published preprint as `preprint.pdf` and its
standalone Palomar project in `palomar/`.

All proof-bearing Lean source files from the Zenodo release are included
unchanged. The eight declarations below are a curated paper-facing Palomar
interface, not a truncation of the underlying Lean development.

The Comparator advertises eight declarations in namespace
`ShellTomography.Verified`. They formalize the bounded integer-trade criterion,
the complete full-factor Cartesian-product kernel and recovery equivalence, a
universal grid sensor lower bound, and the principal all-order square-grid
result: for every `n >= 6`, the alternating `n - 2` boundary sensors have a
unique four-parameter integer kernel, parity-dependent first ambiguity, optimal
sensor count throughout the stated recovery range, and an explicit description
of every equal-observation population fibre.

The formalization uses actual shortest-path distances, labelled sensors, complete
multiplicity-preserving distance bags, and arbitrary nonnegative integer
populations. It covers the paper's principal integer-kernel, recovery-threshold,
sensor-optimality, product, and population-fibre results. It does not claim a
theorem-complete formalization of the paper: the rational-rank clauses,
detector/coding/capacity reformulations, two-sensor cycle theorem, coefficient
census, rational normalization, and executable decoder guarantees remain written
results. Exact alignment and verification notes are included inside `palomar/`.

The preprint is available under CC BY 4.0 at Zenodo. The Lean source and Palomar
scaffolding are MIT-licensed under the repository-root `LICENSE`.
