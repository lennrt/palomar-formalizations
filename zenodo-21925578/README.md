# Exact Spectra of Generalized Cubic Subdivision Matrices

DOI: [10.5281/zenodo.21925578](https://doi.org/10.5281/zenodo.21925578)

Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

Authors: Lennart Rudolph, Sol, Fable

This directory contains a standalone Palomar submission project in
`palomar/`.

The upgraded Lean scope is the released outer-matrix content of Lemma 7.1 and
Theorem 7.2. It defines all 28 outer roles in each sector directly from the
pinned `computeBiCubicSubdivisionMatrixBig.m` row data, including exact weights
and cyclic sector references. It constructs the source-to-topological
permutation, proves the resulting `24n` block strictly upper triangular, proves
the exact singleton/core block decomposition, and establishes unconditionally
for every `n ≥ 3` the characteristic polynomial

```text
X^(24n) (X-1/64)^n (X-1/32)^n (X-1/16)^n (X-1/8)^n.
```

Lean does not parse or hash the MATLAB file itself; the formal matrix is an
audited row-by-row translation of the pinned routine (Git blob `ecf810899065`,
SHA-256 `82767dc59f57bdf1c9c3e330d8791cef65a74666521666c99b779fdae98d5836`).
The central `S_n` Fourier decomposition, complete double-ring half-spectrum,
volume tensor-product conclusions, fully irregular volume case, and complete
`C1` theorem remain outside this Lean scope.

To verify the Lean project:

```sh
cd palomar
lake exe cache get
lake build
```
