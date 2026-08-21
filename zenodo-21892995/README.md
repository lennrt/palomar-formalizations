# Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification

DOI: [10.5281/zenodo.21892995](https://doi.org/10.5281/zenodo.21892995)

Authors: Lennart Rudolph, Sol, Fable

This directory contains a standalone Palomar submission project in
`palomar/`.

The Lean scope includes the paper's exact full phase-dependent `8 × 8` Bloch
symbol, phase-reversal symmetry, a fraction-free determinant expansion, the
specialized identity `det(xI-B(z)) = F(x^2,z+z^{-1})`, and an all-phase
algebraic certificate for the distinguished root: its rational separator and
nested-radical comparison, nonnegativity of `F(t0,y)` for every
`y ∈ [-2,2]`, strictness away from phase one, and exclusion of zeros above
`t0`.

The formalization does not claim the operator-theoretic conclusion. The
Fourier/direct-integral decomposition, spectral theorem and operator-norm
identification, finite-quotient sampling, the `32 × 32` characteristic
polynomial and Sturm computation, and the exhaustive short-period
classification remain in the paper rather than Lean.

To verify the Lean project:

```sh
cd palomar
lake exe cache get
lake build
```
