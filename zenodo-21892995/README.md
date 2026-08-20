# Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification

DOI: [10.5281/zenodo.21892995](https://doi.org/10.5281/zenodo.21892995)

This directory contains a standalone Palomar submission project in
`palomar/`.

The Lean scope is the exact phase-one block reduction and characteristic
polynomial together with certified quartic-root location and exclusion above
the separator.  It does not formalize the full phase-dependent determinant,
Fourier/direct-integral arguments, spectral theorem, or the paper's complete
short-period classification.

To verify the Lean project:

```sh
cd palomar
lake exe cache get
lake build
```

