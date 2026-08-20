# Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census

DOI: [10.5281/zenodo.21925458](https://doi.org/10.5281/zenodo.21925458)

This directory contains the DOI preprint as `preprint.pdf` and the standalone
Palomar project in `palomar/`.

The Lean project checks only the unordered-pair symmetry and three rational
identities used in the label-swap argument.  It contains no graph definition
and does not formalize the infinite-family theorem, distance-locus analysis,
or the exhaustive census.

To verify it:

```sh
cd palomar
lake exe cache get
lake build
```

