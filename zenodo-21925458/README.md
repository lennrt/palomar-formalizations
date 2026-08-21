# Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census

DOI: [10.5281/zenodo.21925458](https://doi.org/10.5281/zenodo.21925458)

Authors: Lennart Rudolph, Sol, Fable

This directory contains the standalone Palomar project in `palomar/`.

The Lean project defines the concrete coordinate distance on
`P_m □ C_(6m)`, proves the paper's four-piece cycle distance-pair locus, and
proves that the displayed landmarks `(0,0)`, `(0,2m)`, and `(m-1,0)` resolve
the cylinder for every even `m ≥ 2`. This is the resolving-set half of the
paper's infinite-family theorem. The separate general lower bound establishing
basis minimality and exact multiset dimension, and the finite exhaustive
census, are not formalized in Lean.

To verify it:

```sh
cd palomar
lake exe cache get
lake build
```
