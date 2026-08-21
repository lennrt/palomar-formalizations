# An Explicit Obstruction to Uniform Two-Word π-Representability

DOI: [10.5281/zenodo.21986230](https://doi.org/10.5281/zenodo.21986230)

Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

Authors: Lennart Rudolph, Sol, Fable

This directory contains the Palomar submission project:

- `palomar/` is the standalone Lean project to submit to Palomar.

The formalization defines the paper's finite-word semantics for uniform
two-word π-representability, proves its general neighbourhood-trace bound,
defines the explicit 20-by-741322 bit-incidence graph `B20`, and proves that
`B20` is not representable by two 2-uniform words.  It also retains the
token-order projection/inversion bridge and exact arithmetic endpoints.  The
paper's separate permutation-graph compaction characterization and
VC-dimension consequences remain outside the formalized scope.

To verify the project locally:

```sh
cd palomar
lake exe cache get
lake build
```
