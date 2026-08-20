# An Explicit Obstruction to Uniform Two-Word π-Representability

DOI: [10.5281/zenodo.21986230](https://doi.org/10.5281/zenodo.21986230)

This directory pairs the deposited preprint with its Palomar submission
project:

- `preprint.pdf` is the DOI preprint;
- `palomar/` is the standalone Lean project to submit to Palomar.

The formalization is deliberately scoped.  It proves the token-order
projection/inversion bridge, same-fibre independence, the exact `k = 2`,
`m = 20` arithmetic endpoint, and the finite pigeonhole obstruction.  It does
not formalize words, graph compactions, the full characterization theorem, or
the paper's explicit graph nonmembership theorem.

To verify the project locally:

```sh
cd palomar
lake exe cache get
lake build
```

