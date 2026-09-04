# The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets

DOI: [10.5281/zenodo.22264675](https://doi.org/10.5281/zenodo.22264675)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), the sole
author of record on the cited Zenodo deposit.

Formalization: Lennart Rudolph, with the automated assistants Anthropic Claude
and OpenAI Codex.

This directory contains the standalone Palomar project in `palomar/`.

The Palomar project advertises three theorems in namespace `GKEvenNet`.
`net` is Theorem A: the even-order construction of the published generator
header `gendiag0m2.h` (Grünschloß and Keller, MCQMC 2008 proceedings) is a
base-2 `(0,m,2)`-net for every even `m ≥ 4`. The proof is symbolic in `m` and
states that every dyadic box at every resolution contains exactly one point.
`distance_upper` is the upper bound of Theorem B: for every even `m ≥ 8`, an
explicit pair of points has squared row-shifted tiling distance
`241 · 2^(m-8)`. `distance_m8_exact` is Theorem B at `m = 8`: the minimum
squared tiling distance over all 32,640 pairs and all lattice translates is
exactly `241`. Its lower bound is an exhaustive check reduced by ordinary
kernel `decide`, combined with a symbolic proof that the checked candidate
minimum is the exact lattice minimum. The paper's lower bound for even
`m ≥ 10` is proved in the paper but is not formalized and not selected;
`formalization.yaml` records this exclusion. The Lean definitions transcribe
the generator header, and the `m = 8` point list they produce was diffed
against two independent generators.

The source paper verified the even-`m` net property by computer for even
`m ≤ 22` and stated the general case as a belief. The compared declarations
have no `sorry` and use only `propext`, `Quot.sound`, and `Classical.choice`.

The preprint remains CC BY 4.0 under its Zenodo record. The Lean source and
Palomar scaffolding are MIT-licensed under the repository-root `LICENSE`.
