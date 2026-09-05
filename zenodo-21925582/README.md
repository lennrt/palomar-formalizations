# Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points

DOI: [10.5281/zenodo.21925582](https://doi.org/10.5281/zenodo.21925582)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), the sole
author of record on the cited Zenodo deposit.

Formalization: Lennart Rudolph, with the automated assistants Sol (OpenAI
Codex) and Fable (Anthropic Claude).

This directory contains the standalone Palomar project in `palomar/`.

The quality parameter `t` of a base-2 digital net with `2^m` points measures
exact equidistribution in dyadic boxes, and for Sobol' sequences used in
quasi-Monte Carlo integration and computer graphics the quality of
low-dimensional projections is a practical bottleneck. The OneTwo construction
of Bonneel, Coeurjolly, Iehl, and Ostromoukhov (ACM Transactions on Graphics
44(4), 2025) releases a 692-dimension direction-number table whose protected
pairs `(2k-1, 2k)` have the `(1,2)` property, with acceptance targets `t ≤ 3`
through `m ≤ 10` and `t ≤ 4` through `m ≤ 15` for the pair-aligned
four-dimensional blocks `(2k-1, 2k, 2k+1, 2k+2)`.

Theorem 1.1 of the paper settles the next depth, `m = 16`, a complete batch of
65,536 points. Every one of the 345 pair-aligned windows of the released table
has exact four-dimensional `t`-value 4 when its first dimension is one of
1, 7, 31, 49, 67, 195, 225, 243, 373, and 5 otherwise. The `t ≤ 4` guarantee
therefore extends to `m = 16` in exactly nine windows and fails in the other
336, each failure witnessed by an empty dyadic box of volume `2^-12` in that
projection. Operationally, `t = 4` certifies 16 points in every box of volume
`2^-12` while `t = 5` certifies 32 points only from volume `2^-11`, and the
standard star-discrepancy bound for the projection is `299/4096` at `t = 4`
against `29/256` at `t = 5`. For the worked block, dimensions 25 to 28, the
unique row dependency has mask `0xD2F`, the empty box is
`[0,1) × [1/2,5/8) × [0,1/8) × [0,1/64)`, and the obstruction is inherited from
the unprotected middle pair `(26, 27)`.

The Palomar project compares three declarations, all decided by kernel
reduction of 16-column XOR row reduction over `F₂` with no native evaluation.
`exact_t_five_certificate` is the dimensions 25 to 28 certificate: every
four-composition of total 11 selects independent generator rows and every
total 12 through 16 has a dependent selection, which is `t = 5` exactly.
`census_every_window` is Theorem 1.1 in rank form for all 345 windows, with
the released table embedded as one 256-bit literal per dimension and an
explicit decoder. `census_distribution` is the count 9 and 336 over 345
windows. The census checks are sharded over 35 window files.

The digital-net rank criterion (Dick and Pillichshammer, Theorem 4.52), the discrepancy
bound, and the authentication of the upstream table (repository commit, Git
blob, and file hashes recorded in the paper) are not formalized. The paper's
ancillary depth-15 census and protected-pair audit are not compared. The
theorem is about the pinned released table, not about optimal direction
numbers, scrambled points, unaligned windows, or other prefixes.

The preprint remains CC BY 4.0 under its Zenodo record. The Lean source and
Palomar scaffolding are MIT-licensed under the repository-root `LICENSE`.
