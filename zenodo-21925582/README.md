# Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points

- DOI: <https://doi.org/10.5281/zenodo.21925582>
Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

- Authors: Lennart Rudolph, Sol, Fable
- Palomar project: `palomar/`

The Palomar project advertises kernel-replayable exact rank certificates for
all 345 pair-aligned four-dimensional windows of the 692-dimension OneTwo
table at `m = 16`, together with the dimensions 25--28 worked block and the
census distribution (9 windows at `t = 4`, 336 at `t = 5`). It does not
rederive the external digital-net rank criterion or authenticate the upstream
direction-number table. For Palomar's proof-cone policy, the supplied native
exhaustive subset evaluator was replaced by a deterministic 16-column XOR
row-reduction checker proved with ordinary kernel `decide`; the packed rows
and claimed thresholds are unchanged. The census checks are sharded over 35
window files, and the dimension table enters the Challenge as one 256-bit
literal per dimension with an explicit in-file decoder.

The preprint remains CC BY 4.0 under its Zenodo record. The Lean source and
Palomar scaffolding are MIT-licensed under the repository-root `LICENSE`.
