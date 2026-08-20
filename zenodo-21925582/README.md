# Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points

- DOI: <https://doi.org/10.5281/zenodo.21925582>
- Author: Lennart Rudolph
- Preprint: `preprint.pdf`
- Palomar project: `palomar/`

The Palomar project advertises the kernel-replayable finite rank certificate
for the dimensions 25--28 worked block at `m = 16`. It does not formalize the
paper's complete 345-window census or rederive the external digital-net rank
criterion. For Palomar's proof-cone policy, the supplied native exhaustive
subset evaluator was replaced by a deterministic 16-column XOR row-reduction
checker proved with ordinary kernel `decide`; the packed rows and claimed
thresholds are unchanged.

The preprint remains CC BY 4.0 under its Zenodo record. The Lean source and
Palomar scaffolding are MIT-licensed under the repository-root `LICENSE`.
