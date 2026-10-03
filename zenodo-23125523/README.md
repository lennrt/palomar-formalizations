# Distance-Shell Tomography: Geometric Certificates

Lennart Rudolph · 3 October 2026

Paper: [10.5281/zenodo.23125523](https://doi.org/10.5281/zenodo.23125523) ·
[ResearchGate](https://www.researchgate.net/publication/415199103_Distance-Shell_Tomography_Geometric_Certificates_for_Fault-Tolerant_Sensing_Moment_Compression_and_Hypercube_Equalization)

This directory contains the substantive Lean development and a focused
Palomar interface for *Distance-Shell Tomography: Geometric Certificates for
Fault-Tolerant Sensing, Moment Compression, and Hypercube Equalization*.
The manuscript and full publication archive are available at the DOI above.

- [Mathematical scope, related work, and build instructions](palomar/README.md).
- [The 14 selected declarations and original proofs](palomar/DECLARATIONS.md).
- [Structured authorship and source metadata](palomar/formalization.yaml).
- [Submission paths and current limitations](palomar/SUBMISSION.md).

The principal results characterize one-erasure recovery of two anonymous
targets on grids, determine the exact four-corner sensor budget at every
square size, and bound hypercube equidistant dimension within one. The
selection also includes the long-rectangle optimum, the even bishop-board
optimum, two exact generalized Petersen values, and a connected counterexample
concerning fractional domination and packing faces.

All proof modules are included. The short `Solution.lean` interface applies
theorems proved in that development; it does not replace the proofs with
external assumptions. Supporting algebra, sampling, moment identities, and
geometric lemmas remain in the library even when they are not selected.
The finite hypercube values in the paper and the unrestricted-grid finite
placements are explicitly computational results, not additional kernel-checked
claims.

The project path is `zenodo-23125523/palomar`, pinned to Lean 4.35.0-rc2.
Local verification does not establish service acceptance or registration.
Older sibling projects currently have 258 Lean files without the module
headers required by Palomar's repository-wide policy; those projects are
unchanged by this addition. See [SUBMISSION.md](palomar/SUBMISSION.md).

Lean source and repository scaffolding use the repository-root
[MIT license](../LICENSE). Lennart Rudolph is the sole project author and
responsible maintainer. Automation is disclosed separately in the
[project documentation](palomar/README.md#automation).
