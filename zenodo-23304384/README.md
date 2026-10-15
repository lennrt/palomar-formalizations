# Lossy Distance-Shell Tomography on Paths

Lennart Rudolph · 11 October 2026 · manuscript version 2.0.0

Paper: [10.5281/zenodo.23252713](https://doi.org/10.5281/zenodo.23252713).
The supplied version and supplemental proofs are archived at
[Zenodo record 23304384](https://zenodo.org/records/23304384).

The substantive Lean project is in [palomar](palomar). Its central result says
that, under independent relay deletion with known survival probability strictly
between zero and one, the mean and covariance of the superimposed reports from
a path's two legs identify the leg populations up to exchange. The covariance
diagonal and one adaptive column suffice. The interface also exposes exact
endpoint semantics and selected variance, rounding, and testing results.

- [Mathematical motivation, observation model, and build instructions](palomar/README.md).
- [The ten selected declarations and their proof sources](palomar/DECLARATIONS.md).
- [Authorship, source fidelity, and formalization metadata](palomar/formalization.yaml).
- [Submission paths and validation limits](palomar/SUBMISSION.md).

The full probability guarantee, general-tree results, unknown-rate calibration,
spider obstruction, and imported trace-complexity theorems are not claimed as
Lean endpoints. The all-length testing bound has the documented factor-two
weaker constant. The complete supplied proof library and exact Python checks
are included. Local validation does not establish Palomar editorial acceptance
or registration. Source and scaffolding are [MIT licensed](../LICENSE).
