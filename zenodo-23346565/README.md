# Optimal Local Decompression on Graphs of Odd Maximum Degree

Lennart Rudolph · 13 October 2026

Paper: [10.5281/zenodo.23346565](https://doi.org/10.5281/zenodo.23346565).

This directory contains the supplied Lean library and an independent
Palomar interface for optimal odd-degree storage. Its main selected theorem
constructs a single decoder family for all graph orders and topologies,
conditional on an explicit total finite-view one-bit orientation rule.
For sufficiently large connected graphs of degree at most `2k-1`, it
recovers arbitrary edge subsets from `k` bits per vertex. The same decoder
has a degree-only neighborhood radius on arbitrary labels, including changes
to topology and marker sets. Storage inequalities, cell geometry, the
advice-first codec and a counting lower bound support this reduction.

The scope is explicit: the external orientation algorithm and its
normalization, computability of the supplied rule, executable LOCAL-machine
semantics, and the paper's final mixed-component assembly remain informal.
The main theorem uses canonical identifiers on `Fin n` and public order `n`.
It is a uniform finite-view reduction, not a claim of end-to-end formalization.

- [Motivation, precise scope and build instructions](palomar/README.md).
- [Selected declarations and substantive proofs](palomar/DECLARATIONS.md).
- [Source and authorship metadata](palomar/formalization.yaml).

The project path is `zenodo-23346565/palomar`, pinned to Lean 4.35.0-rc2
and Mathlib v4.35.0-rc2. Verification reports distinguish proof checks,
rendering, hosted editorial review, and registration.
