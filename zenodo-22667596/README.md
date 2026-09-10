# Short-Cycle Decompositions and Full Zombie Damage in Cubic Graphs

Lennart Rudolph · v1.0.0 · 9 September 2026

DOI: [10.5281/zenodo.22667596](https://doi.org/10.5281/zenodo.22667596)

This directory contains the standalone Lean formalization and Palomar project.

- [Lean project and build instructions](palomar/README.md).
- [All 42 selected results](palomar/DECLARATIONS.md).
- [Verification evidence and limitations](palomar/VERIFICATION.md).
- [Submission instructions](palomar/SUBMISSION.md).

The complete supplied Lean development is included: all 132 original library
files plus the three numerical-value modules. The submission states all 42
selected results independently, including the arbitrary-graph four-exception
characterization, Davila Conjecture 24 as a numerical equality, the
`2n(n+1)` survivor-move bound, recurrent coverage and short-cycle classification.
No finite census or unproved classification/routing hypothesis replaces the
main theorem.

Thirteen selected results use transparent presentation wrappers for compatibility
with Palomar's current renderer. Each wrapper directly applies its original
theorem; the [mapping](palomar/verification/selection-map.json) records all 42
results and retains the other 29 original names. All 135 library sources remain
unchanged.

Two written-only paper claims remain explicit: Theorem 13's general,
degree-independent game-interface abstraction (its complete cubic application
is proved directly), and Remark 19's structural connection between diamond
rings and recurrent coverage (the sensor obstruction and lower bound are
formalized). Historical regression results and census counts are computational
tests, not additional formal theorem claims.

The Palomar project directory is `zenodo-22667596/palomar`, with
`comparator.json` and `formalization.yaml` at their conventional paths inside it.

Lean source and repository scaffolding are MIT licensed under [the root
license](../LICENSE). Authorship metadata names Lennart Rudolph
only; automation is disclosed separately in the project documentation.
