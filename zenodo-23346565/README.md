# Optimal Local Decompression on Graphs of Odd Maximum Degree

Lennart Rudolph · 13 October 2026

Paper: [10.5281/zenodo.23346565](https://doi.org/10.5281/zenodo.23346565).

This directory contains the complete supplied Lean proof library and an
independent eight-statement Palomar interface for the paper's finite coding
reduction, graph partitions, arbitrary-label cell geometry, and counting
lower bound. The graph reconstruction theorem chooses one decoder before
the root set and advice, recovers those roots from zero markers, and recovers
every input edge subset from exactly `k` bits per vertex on a connected graph
of odd degree bound `2k-1` with more than `16(k+1)` vertices,
conditional on an explicit boundary-orientation bound. An explicit ordered
packet reader recovers the supplied advice from those same labels without
orientation or payload-index inputs. The same decoder has
label radius `(4r+1)T+8r+2` at each edge's smaller endpoint when roots cover
within `2r` and the orientation is `T`-local on the actual cell quotient;
this locality comparison fixes the graph and marker set.

The unconditional synchronous LOCAL theorem in the manuscript is **partially
formalized**. Its published orientation algorithm, normalization, uniform
execution across changing quotient topologies, and mixed-component assembly
remain paper-level arguments. This submission does not turn those arguments
into axioms or claim a completed formal LOCAL implementation.

- [Mathematical motivation, scope, and build instructions](palomar/README.md).
- [The eight selected declarations and their proofs](palomar/DECLARATIONS.md).
- [Structured source and authorship metadata](palomar/formalization.yaml).

The project is at `zenodo-23346565/palomar`, pinned to Lean 4.35.0-rc2 and
Mathlib v4.35.0-rc2. Local checks do not establish Palomar service acceptance,
notability approval, registration, or independent human peer review.
