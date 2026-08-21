# Concrete Barnette graph certificate and prescribed-cycle obstruction

Authors: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), Sol, Fable

This Palomar project formalizes the finite certificate chain for the paper's
explicit 16-vertex counterexample.  The compared declarations check:

- cubicity, the displayed bipartition, and connectivity after deleting any at
  most two vertices;
- the displayed Hamiltonian cycle and its exact complementary perfect
  matching;
- oriented facial incidence, two oppositely oriented face occurrences per
  edge, the exact dual graph, and Euler's equality;
- properness and uniqueness up to a global permutation of the face coloring,
  its three induced edge classes, and the fact that every admissible green
  class meets the complementary matching; and
- the concrete final obstruction for any output satisfying the paper's
  forced-green Property 1.

Two inputs remain outside the formalization: a general topological theorem
turning the oriented incidence data into a cellular embedding of the sphere,
and Property 1 of the published algorithm itself.  The final theorem represents
Property 1 by an explicit hypothesis that the admissible green class is a
subset of the output.

All compared proof dependencies are checked by Lean's kernel and the pinned
NanoDa kernel.  Finite computation uses ordinary `decide`; deletion
connectivity is established through an explicit 137-mask BFS certificate and a
proved bridge to Mathlib's standard `SimpleGraph.Connected` proposition.

## Review history

Anthropic Claude (Fable), acting as a co-author, performed an adversarial
self-review of the archived preprint and its original Lean companion before
release. After the six-theorem Palomar selection was introduced, OpenAI Codex
(Sol), also a co-author, performed a later read-only editorial self-review on
2026-08-20 covering the preprint, compared declarations, their Solution proof
cone, Comparator selection, and metadata. No independent human peer review has
been performed.
