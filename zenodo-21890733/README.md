# A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs

- DOI: <https://doi.org/10.5281/zenodo.21890733>
- Authors: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), Sol, Fable
- Palomar registry entry: [PALOMAR-2026-08-21-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-21-000002&version=1)
- Palomar project: `palomar/`

The Palomar project exposes six compared declarations covering the finite
certificate chain for the paper's explicit 16-vertex counterexample: cubicity,
bipartiteness, connectivity after every deletion of at most two vertices, the
displayed Hamiltonian cycle and complementary perfect matching, oriented
face/dual incidence and Euler data, face-coloring uniqueness and induced edge
classes, and the final forced-green obstruction.

Two inputs remain explicit and external: the general topological theorem that
turns the oriented incidence certificate into a cellular sphere embedding, and
Property 1 of the published algorithm. The final Lean theorem represents
Property 1 by assuming that every edge of the admissible green class belongs to
the output.

Anthropic Claude (Fable), acting as a co-author, performed an adversarial
self-review of the archived preprint and its original Lean companion before
release. OpenAI Codex (Sol), also a co-author, performed a later read-only
editorial self-review of the six-theorem Palomar selection on 2026-08-20. No
independent human peer review has been performed.

The preprint remains CC BY 4.0 under its Zenodo record. The Lean source and
Palomar scaffolding are MIT-licensed under the repository-root `LICENSE`.
