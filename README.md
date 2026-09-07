![Palomar Formalizations: observatory dome beneath a graph-like constellation at dusk](assets/palomar-hero.png)

# Lean formalizations of Zenodo preprints

This repository holds standalone Lean 4 projects, each a machine-checked
companion to one Zenodo preprint by Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), who is the sole author of
record on every cited deposit. Each `zenodo-N/` directory holds an
independent Lake project prepared for submission to the
[Palomar registry](https://palomar-registry.org/). Each
project states its selected theorems in `Challenge.lean`, proves them in
`Solution.lean`, and records its scope, sources, and Comparator configuration
in `formalization.yaml` and `comparator.json`.

Every formalization is deliberately scoped. The per-directory READMEs, the
`Challenge.lean` module docstrings, and the `formalization.yaml` scope fields
state which results are formalized and which remain informal in the paper. No
project claims to formalize its paper end to end.

## Index

| Directory | Paper | DOI | Registry |
| --- | --- | --- | --- |
| `zenodo-21890733/` | A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs | [10.5281/zenodo.21890733](https://doi.org/10.5281/zenodo.21890733) | [PALOMAR-2026-08-21-000002](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-21-000002&version=1) |
| `zenodo-21892986/` | Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs | [10.5281/zenodo.21892986](https://doi.org/10.5281/zenodo.21892986) | [PALOMAR-2026-08-21-000008](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000008&version=1) |
| `zenodo-21892995/` | Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification | [10.5281/zenodo.21892995](https://doi.org/10.5281/zenodo.21892995) | [PALOMAR-2026-09-02-000008](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000008&version=1) |
| `zenodo-21892997/` | An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes | [10.5281/zenodo.21892997](https://doi.org/10.5281/zenodo.21892997) | [PALOMAR-2026-09-02-000002](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000002&version=1) |
| `zenodo-21925458/` | Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census | [10.5281/zenodo.21925458](https://doi.org/10.5281/zenodo.21925458) | [PALOMAR-2026-08-21-000011](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000011&version=1) |
| `zenodo-21925574/` | Simpler Graph Conditions for Embedding Tetrahedral Meshes | [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574) | [PALOMAR-2026-09-04-000002](https://palomar-registry.org/entry?id=PALOMAR-2026-09-04-000002&version=1) |
| `zenodo-21925578/` | Exact Spectra of Generalized Cubic Subdivision Matrices | [10.5281/zenodo.21925578](https://doi.org/10.5281/zenodo.21925578) | [PALOMAR-2026-08-21-000010](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000010&version=1) |
| `zenodo-21925582/` | Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points | [10.5281/zenodo.21925582](https://doi.org/10.5281/zenodo.21925582) | [PALOMAR-2026-09-05-000004](https://palomar-registry.org/entry?id=PALOMAR-2026-09-05-000004&version=1) |
| `zenodo-21986230/` | An Explicit Obstruction to Uniform Two-Word π-Representability | [10.5281/zenodo.21986230](https://doi.org/10.5281/zenodo.21986230) | [PALOMAR-2026-08-21-000007](https://palomar-registry.org/entry?id=PALOMAR-2026-08-21-000007&version=1) |
| `zenodo-22264675/` | The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets | [10.5281/zenodo.22264675](https://doi.org/10.5281/zenodo.22264675) | [PALOMAR-2026-09-04-000001](https://palomar-registry.org/entry?id=PALOMAR-2026-09-04-000001&version=1) |
| `zenodo-22404456/` | Distance-Shell Tomography on Graphs: Integer Trades and Optimal Grid Sensing | [10.5281/zenodo.22404456](https://doi.org/10.5281/zenodo.22404456) | [PALOMAR-2026-09-07-000003](https://palomar-registry.org/entry.html?id=PALOMAR-2026-09-07-000003&version=1) |

## Verifying a project

Each `zenodo-N/palomar/` directory is an independent Lake project:

```sh
cd zenodo-22264675/palomar
lake exe cache get
lake build
```

Each project's `lean-toolchain` pins its Lean release, currently 4.30.0 or
4.32.0, with Mathlib at the matching tag. `ruby scripts/check-layout.rb`
checks the repository layout, metadata, and Comparator configurations of
every project.

## Licensing

The Lean source and repository scaffolding are MIT licensed under the root
[`LICENSE`](LICENSE). Each preprint is available under CC BY 4.0 at its Zenodo
record. The repository root carries exactly one licence file, matching the
`project.license` field of every project.

## AI disclosure

The papers are authored by Lennart Rudolph
([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)) alone;
each paper's own declaration states that no AI system is listed as an author.

The formalizations are by Lennart Rudolph, with the automated assistants Sol
(OpenAI Codex) and Fable (Anthropic Claude). Sol and Fable contributed
formalization and adversarial analysis; Lennart Rudolph selected the statements, reviewed the proofs, and
takes responsibility for the results.
Every compared theorem is checked by the Lean kernel, and each
`formalization.yaml` records the automation methods in detail.
