# Lean formalizations of nine preprints

Nine standalone Lean 4 projects, each a machine-checked companion to one
Zenodo preprint by Lennart Rudolph. Each `zenodo-N/` directory holds an
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

| Directory | Paper | DOI |
| --- | --- | --- |
| `zenodo-21890733/` | A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs | [10.5281/zenodo.21890733](https://doi.org/10.5281/zenodo.21890733) |
| `zenodo-21892986/` | Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs | [10.5281/zenodo.21892986](https://doi.org/10.5281/zenodo.21892986) |
| `zenodo-21892995/` | Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification | [10.5281/zenodo.21892995](https://doi.org/10.5281/zenodo.21892995) |
| `zenodo-21892997/` | An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes | [10.5281/zenodo.21892997](https://doi.org/10.5281/zenodo.21892997) |
| `zenodo-21925458/` | Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census | [10.5281/zenodo.21925458](https://doi.org/10.5281/zenodo.21925458) |
| `zenodo-21925574/` | Simpler Graph Conditions for Embedding Tetrahedral Meshes | [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574) |
| `zenodo-21925578/` | Exact Spectra of Generalized Cubic Subdivision Matrices | [10.5281/zenodo.21925578](https://doi.org/10.5281/zenodo.21925578) |
| `zenodo-21925582/` | Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points | [10.5281/zenodo.21925582](https://doi.org/10.5281/zenodo.21925582) |
| `zenodo-21986230/` | An Explicit Obstruction to Uniform Two-Word π-Representability | [10.5281/zenodo.21986230](https://doi.org/10.5281/zenodo.21986230) |

## Verifying a project

Each `zenodo-N/palomar/` directory is an independent Lake project:

```sh
cd zenodo-21986230/palomar
lake exe cache get
lake build
```

Eight projects pin Lean 4.30.0; `zenodo-21892986/` pins Lean 4.32.2.
`ruby scripts/check-layout.rb` checks the repository layout, metadata, and
Comparator configurations of all nine projects.

## Licensing

The Lean source and repository scaffolding are MIT licensed under the root
[`LICENSE`](LICENSE). Each preprint is available under CC BY 4.0 at its Zenodo
record. The repository root carries exactly one licence file, matching the
`project.license` field of every project.

## AI disclosure

OpenAI Codex (Sol) and Anthropic Claude (Fable) were used for formalization
and adversarial analysis. The author selected the statements, reviewed the
proofs, and takes responsibility for the results. Every compared theorem is
checked by the Lean kernel, and each `formalization.yaml` records the
automation methods in detail.
