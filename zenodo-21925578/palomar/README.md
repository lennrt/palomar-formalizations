# Palomar project: released cubic outer double-ring spectrum

Authors: Lennart Rudolph, Sol, Fable

This project formalizes the outer-matrix part of Lemma 7.1 and Theorem 7.2
from *Exact Spectra of Generalized Cubic Subdivision Matrices*.

`Challenge.lean` defines a naturally source-indexed `28n × 28n` matrix. Its
28 row roles per sector are a literal mathematical translation of rows
`2,...,29` in the pinned `computeBiCubicSubdivisionMatrixBig.m`, after removing
the central rows and columns. The definition records every rational weight and
every previous/current/next-sector reference. The pinned routine has Git blob
`ecf810899065` and SHA-256
`82767dc59f57bdf1c9c3e330d8791cef65a74666521666c99b779fdae98d5836`.

The selected results then:

- construct the explicit topological reindexing in which
  `{24_s,25_s,29_(s+1)}` is one ordered core;
- prove entrywise that the reindexed source matrix is the paper's nested
  upper-block normal form;
- prove the first `24n` coordinates form a strictly upper-triangular block;
- compute the exact displayed `3 × 3` core's characteristic polynomial; and
- prove directly for every `n ≥ 3` that the released outer matrix has

```text
X^(24n) (X-1/64)^n (X-1/32)^n (X-1/16)^n (X-1/8)^n.
```

Thus the compared final theorem has no assumed source-to-permutation equality.
The remaining provenance boundary is narrower: Lean does not parse MATLAB or
cryptographically verify the external file. The row-by-row Lean definition was
human/agent audited against the pinned file. The central matrix's Fourier
decomposition, Corollary 7.3, tensor-product volume results, fully irregular
volume matrices, and a complete `C1` theorem remain outside this project.

The project pins Lean and Mathlib v4.30.0. Build it with:

```sh
lake exe cache get
lake build
```

The selected proofs use no `native_decide`, `sorry`, or project axioms. Their
reported foundational axioms are `propext`, `Quot.sound`, and
`Classical.choice`.
