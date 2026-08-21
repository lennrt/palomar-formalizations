# Palomar project: actual F₂ flag homology and the dense extremal family

Authors: Lennart Rudolph, Sol, Fable

This Lean project formalizes the F₂ content of Theorem 1.1 and Proposition
3.1 of *An Infinite Dense Counterexample Family for Extremal First Betti
Numbers of Flag Complexes*.

The formalization defines the actual finite simplicial chain complex of a
graph's flag complex in degrees zero through two. Its edge basis consists of
unordered `Sym2` edges, its two-face basis consists of three-vertex clique
finsets, and its first homology is the quotient `ker d₁ / range d₂` over
`ZMod 2`. Thus the selected theorems concern a concrete, auditable homology
object rather than an arbitrary supplied vector space or only the earlier
five-vertex Boolean surrogate.

For every `n ≥ 7`, Lean proves:

- the paper's graph `Gₙ` has actual F₂ flag-complex first Betti number two;
- every graph on `n` vertices with exactly `choose(n,2)-n` edges has F₂ first
  Betti number at most two (Proposition 3.1);
- `Gₙ` has exactly `choose(n,2)-n` edges, lies strictly above
  `floor(n²/4)`, attains the universal bound, and has no complete bipartite
  spanning subgraph.

The proof cone internalizes the degree-one consequences of the paper's
topological reductions: cone and leaf normal forms, the `K₂,₃` family core,
complements of cycles, connected-component splitting, and the joined-chain
quotient calculation. No external homology equivalence is assumed by a
compared theorem.

The scope is explicitly F₂ only. The project does not claim arbitrary-field
or integral homology, higher homology, or a formalization of the paper's
finite census. The selected proofs use no `native_decide` and no custom axiom.

Build with:

```sh
lake build
```

`Challenge.lean` contains Mathlib-only transparent definitions and four
compared proof holes: the structural identity `d₁ ∘ d₂ = 0` and the three
paper-level results. `ExtremalFlagBetti/ActualHomology.lean` contains the
implementation, and `Solution.lean` imports the identity and provides the
three paper-level wrappers. Comparator, NanoDa, and the default Lean kernel
check the selected proof cone.

The current upgraded package received a strict OpenAI Codex (Sol) review. The
recorded Anthropic Claude (Fable) review concerned the older graph-certificate
and Boolean-core package; it is retained as provenance, not represented as an
independent review of the new actual-homology proof.
