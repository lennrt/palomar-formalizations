# An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes

DOI: [10.5281/zenodo.21892997](https://doi.org/10.5281/zenodo.21892997)

Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

Authors: Lennart Rudolph, Sol, Fable

This directory contains the standalone Palomar project in `palomar/`.

The upgraded Lean development formalizes actual first simplicial homology over
F₂ for finite graph flag complexes, using unordered graph edges, triangular
clique faces, and the quotient `ker d₁ / range d₂`. It proves that the paper's
family has F₂ first Betti number exactly two for every `n ≥ 7`, proves the
universal F₂ upper bound in Proposition 3.1 for every graph with
`choose(n,2)-n` edges, and bundles these with the exact density and the
obstruction to a complete bipartite spanning subgraph.

The formalized result is F₂-specific. Arbitrary-field and integral homology,
higher homology, and the finite census remain outside the selected Lean scope.
No compared proof uses `native_decide` or a custom axiom.

To verify it:

```sh
cd palomar
lake build
```

The current actual-homology upgrade was reviewed by OpenAI Codex (Sol). The
older Anthropic Claude (Fable) review remains documented as provenance for the
earlier graph-certificate/Boolean-core package, not as a review of the new
Proposition 3.1 proof cone.
