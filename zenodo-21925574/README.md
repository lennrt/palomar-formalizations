# Simpler Graph Conditions for Embedding Tetrahedral Meshes

DOI: [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574)

Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

Authors: Lennart Rudolph, Sol, Fable

The compared Lean theorem group now formalizes the paper's actual
ambient-to-finite bridge. It defines a finite abstract simplicial complex and
boundary subcomplex, restricts them to an injectively labelled four-clique,
and proves under the paper's boundary-triangle condition (BT) that the induced
pair gives an admissible `FourVertexPair` (Lemma 7.1). It then identifies the
actual relative `C₂ → C₁` map, `d₃` generator, cycles, and boundary relation
with that coordinate model and proves the actual quotient has at most two F₂
classes (Lemma 4.3).

The selected proof does not assume an external homology equivalence. It uses
the explicit four-face/six-edge coordinate complex, so “dimension at most
one” is represented by the equivalent finite-F₂ statement that the quotient
has at most two classes. The topological-ball realization, general homology
library bridge, Alexander--Lefschetz duality, deletion retraction, separator
theorem, rigidity, graph-minor, and embedding results remain outside scope.

The three compared declarations have no `sorry` and use only `propext`,
`Quot.sound`, and (for the quotient theorem) `Classical.choice`.
