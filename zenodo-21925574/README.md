# Simpler Graph Conditions for Embedding Tetrahedral Meshes

DOI: [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), the sole
author of record on the cited Zenodo deposit.

Formalization: Lennart Rudolph, with the automated assistants Sol (OpenAI
Codex) and Fable (Anthropic Claude).

Alexa's three-dimensional Tutte embedding theorem (Discrete & Computational
Geometry 73, 2025) requires the graph of a tetrahedral mesh to have neither a
`K₆` nor a `K₃,₃,₁` minor, and asks whether the second exclusion is necessary.
The paper proves that it is redundant for finite simplicial complexes whose
realization is a closed topological 3-ball and which satisfy the
boundary-triangle condition (BT): if the 1-skeleton `G` has no `K₆` minor, then
`G` is linklessly embeddable and so has no `K₃,₃,₁` minor (Theorem 1.1), and
Alexa's theorem applies to such meshes without the `K₃,₃,₁` clause
(Corollary 1.2).

The Palomar project compares six declarations. They prove the paper's new
combinatorial mathematics over mathlib simple graphs and finite simplicial
complexes and compose it into Theorem 1.1, with the cited theorems as named
hypotheses.

`K331Tutte.Bridge.structural_theorem` is the combinatorial core of
Theorem 1.1. The skeleton of a finite simplicial pair on `Fin n` is a mathlib
`SimpleGraph`. Every four-clique of the skeleton is a labelled four-clique of
the pair, Lemma 4.3 bounds the relative `F₂` homology it induces, the
hypothesis `hduality` (Propositions 4.1 and 4.2 with universal coefficients)
turns that bound into the separator bound of Theorem 4.4, and Proposition 5.3
concludes that the skeleton is linklessly embeddable. The remaining hypotheses
are Corollary 3.6 (rigidity, Mader, and Jørgensen make the skeleton an
MP₁-cockade), Corollary 2.5 (the four-clique Holst–Lovász–Schrijver
criterion), and Lemma 5.1 (atoms are linklessly embeddable).

`K331Tutte.Cockades.attachment_reachable_transfer` is Lemma 5.2: when a new
part is attached to an old part along a clique, two old vertices joined after
deleting any vertex set were already joined inside the old part, proved by
walk surgery through the attachment clique. `K331Tutte.Cockades.safe_cockade_linkless`
is Proposition 5.3: a graph generated from atoms of at least five vertices by
`K₄`-attachments is linklessly embeddable whenever every four-clique deletion
leaves at most two components. Linkless embeddability enters as an abstract
predicate constrained by exactly the two inputs the paper cites, Lemma 5.1
and Corollary 2.5, both explicit hypotheses.

`K331Tutte.FiniteHomology.Ambient.encoded_induced_four_pair_admissible`,
`induced_four_coordinate_chain_identification`, and
`induced_four_clique_relative_homology_bound` are Lemma 7.1, the
identification of the induced relative chain complex with its four-face,
six-edge `F₂` coordinate model, and Lemma 4.3. They hold for every finite
simplicial pair and every injectively labelled four-clique under (BT). The
32,768-encoding census in Section 7 of the paper is a regression check of
Lemma 4.3; the compared statement is the lemma itself.

Generic rigidity, Mader's theorem, Jørgensen's classification, the PL topology
of Propositions 4.1 and 4.2, the Holst–Lovász–Schrijver theorem, linkless
embeddability of apex graphs, graph minors, spatial embeddings, and Alexa's
theorem remain external, matching the paper's own formal-scope statement.

The compared declarations have no `sorry` and use only `propext`,
`Quot.sound`, and `Classical.choice`.
