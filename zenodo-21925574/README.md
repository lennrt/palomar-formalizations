# Simpler Graph Conditions for Embedding Tetrahedral Meshes

DOI: [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), the sole
author of record on the cited Zenodo deposit.

Formalization: Lennart Rudolph, with the automated assistants Sol (OpenAI
Codex) and Fable (Anthropic Claude).

The compared Lean theorem group formalizes the paper's structural mechanism
and its finite support layer.

The structural layer works over mathlib simple graphs.
`attachment_reachable_transfer` is Lemma 5.2: when a new part is attached to
an old part along a clique, two old vertices joined after deleting any vertex
set were already joined inside the old part, proved by walk surgery through
the attachment clique. `safe_cockade_linkless` is Proposition 5.3: a graph
generated from atoms of at least five vertices by K₄-attachments is linklessly
embeddable whenever every four-clique deletion leaves at most two components.
Linkless embeddability enters as an abstract predicate constrained by exactly
the two inputs the paper cites: atoms are linklessly embeddable (Lemma 5.1)
and the Holst–Lovász–Schrijver four-clique specialization (Corollary 2.5),
both explicit hypotheses of the theorem.

The finite layer is the ambient-to-finite bridge retained from the previous
version: an injectively labelled four-clique of a finite simplicial pair
under the boundary-triangle condition (BT) induces an admissible
`FourVertexPair` (Lemma 7.1), identifies exactly with the four-face/six-edge
F₂ coordinate complex, and its relative quotient has at most two classes
(Lemma 4.3).

Generic rigidity, Jørgensen's classification, Alexander–Lefschetz duality,
the Holst–Lovász–Schrijver theorem itself, graph minors, spatial embeddings,
and Alexa's theorem remain external, matching the paper's own formal-scope
statement.

The compared declarations have no `sorry` and use only `propext`,
`Quot.sound`, and `Classical.choice`.
