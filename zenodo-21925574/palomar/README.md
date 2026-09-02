# Simpler Graph Conditions for Embedding Tetrahedral Meshes

DOI: [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574)

Formalization: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude). The cited paper is
by Lennart Rudolph alone.

Five declarations are compared, in two layers.

## Structural layer (Section 5), over mathlib `SimpleGraph`

`K331Tutte.Cockades.attachment_reachable_transfer` is Lemma 5.2: when a new
part is attached to an old part along a shared four-clique, two vertices of
the old support that are joined in the glued graph after deleting an arbitrary
vertex set were already joined inside the old part alone. The proof is walk
surgery — each excursion through the new part is replaced by an edge of the
shared clique.

`K331Tutte.Cockades.safe_cockade_linkless` is Proposition 5.3: a graph
generated from atoms by K₄-attachments is linklessly embeddable whenever every
four-clique deletion leaves at most two components. The proof is structural
induction over the cockade, transporting the final graph's separator bound
down the construction by Lemma 5.2.

Linkless embeddability is **not** defined inside Lean. It is an abstract
predicate `nIL` constrained by exactly the two inputs the paper takes from the
literature, both explicit hypotheses of the theorem: atoms are linklessly
embeddable (Lemma 5.1) and the Holst–Lovász–Schrijver four-clique
specialization (Corollary 2.5). The compared theorem is therefore precisely
the paper's *conditional* mechanism, not a claim about linkless embeddability
proved from first principles. Atoms are required to carry at least five
vertices, which is what drives the nonemptiness side condition of the
separator bound.

## Finite layer (Lemmas 7.1 and 4.3)

`encoded_induced_four_pair_admissible`,
`induced_four_coordinate_chain_identification`, and
`induced_four_clique_relative_homology_bound` are the ambient-to-finite bridge
supporting Section 4. They define a finite abstract
simplicial complex and boundary subcomplex, restrict them to an injectively
labelled four-clique, prove the induced pair is admissible under the
boundary-triangle condition (BT), identify the relative `C₂ → C₁` map, `d₃`
generator, cycles, and boundary relation with the four-face/six-edge F₂
coordinate model, and prove the actual quotient has at most two F₂ classes.
"Dimension at most one" is represented by that equivalent finite-F₂
statement. No external homology equivalence is assumed.

## Out of scope

The topological-ball realization, general simplicial/singular homology
equivalence, Alexander–Lefschetz duality, deletion retraction, generic
rigidity, Jørgensen's extremal classification, the Holst–Lovász–Schrijver
theorem itself, graph minors, spatial embeddings, and Alexa's theorem are not
formalized. This matches the paper's own formal-scope statement in Section 7.

All five compared declarations have no `sorry` and use only `propext`,
`Quot.sound`, and `Classical.choice`.
