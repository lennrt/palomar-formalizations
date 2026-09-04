# Simpler Graph Conditions for Embedding Tetrahedral Meshes

DOI: [10.5281/zenodo.21925574](https://doi.org/10.5281/zenodo.21925574)

Formalization: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude). The cited paper is
by Lennart Rudolph alone.

## The result

Alexa's three-dimensional Tutte embedding theorem (Discrete & Computational
Geometry 73, 2025) requires a tetrahedral mesh graph with neither a `K₆` nor a
`K₃,₃,₁` minor and asks whether the `K₃,₃,₁` exclusion is necessary. Theorem 1.1
of the paper: if `T` is a finite simplicial complex whose realization is a
closed topological 3-ball, `T` satisfies the boundary-triangle condition (BT),
and the 1-skeleton `G` has no `K₆` minor, then `G` is linklessly embeddable and
hence has no `K₃,₃,₁` minor. Corollary 1.2 drops the `K₃,₃,₁` clause from
Alexa's theorem for this mesh class.

The proof has four steps: (1) (BT) and generic 4-rigidity force the extremal
edge count `4|V| - 10`, so Mader and Jørgensen make `G` an MP₁-cockade
(Corollary 3.6); (2) a four-vertex relative `F₂` homology bound (Lemma 4.3)
and relative ball duality give `comp(G - S) ≤ 2` for every four-clique `S`
(Theorem 4.4); (3) `K₄`-attachments never merge old components (Lemma 5.2), so
the separator bound transports down the cockade tree and the four-clique
Holst–Lovász–Schrijver criterion preserves linklessness (Proposition 5.3);
(4) linkless embeddability is minor closed and `K₃,₃,₁` is intrinsically
linked. Steps (2) and (3) are the paper's new mathematics. Six declarations are
compared.

## Theorem 1.1, combinatorial core

`K331Tutte.Bridge.structural_theorem` joins the two layers below. The skeleton
of a finite simplicial pair on `Fin n` is the mathlib `SimpleGraph` whose
distinct vertices are adjacent exactly when their edge is a simplex. Every
four-clique of the skeleton is a labelled four-clique of the pair, Lemma 4.3
applies to it, and the hypothesis `hduality` (Propositions 4.1 and 4.2 with
universal coefficients) converts the homology bound into the component bound
of Theorem 4.4. With `hcockade` (Corollary 3.6), `hHLS` (Corollary 2.5), and
`hatom_nIL` (Lemma 5.1), Proposition 5.3 concludes that the skeleton is
linklessly embeddable. Each hypothesis is one cited theorem.

## Structural layer (Section 5), over mathlib `SimpleGraph`

`K331Tutte.Cockades.attachment_reachable_transfer` is Lemma 5.2: when a new
part is attached to an old part along a shared four-clique, two vertices of
the old support that are joined in the glued graph after deleting an arbitrary
vertex set were already joined inside the old part alone. The proof is walk
surgery: each excursion through the new part is replaced by an edge of the
shared clique.

`K331Tutte.Cockades.safe_cockade_linkless` is Proposition 5.3: a graph
generated from atoms by `K₄`-attachments is linklessly embeddable whenever every
four-clique deletion leaves at most two components. The proof is structural
induction over the cockade, transporting the final graph's separator bound
down the construction by Lemma 5.2.

Linkless embeddability is not defined inside Lean. It is an abstract predicate
`nIL` constrained by exactly the two inputs the paper takes from the
literature, both explicit hypotheses: atoms are linklessly embeddable
(Lemma 5.1) and the Holst–Lovász–Schrijver four-clique specialization
(Corollary 2.5). The compared theorem is therefore the paper's conditional
mechanism, with the cited inputs visible as hypotheses. Atoms carry at least
five vertices, which drives the nonemptiness side condition of the separator
bound.

## Finite layer (Lemmas 7.1 and 4.3)

`encoded_induced_four_pair_admissible`,
`induced_four_coordinate_chain_identification`, and
`induced_four_clique_relative_homology_bound` are the ambient-to-finite bridge
supporting Section 4. They define a finite abstract simplicial complex and
boundary subcomplex on `Fin n`, restrict them to an injectively labelled
four-clique, prove the induced pair is admissible under (BT), identify the
relative `C₂ → C₁` map, `d₃` generator, cycles, and boundary relation with the
four-face, six-edge `F₂` coordinate model, and prove the actual quotient has at
most two `F₂` classes. "Dimension at most one" is represented by that
equivalent finite `F₂` statement. The statements hold for every pair and every
labelled four-clique; the 32,768-encoding census of Section 7 is a regression
check of the same lemma.

## Out of scope

Generic rigidity, Mader's theorem, Jørgensen's classification, the PL topology
of the deletion retraction and relative ball duality, the Holst–Lovász–Schrijver
theorem itself, linkless embeddability of apex graphs, graph minors, spatial
embeddings, and Alexa's theorem are not formalized. Each enters the compared
statements only as an explicit hypothesis, matching the paper's own
formal-scope statement in Section 7.

All six compared declarations have no `sorry` and use only `propext`,
`Quot.sound`, and `Classical.choice`.
