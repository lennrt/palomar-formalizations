/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Formalization: Lennart Rudolph, the responsible author, with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude)
-/
import K331Tutte.AmbientFourClique
import K331Tutte.CockadeLinkless

/-!
# Joining the two layers: the combinatorial core of Theorem 1.1

The 1-skeleton of a finite simplicial complex is a mathlib `SimpleGraph` on
`Fin n`. A four-clique of that skeleton is a labelled four-clique of the
complex, so the relative bound of Lemma 4.3 applies to the pair it induces.
Once the relative ball duality of Section 4 (Propositions 4.1 and 4.2 with
universal coefficients) is supplied as a hypothesis, Theorem 4.4's separator
bound holds for every four-clique, and Proposition 5.3 gives linkless
embeddability. This is the paper's proof of Theorem 1.1 with the cited
external theorems as explicit hypotheses.
-/

namespace K331Tutte.Bridge

open K331Tutte.FiniteHomology K331Tutte.FiniteHomology.Ambient K331Tutte.Cockades

variable {n : Nat}

/-- The 1-skeleton of a finite simplicial complex: two distinct vertices are
adjacent exactly when the edge between them is a simplex. -/
def skeleton (C : FiniteSimplicialComplex n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ C.simplex (EdgeVertexSet u v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by
    rw [C.extensional (a := EdgeVertexSet v u) (b := EdgeVertexSet u v)
      (fun w => show (w = v ∨ w = u) ↔ (w = u ∨ w = v) from or_comm)]
    exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- A four-clique of the skeleton, read as a labelled four-clique of the pair. -/
noncomputable def labelledOfFourClique (P : FiniteSimplicialPair n) (R : Finset (Fin n))
    (hR : IsFourClique (skeleton P.ambient) R) : LabelledFourClique P where
  label i := (R.equivFin.symm (Fin.cast hR.1.symm i)).1
  injective := by
    intro i j h
    exact Fin.cast_injective _ (R.equivFin.symm.injective (Subtype.val_injective h))
  clique := by
    intro i j hij
    have hne : (R.equivFin.symm (Fin.cast hR.1.symm i)).1 ≠
        (R.equivFin.symm (Fin.cast hR.1.symm j)).1 := by
      intro h
      exact hij (Fin.cast_injective _ (R.equivFin.symm.injective (Subtype.val_injective h)))
    have hadj := hR.2 (Finset.mem_coe.2 (R.equivFin.symm (Fin.cast hR.1.symm i)).2)
      (Finset.mem_coe.2 (R.equivFin.symm (Fin.cast hR.1.symm j)).2) hne
    exact hadj.2

theorem range_labelledOfFourClique (P : FiniteSimplicialPair n) (R : Finset (Fin n))
    (hR : IsFourClique (skeleton P.ambient) R) :
    Set.range (labelledOfFourClique P R hR).label = (↑R : Set (Fin n)) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact Finset.mem_coe.2 (R.equivFin.symm (Fin.cast hR.1.symm i)).2
  · intro hx
    refine ⟨Fin.cast hR.1 (R.equivFin ⟨x, Finset.mem_coe.1 hx⟩), ?_⟩
    simp [labelledOfFourClique]

/-- Theorem 1.1, combinatorial core: with Corollary 3.6, the Section 4 duality,
Corollary 2.5, and Lemma 5.1 as hypotheses, the skeleton of a (BT) pair is
linklessly embeddable. -/
theorem structural_theorem_source (P : FiniteSimplicialPair n)
    (hBT : BoundaryTriangleCondition P)
    (Atom : SimpleGraph (Fin n) → Set (Fin n) → Prop) (nIL : SimpleGraph (Fin n) → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph (Fin n)) (s : Set (Fin n)), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph (Fin n)) (s : Set (Fin n)), Atom A s →
      ∃ T : Finset (Fin n), (↑T : Set (Fin n)) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph (Fin n)) (s t : Set (Fin n)) (R : Finset (Fin n)),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set (Fin n)) → nIL (X ⊔ A))
    (hcockade : IsCockade Atom (skeleton P.ambient) Set.univ)
    (hduality : ∀ L : LabelledFourClique P, (∃ x : Fin n, x ∉ Set.range L.label) →
      ActualHomologyDimensionAtMostOne (inducedPair P L) →
      TwoComponentsAfterDeletion (skeleton P.ambient) Set.univ (Set.range L.label)) :
    nIL (skeleton P.ambient) := by
  refine safe_cockade_linkless_source Atom nIL hatom_nIL hatom_big hHLS hcockade ?_
  intro R hR hne
  have hrange := range_labelledOfFourClique P R hR
  have h := hduality (labelledOfFourClique P R hR)
    (by
      obtain ⟨x, -, hx⟩ := hne
      exact ⟨x, by rw [hrange]; exact hx⟩)
    (induced_four_clique_relative_homology_bound_source P (labelledOfFourClique P R hR) hBT)
  rw [hrange] at h
  exact h

#print axioms structural_theorem_source

end K331Tutte.Bridge
