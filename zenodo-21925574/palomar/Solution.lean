/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Formalization authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Palomar ambient-bridge upgrade: 2026-08-20.
-/
import K331Tutte.AmbientFourClique
import K331Tutte.CockadeLinkless

set_option autoImplicit true

namespace K331Tutte.FiniteHomology.Ambient

theorem encoded_induced_four_pair_admissible
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    Admissible (encodePair (inducedPair P L)) := by
  exact encoded_induced_four_pair_admissible_source P L hBT

theorem induced_four_coordinate_chain_identification
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    let Q := inducedPair P L
    let c := encodePair Q
    actualRelativeFaces Q = relativeFaces c ∧
      (∀ z, ActualRelativeCycle Q z ↔ RelativeCycle c z) ∧
      actualD3Boundary Q = d3Boundary c ∧
      (∀ x y, ActualHomologous Q x y ↔ Homologous c x y) := by
  exact induced_four_coordinate_chain_identification_source P L hBT

theorem induced_four_clique_relative_homology_bound
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    ActualHomologyDimensionAtMostOne (inducedPair P L) := by
  exact induced_four_clique_relative_homology_bound_source P L hBT

end K331Tutte.FiniteHomology.Ambient

namespace K331Tutte.Cockades

open SimpleGraph

variable {V : Type*}

theorem attachment_reachable_transfer
    (X A : SimpleGraph V) (s t : Set V) (R : Finset V)
    (h : K4Attachment X A s t R) (S : Set V) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hus : u ∉ S) (hvs : v ∉ S)
    (hreach : (deleteVerts (X ⊔ A) S).Reachable u v) :
    (deleteVerts X S).Reachable u v := by
  exact attachment_reachable_transfer_source X A s t R h S hu hv hus hvs hreach

theorem safe_cockade_linkless
    (Atom : SimpleGraph V → Set V → Prop) (nIL : SimpleGraph V → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph V) (s : Set V), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph V) (s : Set V), Atom A s →
      ∃ T : Finset V, (↑T : Set V) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph V) (s t : Set V) (R : Finset V),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set V) → nIL (X ⊔ A))
    {G : SimpleGraph V} {s : Set V} (hG : IsCockade Atom G s)
    (hsep : ∀ R : Finset V, IsFourClique G R → (∃ x ∈ s, x ∉ (↑R : Set V)) →
      TwoComponentsAfterDeletion G s (↑R : Set V)) :
    nIL G := by
  exact safe_cockade_linkless_source Atom nIL hatom_nIL hatom_big hHLS hG hsep

#print axioms K331Tutte.Cockades.attachment_reachable_transfer
#print axioms K331Tutte.Cockades.safe_cockade_linkless

end K331Tutte.Cockades
