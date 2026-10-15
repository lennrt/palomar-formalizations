module
public import LocalDecompression.CrossingBridge
public import LocalDecompression.Padding
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
@[expose] public section
namespace LocalDecompression.FiniteView
open MarkerLocality QuotientOrientation
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem boundedResidualGraph_adj_roots_iff {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (c d : roots) :
    (boundedResidualGraph G id R labels).Adj c.val d.val ↔
      (residualGraph (graphPresentation G) part).Adj c d := by
  constructor
  · rintro ⟨hne,hcard⟩
    have hne' : c ≠ d := fun h => hne (congrArg Subtype.val h)
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · let p : CellPair roots := ⟨(c,d),hlt⟩
      refine ⟨p,?_,Or.inl ⟨rfl,rfl⟩⟩
      have hc := crossingPairs_card_eq_multiplicity G roots part id R labels hpart p
      exact hc ▸ hcard
    · let p : CellPair roots := ⟨(d,c),hlt⟩
      refine ⟨p,?_,Or.inr ⟨rfl,rfl⟩⟩
      have hc := crossingPairs_card_eq_multiplicity G roots part id R labels hpart p
      rw [crossingPairs_symm] at hcard
      exact hc ▸ hcard
  · rintro ⟨p,hp,hends | hends⟩
    · rcases hends with ⟨rfl,rfl⟩
      refine ⟨fun h => (ne_of_lt p.property) (Subtype.ext h),?_⟩
      rw [crossingPairs_card_eq_multiplicity G roots part id R labels hpart p]
      exact hp
    · rcases hends with ⟨rfl,rfl⟩
      refine ⟨fun h => (ne_of_lt p.property) (Subtype.ext h.symm),?_⟩
      rw [crossingPairs_symm,crossingPairs_card_eq_multiplicity G roots part id R labels hpart p]
      exact hp

theorem boundedResidualGraph_nonroot_isolated {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (c : V) (hc : c ∉ roots) (d : V) :
    ¬ (boundedResidualGraph G id R labels).Adj c d := by
  intro hadj
  have hpos : 0 < (crossingPairs G id R labels c d).card := by
    have hp := hadj.2
    omega
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  obtain ⟨_,⟨hl,hr⟩ | ⟨hl,hr⟩⟩ := (mem_crossingPairs _ _ _ _ _ _ _).mp he
  · have h := Option.some.inj ((hpart _).symm.trans hl)
    exact hc (h ▸ (part (ofLex e).1).property)
  · have h := Option.some.inj ((hpart _).symm.trans hr)
    exact hc (h ▸ (part (ofLex e).2).property)

/-- On covered inputs, the ambient bounded quotient is exactly the old root
quotient with all nonroots made isolated. Thus both see the same finite oracle
records with the same IDs and encoded root advice. -/
theorem boundedResidualGraph_eq_onOriginal {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val) :
    boundedResidualGraph G id R labels =
      Padding.onOriginal roots (residualGraph (graphPresentation G) part) := by
  ext c d
  by_cases hc : c ∈ roots
  · by_cases hd : d ∈ roots
    · exact (boundedResidualGraph_adj_roots_iff G roots part id R labels hpart ⟨c,hc⟩ ⟨d,hd⟩).trans
        (Padding.onOriginal_adj roots (residualGraph (graphPresentation G) part) ⟨c,hc⟩ ⟨d,hd⟩).symm
    · constructor
      · intro h
        exact False.elim (boundedResidualGraph_nonroot_isolated G roots part id R labels hpart d hd c h.symm)
      · intro h
        exact False.elim (Padding.nonroot_isolated roots (residualGraph (graphPresentation G) part) d hd c h.symm)
  · constructor
    · intro h
      exact False.elim (boundedResidualGraph_nonroot_isolated G roots part id R labels hpart c hc d h)
    · intro h
      exact False.elim (Padding.nonroot_isolated roots (residualGraph (graphPresentation G) part) c hc d h)

end LocalDecompression.FiniteView
