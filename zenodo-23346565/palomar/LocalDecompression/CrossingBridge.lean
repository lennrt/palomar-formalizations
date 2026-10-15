module
public import LocalDecompression.QuotientView
public import LocalDecompression.QuotientOrientation

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket QuotientOrientation

/-- Equality with a canonical cell pair is exactly the two endpoint orders. -/
theorem pairOf_eq_iff_endpoints
    {V E C : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
    [Fintype C] [LinearOrder C]
    (G : EdgePresentation V E) (part : V → C) (e : BoundaryEdge G part) (p : CellPair C) :
    pairOf G part e = p ↔
      ((part (G.left e.val) = p.val.1 ∧ part (G.right e.val) = p.val.2) ∨
       (part (G.left e.val) = p.val.2 ∧ part (G.right e.val) = p.val.1)) := by
  constructor
  · intro h
    simpa only [h] using pairOf_endpoints G part e
  · rintro (⟨hl,hr⟩ | ⟨hl,hr⟩)
    · apply Subtype.ext
      simp only [pairOf, cellPair, hl, hr, min_eq_left p.property.le,
        max_eq_right p.property.le]
    · apply Subtype.ext
      simp only [pairOf, cellPair, hl, hr, min_eq_right p.property.le,
        max_eq_left p.property.le]

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- On covered labels, the actual bounded crossing fiber is order-isomorphic
to the original library's parallel-edge fiber. This preserves canonical ranks,
not only multiplicities. -/
noncomputable def parallelCrossingEquiv {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (p : CellPair roots) :
    @OrderIso (Parallel (graphPresentation G) part p)
      {e : NamedPair V // e ∈ crossingPairs G id R labels p.val.1.val p.val.2.val}
      (inferInstance : LinearOrder (Parallel (graphPresentation G) part p)).toLE inferInstance := by
  classical
  refine
    { toFun := fun e => ⟨toLex e.val.val.val, ?_⟩
      invFun := fun z => ?_
      left_inv := ?_
      right_inv := ?_
      map_rel_iff' := ?_ }
  · apply (mem_crossingPairs G id R labels _ _ _).mpr
    refine ⟨(mem_actualPairs G _).mpr e.val.val.property, ?_⟩
    have ends := (pairOf_eq_iff_endpoints (graphPresentation G) part e.val p).mp e.property
    change ((boundedOwner G id R labels e.val.val.val.1 = some p.val.1.val ∧
      boundedOwner G id R labels e.val.val.val.2 = some p.val.2.val) ∨
      (boundedOwner G id R labels e.val.val.val.1 = some p.val.2.val ∧
      boundedOwner G id R labels e.val.val.val.2 = some p.val.1.val))
    rcases ends with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · exact Or.inl ⟨(hpart _).trans (congrArg (fun c : roots => some c.val) hl),
        (hpart _).trans (congrArg (fun c : roots => some c.val) hr)⟩
    · exact Or.inr ⟨(hpart _).trans (congrArg (fun c : roots => some c.val) hl),
        (hpart _).trans (congrArg (fun c : roots => some c.val) hr)⟩
  · have hz := (mem_crossingPairs G id R labels p.val.1.val p.val.2.val z.val).mp z.property
    let e : GraphEdge G := ⟨ofLex z.val, (mem_actualPairs G z.val).mp hz.1⟩
    have ends : ((part e.val.1 = p.val.1 ∧ part e.val.2 = p.val.2) ∨
        (part e.val.1 = p.val.2 ∧ part e.val.2 = p.val.1)) := by
      rcases hz.2 with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · exact Or.inl ⟨Subtype.ext (Option.some.inj ((hpart _).symm.trans hl)),
          Subtype.ext (Option.some.inj ((hpart _).symm.trans hr))⟩
      · exact Or.inr ⟨Subtype.ext (Option.some.inj ((hpart _).symm.trans hl)),
          Subtype.ext (Option.some.inj ((hpart _).symm.trans hr))⟩
    have he : part e.val.1 ≠ part e.val.2 := by
      rcases ends with ⟨hl,hr⟩ | ⟨hl,hr⟩
      · simpa only [hl, hr] using ne_of_lt p.property
      · simpa only [hl, hr] using (ne_of_lt p.property).symm
    exact ⟨⟨e,he⟩, (pairOf_eq_iff_endpoints (graphPresentation G) part ⟨e,he⟩ p).mpr ends⟩
  · intro e
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro e
    apply Subtype.ext
    rfl
  · intro a b
    rfl

/-- The parity used by the total bounded quotient is exactly the parity of
the original graph-native library multiplicity on valid covered labels. -/
theorem crossingPairs_card_eq_multiplicity {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (p : CellPair roots) :
    (crossingPairs G id R labels p.val.1.val p.val.2.val).card =
      multiplicity (graphPresentation G) part p := by
  have hc := Fintype.card_congr (parallelCrossingEquiv G roots part id R labels hpart p).toEquiv
  simpa only [QuotientOrientation.multiplicity, Fintype.card_coe, Fintype.card_eq_nat_card, Nat.card_eq_finsetCard] using hc.symm


/-- The ordered packet slot of a named crossing edge is exactly its original
parallel-fiber rank; no rank is changed by passing to common edge names. -/
theorem parallelRank_eq_crossingSlot {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (p : CellPair roots) (e : Parallel (graphPresentation G) part p) :
    (Reduction.orderedSlots (crossingPairs G id R labels p.val.1.val p.val.2.val)
      (parallelCrossingEquiv G roots part id R labels hpart p e)).val =
      (fiberRank (graphPresentation G) part p e).val := by
  classical
  let : DecidableEq roots := (inferInstance : LinearOrder roots).toDecidableEq
  let : LE (Parallel (graphPresentation G) part p) :=
    (inferInstance : LinearOrder (Parallel (graphPresentation G) part p)).toLE
  let f := parallelCrossingEquiv G roots part id R labels hpart p
  let s := crossingPairs G id R labels p.val.1.val p.val.2.val
  let ranks := ((Fintype.orderIsoFinOfCardEq (Parallel (graphPresentation G) part p) rfl).trans f).trans
    (s.orderIsoOfFin rfl).symm
  have h := Fin.coe_orderIso_apply ranks
    ((Fintype.orderIsoFinOfCardEq (Parallel (graphPresentation G) part p) rfl).symm e)
  simp only [ranks, OrderIso.trans_apply, OrderIso.apply_symm_apply, f, s,
    Reduction.orderedSlots, fiberRank, OrderIso.coe_toEquiv] at h ⊢
  convert h using 1

end LocalDecompression.FiniteView
