module
public import LocalDecompression.UniformDecoder
public import LocalDecompression.ResidualBridge

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket Reduction QuotientOrientation
open LocalDecompression.OrientationOracle
variable {V : Type*} [Fintype V] [LinearOrder V]

def mapRootPair (roots : Finset V) (p : CellPair roots) : CellPair V :=
  ⟨(p.val.1.val, p.val.2.val), p.property⟩

theorem mapRootPair_cellPair (roots : Finset V) (a b : roots) (h : a ≠ b)
    (hv : a.val ≠ b.val) :
    mapRootPair roots (cellPair a b h) = cellPair a.val b.val hv := by
  apply Subtype.ext
  by_cases hab : a ≤ b
  · simp [mapRootPair, cellPair, min_eq_left hab, max_eq_right hab,
      min_eq_left (show a.val ≤ b.val from hab), max_eq_right (show a.val ≤ b.val from hab)]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [mapRootPair, cellPair, min_eq_right hba, max_eq_left hba,
      min_eq_right (show b.val ≤ a.val from hba), max_eq_left (show b.val ≤ a.val from hba)]

theorem blockOwner_mapRootPair (roots : Finset V) (p : CellPair roots)
    (n : ℕ) (bit : Fin 2) (i : Fin n) :
    blockOwner (mapRootPair roots p) n bit i = (blockOwner p n bit i).val := by
  unfold blockOwner
  split_ifs <;> rfl

/-- The actual total bounded residual oracle evaluates exactly the same
finite input as the old root-subtype oracle when owners and advice agree. -/
theorem bounded_pairRule_eq_root_pairRule {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (a : roots → Fin 2)
    (hadvice : ∀ v : roots, boundedAdvice hq G id R labels v.val = a v)
    (p : CellPair roots) :
    pairRule F N D c T (boundedResidualGraph G id R labels) id
      (boundedAdvice hq G id R labels) (mapRootPair roots p) =
    pairRule F N D c T (residualGraph (graphPresentation G) part)
      (id ∘ Subtype.val) a p := by
  rw [boundedResidualGraph_eq_onOriginal G roots part id R labels hpart]
  have ht := tailId_image F N D c T (residualGraph (graphPresentation G) part)
    (Padding.onOriginal roots (residualGraph (graphPresentation G) part))
    Subtype.val (original_neighbors roots (residualGraph (graphPresentation G) part))
    (id ∘ Subtype.val) id (fun _ => rfl) a (boundedAdvice hq G id R labels) hadvice p.val.1 p.val.2
  simpa only [pairRule, mapRootPair, Function.comp_apply] using
    congrArg (fun z : ℕ => if z = id p.val.1.val then (0 : Fin 2) else 1) ht

/-- Exact agreement with the supplied encoder's canonical orientation lift.
The bridge concerns the real crossing fibers and their ordered ranks; no
orientation-agreement or payload-recovery hypothesis is assumed. -/
theorem boundedDirections_eq_liftedOrientation {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G : SimpleGraph V) [DecidableRel G.Adj] (roots : Finset V) (part : V → roots)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hpart : ∀ v, boundedOwner G id R labels v = some (part v).val)
    (advice : roots → Fin 2)
    (hadvice : ∀ v : roots, boundedAdvice hq G id R labels v.val = advice v)
    (e : GraphEdge G) :
    boundedDirections hq F N D c T G id R labels (toLex e.val) =
      liftedOrientation (graphPresentation G) part
        (pairRule F N D c T (residualGraph (graphPresentation G) part)
          (id ∘ Subtype.val)) advice e := by
  classical
  let a := part e.val.1
  let b := part e.val.2
  by_cases hab : a = b
  · have hv : a.val = b.val := congrArg Subtype.val hab
    simp only [boundedDirections, hpart, ofLex_toLex]
    change (if h : a.val = b.val then 0 else _) = _
    rw [dite_eq_left hv]
    simp [liftedOrientation, liftedOwner, graphPresentation, a, b, hab]
  · have hv : a.val ≠ b.val := fun h => hab (Subtype.ext h)
    let p : CellPair roots := cellPair a b hab
    let fiber : Parallel (graphPresentation G) part p := ⟨⟨e, hab⟩, rfl⟩
    let s := crossingPairs G id R labels a.val b.val
    have hs : s = crossingPairs G id R labels p.val.1.val p.val.2.val := by
      by_cases hab' : a ≤ b
      · simp [s, p, cellPair, min_eq_left hab', max_eq_right hab']
      · have hba : b ≤ a := le_of_not_ge hab'
        simp only [s, p, cellPair, min_eq_right hba, max_eq_left hba]
        exact crossingPairs_symm G id R labels a.val b.val
    have hc : s.card = multiplicity (graphPresentation G) part p :=
      hs ▸ crossingPairs_card_eq_multiplicity G roots part id R labels hpart p
    have hj : rankIn s (toLex e.val) = (fiberRank (graphPresentation G) part p fiber).val := by
      rw [hs]
      have hm : toLex e.val ∈ crossingPairs G id R labels p.val.1.val p.val.2.val :=
        (parallelCrossingEquiv G roots part id R labels hpart p fiber).property
      simp only [rankIn, dite_eq_left hm]
      exact parallelRank_eq_crossingSlot G roots part id R labels hpart p fiber
    have hbit := bounded_pairRule_eq_root_pairRule hq F N D c T G roots part id R
      labels hpart advice hadvice p
    have hpmap : mapRootPair roots p = cellPair a.val b.val hv :=
      mapRootPair_cellPair roots a b hab hv
    rw [hpmap] at hbit
    have hold : liftedOrientation (graphPresentation G) part
        (pairRule F N D c T (residualGraph (graphPresentation G) part)
          (id ∘ Subtype.val)) advice e =
        if blockOwner p (multiplicity (graphPresentation G) part p)
          (pairRule F N D c T (residualGraph (graphPresentation G) part)
            (id ∘ Subtype.val) advice p)
          (fiberRank (graphPresentation G) part p fiber) = a then 0 else 1 := by
      unfold liftedOrientation liftedOwner
      have hn : part ((graphPresentation G).left e) ≠ part ((graphPresentation G).right e) := hab
      rw [dite_eq_left hn]
      have hi : boundaryIndex (graphPresentation G) part ⟨e, hn⟩ =
          ⟨p, fiberRank (graphPresentation G) part p fiber⟩ := rfl
      simp only [hi]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact False.elim (h₂ h₁)
      · exact False.elim (h₁ h₂)
      · rfl
    rw [hold]
    simp only [boundedDirections, ofLex_toLex, hpart]
    change (if h : a.val = b.val then 0 else _) = _
    rw [dite_eq_right hv]
    rw [hbit]
    unfold pairedDirection
    change (if (if rankIn s (toLex e.val) < s.card / 2 ∨
        (2 * (s.card / 2) ≤ rankIn s (toLex e.val) ∧ _)
      then (cellPair a.val b.val hv).val.1 else (cellPair a.val b.val hv).val.2) = a.val
      then 0 else 1) = _
    rw [hj, hc, ← hpmap]
    change (if blockOwner (mapRootPair roots p) _ _ _ = a.val then 0 else 1) = _
    rw [blockOwner_mapRootPair]
    have heq : ∀ z : roots, z.val = a.val ↔ z = a := fun z =>
      ⟨Subtype.ext, fun h => congrArg Subtype.val h⟩
    simp only [heq]

end LocalDecompression.FiniteView
