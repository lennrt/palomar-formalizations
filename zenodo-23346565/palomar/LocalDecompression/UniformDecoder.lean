module
public import LocalDecompression.OracleView
public import LocalDecompression.NamedLocality

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket Reduction QuotientOrientation
open LocalDecompression.OrientationOracle
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Numeric rank in the ID-ordered finite crossing list, with a total default. -/
noncomputable def rankIn (s : Finset (NamedPair V)) (e : NamedPair V) : ℕ := by
  classical
  exact if he : e ∈ s then (orderedSlots s ⟨e, he⟩).val else 0

/-- The finite parallel-pairing rule: opposite owners for the paired halves;
only the possible last unpaired edge reads the residual orientation bit. -/
noncomputable def pairedDirection (s : Finset (NamedPair V)) (a b : V)
    (h : a ≠ b) (bit : Fin 2) (e : NamedPair V) : Fin 2 :=
  let p := cellPair a b h
  let j := rankIn s e
  let owner := if j < s.card / 2 ∨ (2 * (s.card / 2) ≤ j ∧ bit = 0)
    then p.val.1 else p.val.2
  if owner = a then 0 else 1

theorem pairedDirection_eq_blockOwner (s : Finset (NamedPair V)) (a b : V)
    (h : a ≠ b) (bit : Fin 2) (e : NamedPair V) (he : e ∈ s) :
    pairedDirection s a b h bit e =
      if blockOwner (cellPair a b h) s.card bit (orderedSlots s ⟨e, he⟩) = a then 0 else 1 := by
  classical
  simp only [pairedDirection, rankIn, dite_eq_left he, blockOwner, lowerRank]

/-- Fully specified orientation stage on arbitrary vertex labels. The only
external input is a total finite-view rule; global topology, marker sets, or
advice do not enter its interface. Uncovered/internal cases have fixed defaults. -/
noncomputable def boundedDirections {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (e : NamedPair V) : Fin 2 :=
  match boundedOwner G id R labels (ofLex e).1,
      boundedOwner G id R labels (ofLex e).2 with
  | some a, some b =>
    if h : a = b then 0
    else pairedDirection (crossingPairs G id R labels a b) a b h
      (pairRule F N D c T (boundedResidualGraph G id R labels) id
        (boundedAdvice hq G id R labels) (cellPair a b h)) e
  | _, _ => 0

theorem tailId_cellPair
    (F : Rule) (N D c T : ℕ) (H : SimpleGraph V) (id : V → ℕ)
    (a : V → Fin 2) (u v : V) (h : u ≠ v) :
    tailId F N D c T H id a (cellPair u v h).val.1 (cellPair u v h).val.2 =
      tailId F N D c T H id a u v := by
  by_cases huv : u ≤ v
  · simp [cellPair, min_eq_left huv, max_eq_right huv]
  · simp only [cellPair, min_eq_right (le_of_not_ge huv), max_eq_left (le_of_not_ge huv)]
    exact tailId_swap F N D c T H id a v u

/-- A complete residual output at either endpoint is fixed by the common
physical view, even when global topology and marker sets change. -/
theorem boundedTail_eq_of_graph_view_near {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (center : V) (R S : ℕ)
    (physical : SameGraphView G H center (S+((2*R+1)*T+((R+1)+R))))
    (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist center w ≤ S+((2*R+1)*T+((R+1)+R)) → x w = y w)
    (u v : V) (hu : G.dist center u ≤ S) (hv : G.dist center v ≤ S) :
    tailId F N D c T (boundedResidualGraph G id R x) id (boundedAdvice hq G id R x) u v =
      tailId F N D c T (boundedResidualGraph H id R y) id (boundedAdvice hq H id R y) u v := by
  have he : ∀ w, G.dist center w ≤ S →
      LocalDecompression.OrientationOracle.view (boundedResidualGraph G id R x) id
        (boundedAdvice hq G id R x) T w =
      LocalDecompression.OrientationOracle.view (boundedResidualGraph H id R y) id
        (boundedAdvice hq H id R y) T w := by
    intro w hw
    apply boundedResidual_oracle_view_eq hq G H hG hH id hinj w R T
      (nearby_view G H hG hH center S _ physical w hw) x y
    intro z hz
    exact hlabels z (le_trans (hG.dist_triangle (u := center) (v := w) (w := z)) (by omega))
  unfold tailId output
  rw [he u hu, he v hv]

/-- The actual paired orientation is determined by a bounded physical view.
There is no coverage, root separation, correctness or good-advice hypothesis. -/
theorem boundedDirections_eq_of_graph_view_near {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (center : V) (R S : ℕ)
    (physical : SameGraphView G H center ((S+R)+((2*R+1)*T+((R+1)+R))))
    (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist center w ≤ (S+R)+((2*R+1)*T+((R+1)+R)) → x w = y w)
    (e : NamedPair V)
    (hl : G.dist center (ofLex e).1 ≤ S) (hr : G.dist center (ofLex e).2 ≤ S) :
    boundedDirections hq F N D c T G id R x e =
      boundedDirections hq F N D c T H id R y e := by
  have ho : ∀ v, G.dist center v ≤ S →
      boundedOwner G id R x v = boundedOwner H id R y v := by
    intro v hv
    apply boundedOwner_eq_of_graph_view G H hG hH id hinj v R
      (nearby_view G H hG hH center S R (physical.restrict hG hH (by omega)) v hv) x y
    intro z hz
    have hd := hG.dist_triangle (u := center) (v := v) (w := z)
    rw [hlabels z (by omega)]
  have hlo := ho (ofLex e).1 hl
  have hro := ho (ofLex e).2 hr
  unfold boundedDirections
  rw [← hlo, ← hro]
  cases hol : boundedOwner G id R x (ofLex e).1 with
  | none => rfl
  | some a =>
    cases hor : boundedOwner G id R x (ofLex e).2 with
    | none => rfl
    | some b =>
      by_cases hab : a = b
      · simp only [hab, dite_true]
      · simp only [dite_eq_right hab]
        have ha : G.dist center a ≤ S+R := by
          have hd := owner_distance G id hinj R x hol
          have ht := hG.dist_triangle (u := center) (v := (ofLex e).1) (w := a)
          rw [G.dist_comm (u := (ofLex e).1) (v := a)] at ht
          omega
        have hb : G.dist center b ≤ S+R := by
          have hd := owner_distance G id hinj R x hor
          have ht := hG.dist_triangle (u := center) (v := (ofLex e).2) (w := b)
          rw [G.dist_comm (u := (ofLex e).2) (v := b)] at ht
          omega
        have hs : crossingPairs G id R x a b = crossingPairs H id R y a b := by
          apply crossingPairs_eq_of_graph_view G H hG hH id hinj a b R
            (nearby_view G H hG hH center (S+R) ((R+1)+R)
              (physical.restrict hG hH (by omega)) a ha) x y
          intro w hw
          rw [hlabels w (le_trans (hG.dist_triangle (u := center) (v := a) (w := w)) (by omega))]
        have ht := boundedTail_eq_of_graph_view_near hq F N D c T G H hG hH id hinj
          center R (S+R) physical x y hlabels a b ha hb
        have hbit : pairRule F N D c T (boundedResidualGraph G id R x) id
            (boundedAdvice hq G id R x) (cellPair a b hab) =
            pairRule F N D c T (boundedResidualGraph H id R y) id
            (boundedAdvice hq H id R y) (cellPair a b hab) := by
          unfold pairRule
          rw [tailId_cellPair, tailId_cellPair, ht]
        rw [hs, hbit]

/-- One total decoder for all physical topologies and marker patterns.
All graph information reaching the supplied oracle is in explicit finite views. -/
noncomputable def uniformDecode {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R d : ℕ) (labels : V → Fin (q+1)) (e : NamedPair V) : Fin 2 :=
  boundedPairDecode hq G id R d labels
    (boundedDirections hq F N D c T G id R labels) e

def decodeRadius (R T : ℕ) : ℕ := (3*R+2)+(2*R+1)*(T+1)

/-- Uniform cross-topology, cross-marker label-locality of the complete
specified decoder on arbitrary inputs. This is conditional only on supplying
a total finite-view rule, not on good advice, coverage, separation or recovery. -/
theorem uniformDecode_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R d : ℕ)
    (x y : V → Fin (q+1)) (e : NamedPair V)
    (physical : SameGraphView G H (ofLex e).1 (decodeRadius R T))
    (hlabels : ∀ w, G.dist (ofLex e).1 w ≤ decodeRadius R T → x w = y w) :
    uniformDecode hq F N D c T G id R d x e =
      uniformDecode hq F N D c T H id R d y e := by
  have hradius : ((2*R+2)+R)+((2*R+1)*T+((R+1)+R)) = decodeRadius R T := by
    unfold decodeRadius
    ring
  apply boundedPairDecode_eq_of_graph_view hq G H hG hH id hinj R d x y
    (boundedDirections hq F N D c T G id R x)
    (boundedDirections hq F N D c T H id R y) e
    (physical.restrict hG hH (by unfold decodeRadius; omega))
    (fun w hw => hlabels w (by unfold decodeRadius; omega))
  intro p hp hleft hright
  apply boundedDirections_eq_of_graph_view_near hq F N D c T G H hG hH id hinj
    (ofLex e).1 R (2*R+2) (by simpa only [hradius] using physical) x y
    (by simpa only [hradius] using hlabels) p hleft hright

end LocalDecompression.FiniteView
