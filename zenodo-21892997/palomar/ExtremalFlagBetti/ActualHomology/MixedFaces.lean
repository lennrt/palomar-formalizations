/-
Literal mixed triangular faces for the canonical unordered chain model used
in the graph-join proof.

Authors: Lennart Rudolph, Sol, Fable
-/

import Mathlib

open Finset SimpleGraph

namespace ExtremalUnorderedMixedFaces

abbrev F₂ := ZMod 2

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W

lemma f2_add_self {M : Type*} [AddCommGroup M] [Module F₂ M]
    (x : M) : x + x = 0 := by
  calc
    x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
    _ = ((1 : F₂) + 1) • x := by rw [add_smul]
    _ = 0 := by
      have htwo : (1 : F₂) + 1 = 0 := by decide
      rw [htwo, zero_smul]

abbrev FlagEdge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}
abbrev FlagTriangle (G : SimpleGraph V) :=
  {s : Finset V // s.card = 3 ∧ G.IsClique s}
abbrev FlagChain0 (V : Type*) := V →₀ F₂
abbrev FlagChain1 (G : SimpleGraph V) := FlagEdge G →₀ F₂
abbrev FlagChain2 (G : SimpleGraph V) := FlagTriangle G →₀ F₂

noncomputable def triangleBoundary (G : SimpleGraph V)
    (t : FlagTriangle G) : FlagChain1 G := by
  classical
  let es : Finset (Sym2 V) :=
    t.1.sym2.filter (fun e ↦ e ∈ G.edgeSet)
  exact es.attach.sum fun e ↦
    Finsupp.single ⟨e.1, (mem_filter.mp e.2).2⟩ 1

noncomputable def flagD2 (G : SimpleGraph V) :
    FlagChain2 G →ₗ[F₂] FlagChain1 G :=
  Finsupp.linearCombination F₂ (triangleBoundary G)

/-- The canonical vertex finset of a left mixed face. -/
def leftMixedVertices (e : Sym2 V) (w : W) : Finset (V ⊕ W) :=
  Sym2.lift
    ⟨fun u v ↦ {Sum.inl u, Sum.inl v, Sum.inr w},
      fun u v ↦ by
        ext x
        simp only [mem_insert, mem_singleton]
        tauto⟩ e

/-- The literal face consisting of a left internal edge and one right
vertex.  No representative or vertex order is chosen. -/
def leftMixedTriangle (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) (w : W) : FlagTriangle (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨leftMixedVertices e w, ?_⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : Gᶜ.Adj u v := by simpa using he
      have huv' : u ≠ v ∧ ¬G.Adj u v := (G.compl_adj u v).mp huv
      constructor
      · simp [leftMixedVertices, huv.ne]
      · rw [SimpleGraph.isClique_iff]
        simp [leftMixedVertices, Set.Pairwise, SimpleGraph.compl_adj,
          SimpleGraph.sum]
        constructor
        · intro _
          exact huv'
        · intro hne
          exact ⟨hne, fun hvu ↦ huv'.2 (G.symm hvu)⟩

/-- The canonical vertex finset of a right mixed face. -/
def rightMixedVertices (v : V) (e : Sym2 W) : Finset (V ⊕ W) :=
  Sym2.lift
    ⟨fun w w' ↦ {Sum.inl v, Sum.inr w, Sum.inr w'},
      fun w w' ↦ by
        ext x
        simp only [mem_insert, mem_singleton]
        tauto⟩ e

/-- The literal face consisting of one left vertex and a right internal
edge.  No representative or vertex order is chosen. -/
def rightMixedTriangle (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : FlagEdge Hᶜ) : FlagTriangle (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨rightMixedVertices v e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      have hww' : Hᶜ.Adj w w' := by simpa using he
      have hww'' : w ≠ w' ∧ ¬H.Adj w w' := (H.compl_adj w w').mp hww'
      constructor
      · simp [rightMixedVertices, hww'.ne]
      · rw [SimpleGraph.isClique_iff]
        simp [rightMixedVertices, Set.Pairwise, SimpleGraph.compl_adj,
          SimpleGraph.sum]
        constructor
        · intro _
          exact hww''
        · intro hne
          exact ⟨hne, fun hw'w ↦ hww''.2 (H.symm hw'w)⟩

/-- Linear extension of the left mixed faces. -/
noncomputable def leftMixedFaceMap (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (FlagChain1 Gᶜ) (FlagChain0 W) →ₗ[F₂]
      FlagChain2 (G ⊕g H)ᶜ :=
  TensorProduct.lift
    (Finsupp.lsum F₂ (fun e ↦
      LinearMap.toSpanSingleton F₂
        (FlagChain0 W →ₗ[F₂] FlagChain2 (G ⊕g H)ᶜ)
        (Finsupp.linearCombination F₂ (fun w ↦
          Finsupp.single (leftMixedTriangle G H e w) (1 : F₂)))))

/-- Linear extension of the right mixed faces. -/
noncomputable def rightMixedFaceMap (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (FlagChain0 V) (FlagChain1 Hᶜ) →ₗ[F₂]
      FlagChain2 (G ⊕g H)ᶜ :=
  TensorProduct.lift
    (Finsupp.lsum F₂ (fun v ↦
      LinearMap.toSpanSingleton F₂
        (FlagChain1 Hᶜ →ₗ[F₂] FlagChain2 (G ⊕g H)ᶜ)
        (Finsupp.linearCombination F₂ (fun e ↦
          Finsupp.single (rightMixedTriangle G H v e) (1 : F₂)))))

/-- Both mixed-face families together. -/
noncomputable def mixedFaceMap (G : SimpleGraph V) (H : SimpleGraph W) :
    (TensorProduct F₂ (FlagChain1 Gᶜ) (FlagChain0 W) ×
      TensorProduct F₂ (FlagChain0 V) (FlagChain1 Hᶜ)) →ₗ[F₂]
      FlagChain2 (G ⊕g H)ᶜ :=
  (leftMixedFaceMap G H).coprod (rightMixedFaceMap G H)

/-! ### Literal degree-one boundaries of the mixed faces -/

/-- A left internal complement edge, viewed in the joined complement. -/
def leftJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) : FlagEdge (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨Sym2.map Sum.inl e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : Gᶜ.Adj u v := by simpa using he
      simp [SimpleGraph.compl_adj, SimpleGraph.sum,
        (G.compl_adj u v).mp huv]

/-- A right internal complement edge, viewed in the joined complement. -/
def rightJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Hᶜ) : FlagEdge (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨Sym2.map Sum.inr e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      have hww' : Hᶜ.Adj w w' := by simpa using he
      simp [SimpleGraph.compl_adj, SimpleGraph.sum,
        (H.compl_adj w w').mp hww']

/-- Every cross pair is an edge of the joined complement. -/
def crossJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) : FlagEdge (G ⊕g H)ᶜ :=
  ⟨s(Sum.inl v, Sum.inr w), by
    simp [SimpleGraph.compl_adj, SimpleGraph.sum]⟩

/-- Expected literal boundary of a left mixed face. -/
def leftCrossBoundary (G : SimpleGraph V) (H : SimpleGraph W)
    (e : Sym2 V) (w : W) : FlagChain1 (G ⊕g H)ᶜ :=
  Sym2.lift
    ⟨fun u v ↦
        Finsupp.single (crossJoinedEdge G H u w) 1 +
          Finsupp.single (crossJoinedEdge G H v w) 1,
      fun u v ↦ by dsimp; rw [add_comm]⟩ e

/-- Expected literal boundary of a left mixed face. -/
def leftMixedBoundaryExpected
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) (w : W) : FlagChain1 (G ⊕g H)ᶜ :=
  Finsupp.single (leftJoinedEdge G H e) 1 +
    leftCrossBoundary G H e.1 w

/-- Expected literal boundary of a right mixed face. -/
def rightCrossBoundary (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : Sym2 W) : FlagChain1 (G ⊕g H)ᶜ :=
  Sym2.lift
    ⟨fun w w' ↦
        Finsupp.single (crossJoinedEdge G H v w) 1 +
          Finsupp.single (crossJoinedEdge G H v w') 1,
      fun w w' ↦ by dsimp; rw [add_comm]⟩ e

/-- Expected literal boundary of a right mixed face. -/
def rightMixedBoundaryExpected
    (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : FlagEdge Hᶜ) : FlagChain1 (G ⊕g H)ᶜ :=
  Finsupp.single (rightJoinedEdge G H e) 1 +
    rightCrossBoundary G H v e.1

omit [Fintype V] in
private lemma attachedEdgeSingleSum_apply
    (K : SimpleGraph V) (s : Finset (Sym2 V))
    (hs : ∀ e ∈ s, e ∈ K.edgeSet) (f : FlagEdge K) :
    (∑ c ∈ s.attach,
      (Finsupp.single ⟨c.1, hs c.1 c.2⟩ (1 : F₂) : FlagChain1 K)) f =
      if f.1 ∈ s then 1 else 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  by_cases hf : f.1 ∈ s
  · let c : {e // e ∈ s} := ⟨f.1, hf⟩
    rw [if_pos hf, Finset.sum_eq_single_of_mem c (by simp [c])]
    · simp [c]
    · intro b hb hbc
      simp only [Finsupp.single_apply]
      rw [if_neg]
      intro h
      apply hbc
      apply Subtype.ext
      exact congrArg (fun q : FlagEdge K ↦ q.1) h
  · rw [if_neg hf]
    apply Finset.sum_eq_zero
    intro c hc
    simp only [Finsupp.single_apply]
    rw [if_neg]
    intro h
    apply hf
    have hval : c.1 = f.1 := congrArg Subtype.val h
    rw [← hval]
    exact c.2

/-- Coefficient description of the literal filtered-`sym2` face boundary. -/
lemma triangleBoundary_apply (K : SimpleGraph V) (t : FlagTriangle K)
    (f : FlagEdge K) :
    triangleBoundary K t f = if f.1 ∈ t.1.sym2 then 1 else 0 := by
  classical
  let es : Finset (Sym2 V) :=
    t.1.sym2.filter (fun e ↦ e ∈ K.edgeSet)
  change (∑ c ∈ es.attach,
    (Finsupp.single
      ⟨c.1, (Finset.mem_filter.mp c.2).2⟩ (1 : F₂) : FlagChain1 K)) f = _
  rw [attachedEdgeSingleSum_apply K es
    (fun e he ↦ (Finset.mem_filter.mp he).2) f]
  simp [es, f.2]

/-- The source `triangleBoundary` of a left mixed face is exactly its one
internal and two cross edges. -/
lemma triangleBoundary_leftMixedTriangle
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) (w : W) :
    triangleBoundary (G ⊕g H)ᶜ (leftMixedTriangle G H e w) =
      leftMixedBoundaryExpected G H e w := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      ext f
      rw [triangleBoundary_apply]
      rcases f with ⟨f, hf⟩
      induction f using Sym2.inductionOn with
      | _ x y =>
          cases x <;> cases y <;>
            simp [leftMixedTriangle, leftMixedVertices,
              leftMixedBoundaryExpected, leftCrossBoundary,
              leftJoinedEdge, crossJoinedEdge, Finset.mem_sym2_iff,
              Finsupp.single_apply, Subtype.ext_iff] <;> aesop

/-- The corresponding literal boundary formula for a right mixed face. -/
lemma triangleBoundary_rightMixedTriangle
    (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : FlagEdge Hᶜ) :
    triangleBoundary (G ⊕g H)ᶜ (rightMixedTriangle G H v e) =
      rightMixedBoundaryExpected G H v e := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      ext f
      rw [triangleBoundary_apply]
      rcases f with ⟨f, hf⟩
      induction f using Sym2.inductionOn with
      | _ x y =>
          cases x <;> cases y <;>
            simp [rightMixedTriangle, rightMixedVertices,
              rightMixedBoundaryExpected, rightCrossBoundary,
              rightJoinedEdge, crossJoinedEdge, Finset.mem_sym2_iff,
              Finsupp.single_apply, Subtype.ext_iff] <;> aesop

/-- Degree-one boundary generated by the mixed two-faces. -/
noncomputable def mixedBoundaryMap (G : SimpleGraph V) (H : SimpleGraph W) :
    (TensorProduct F₂ (FlagChain1 Gᶜ) (FlagChain0 W) ×
      TensorProduct F₂ (FlagChain0 V) (FlagChain1 Hᶜ)) →ₗ[F₂]
      FlagChain1 (G ⊕g H)ᶜ :=
  (flagD2 (G ⊕g H)ᶜ).comp (mixedFaceMap G H)

omit [Fintype V] [Fintype W] in
@[simp]
lemma leftMixedFaceMap_single_tmul_single
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) (w : W) :
    leftMixedFaceMap G H
        (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single w 1) =
      Finsupp.single (leftMixedTriangle G H e w) 1 := by
  simp [leftMixedFaceMap]

omit [Fintype V] [Fintype W] in
@[simp]
lemma rightMixedFaceMap_single_tmul_single
    (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : FlagEdge Hᶜ) :
    rightMixedFaceMap G H
        (Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single e 1) =
      Finsupp.single (rightMixedTriangle G H v e) 1 := by
  simp [rightMixedFaceMap]

/-- Basis formula used by the left mixed-boundary normalization. -/
lemma mixedBoundaryMap_left_basis
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) (w : W) :
    mixedBoundaryMap G H
        (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single w 1, 0) =
      leftMixedBoundaryExpected G H e w := by
  simp [mixedBoundaryMap, mixedFaceMap, flagD2,
    triangleBoundary_leftMixedTriangle]

/-- Basis formula used by the right mixed-boundary normalization. -/
lemma mixedBoundaryMap_right_basis
    (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : FlagEdge Hᶜ) :
    mixedBoundaryMap G H
        (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single e 1) =
      rightMixedBoundaryExpected G H v e := by
  simp [mixedBoundaryMap, mixedFaceMap, flagD2,
    triangleBoundary_rightMixedTriangle]

/-! ### Every triangular boundary is generated by mixed faces -/

def flagEdgeOfAdj (K : SimpleGraph V) {u v : V} (h : K.Adj u v) :
    FlagEdge K :=
  ⟨s(u, v), K.mem_edgeSet.mpr h⟩

lemma triangleBoundary_eq_three_edges
    (K : SimpleGraph V) (t : FlagTriangle K) {a b c : V}
    (hab : K.Adj a b) (hac : K.Adj a c) (hbc : K.Adj b c)
    (ht : ∀ x, x ∈ t.1 ↔ x = a ∨ x = b ∨ x = c) :
    triangleBoundary K t =
      Finsupp.single (flagEdgeOfAdj K hab) 1 +
      Finsupp.single (flagEdgeOfAdj K hac) 1 +
      Finsupp.single (flagEdgeOfAdj K hbc) 1 := by
  classical
  ext e
  rw [triangleBoundary_apply]
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy : K.Adj x y := K.mem_edgeSet.mp he
      have ht0 : t.1 = {a, b, c} := by
        ext z
        simpa only [Finset.mem_insert, Finset.mem_singleton] using ht z
      simp only [ht0, Finset.mk_mem_sym2_iff]
      simp [flagEdgeOfAdj, Finsupp.single_apply, Subtype.ext_iff]
      aesop

omit [Fintype V] [Fintype W] in
private lemma sum_leftMixedBoundaryExpected_eq_internal
    (G : SimpleGraph V) (H : SimpleGraph W) {a b c : V}
    (hab : Gᶜ.Adj a b) (hac : Gᶜ.Adj a c) (hbc : Gᶜ.Adj b c)
    (w : W) :
    let eab : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hab
    let eac : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hac
    let ebc : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hbc
    leftMixedBoundaryExpected G H eab w +
        leftMixedBoundaryExpected G H eac w +
        leftMixedBoundaryExpected G H ebc w =
      Finsupp.single (leftJoinedEdge G H eab) 1 +
        Finsupp.single (leftJoinedEdge G H eac) 1 +
        Finsupp.single (leftJoinedEdge G H ebc) 1 := by
  dsimp only
  let Aab := Finsupp.single
    (leftJoinedEdge G H (flagEdgeOfAdj Gᶜ hab)) (1 : F₂)
  let Aac := Finsupp.single
    (leftJoinedEdge G H (flagEdgeOfAdj Gᶜ hac)) (1 : F₂)
  let Abc := Finsupp.single
    (leftJoinedEdge G H (flagEdgeOfAdj Gᶜ hbc)) (1 : F₂)
  let xa := Finsupp.single (crossJoinedEdge G H a w) (1 : F₂)
  let xb := Finsupp.single (crossJoinedEdge G H b w) (1 : F₂)
  let xc := Finsupp.single (crossJoinedEdge G H c w) (1 : F₂)
  change (Aab + (xa + xb)) + (Aac + (xa + xc)) + (Abc + (xb + xc)) =
    Aab + Aac + Abc
  calc
    _ = (Aab + Aac + Abc) + (xa + xa) + (xb + xb) + (xc + xc) := by
      abel
    _ = Aab + Aac + Abc := by
      rw [f2_add_self xa, f2_add_self xb, f2_add_self xc]
      simp

omit [Fintype V] [Fintype W] in
private lemma sum_rightMixedBoundaryExpected_eq_internal
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) {a b c : W}
    (hab : Hᶜ.Adj a b) (hac : Hᶜ.Adj a c) (hbc : Hᶜ.Adj b c) :
    let eab : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hab
    let eac : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hac
    let ebc : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hbc
    rightMixedBoundaryExpected G H v eab +
        rightMixedBoundaryExpected G H v eac +
        rightMixedBoundaryExpected G H v ebc =
      Finsupp.single (rightJoinedEdge G H eab) 1 +
        Finsupp.single (rightJoinedEdge G H eac) 1 +
        Finsupp.single (rightJoinedEdge G H ebc) 1 := by
  dsimp only
  let Aab := Finsupp.single
    (rightJoinedEdge G H (flagEdgeOfAdj Hᶜ hab)) (1 : F₂)
  let Aac := Finsupp.single
    (rightJoinedEdge G H (flagEdgeOfAdj Hᶜ hac)) (1 : F₂)
  let Abc := Finsupp.single
    (rightJoinedEdge G H (flagEdgeOfAdj Hᶜ hbc)) (1 : F₂)
  let xa := Finsupp.single (crossJoinedEdge G H v a) (1 : F₂)
  let xb := Finsupp.single (crossJoinedEdge G H v b) (1 : F₂)
  let xc := Finsupp.single (crossJoinedEdge G H v c) (1 : F₂)
  change (Aab + (xa + xb)) + (Aac + (xa + xc)) + (Abc + (xb + xc)) =
    Aab + Aac + Abc
  calc
    _ = (Aab + Aac + Abc) + (xa + xa) + (xb + xb) + (xc + xc) := by
      abel
    _ = Aab + Aac + Abc := by
      rw [f2_add_self xa, f2_add_self xb, f2_add_self xc]
      simp

private lemma triangleBoundary_mem_range_mixedBoundaryMap
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    (t : FlagTriangle (G ⊕g H)ᶜ) :
    triangleBoundary (G ⊕g H)ᶜ t ∈ LinearMap.range (mixedBoundaryMap G H) := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ht⟩ :=
    SimpleGraph.is3Clique_iff.mp
      (⟨t.2.2, t.2.1⟩ : (G ⊕g H)ᶜ.IsNClique 3 t.1)
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          cases c with
          | inl c =>
              have habG : Gᶜ.Adj a b := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hab
              have hacG : Gᶜ.Adj a c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hac
              have hbcG : Gᶜ.Adj b c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hbc
              let eab : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ habG
              let eac : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hacG
              let ebc : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hbcG
              let w : W := Classical.choice inferInstance
              refine ⟨
                (Finsupp.single eab 1 ⊗ₜ[F₂] Finsupp.single w 1, 0) +
                  (Finsupp.single eac 1 ⊗ₜ[F₂] Finsupp.single w 1, 0) +
                  (Finsupp.single ebc 1 ⊗ₜ[F₂] Finsupp.single w 1, 0), ?_⟩
              rw [map_add, map_add,
                mixedBoundaryMap_left_basis, mixedBoundaryMap_left_basis,
                mixedBoundaryMap_left_basis,
                sum_leftMixedBoundaryExpected_eq_internal G H habG hacG hbcG w]
              have heab : leftJoinedEdge G H eab =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hab := by
                apply Subtype.ext
                rfl
              have heac : leftJoinedEdge G H eac =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hac := by
                apply Subtype.ext
                rfl
              have hebc : leftJoinedEdge G H ebc =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hbc := by
                apply Subtype.ext
                rfl
              rw [heab, heac, hebc]
              exact (triangleBoundary_eq_three_edges
                (G ⊕g H)ᶜ t hab hac hbc (fun x ↦ by
                  have hx := Finset.ext_iff.mp ht x
                  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx)).symm
          | inr c =>
              have habG : Gᶜ.Adj a b := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hab
              let e : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ habG
              have ht' : t = leftMixedTriangle G H e c := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [leftMixedTriangle, leftMixedVertices, e, flagEdgeOfAdj]
              refine ⟨(Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single c 1, 0), ?_⟩
              calc
                mixedBoundaryMap G H
                    (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single c 1, 0) =
                    leftMixedBoundaryExpected G H e c :=
                  mixedBoundaryMap_left_basis G H e c
                _ = triangleBoundary (G ⊕g H)ᶜ (leftMixedTriangle G H e c) :=
                  (triangleBoundary_leftMixedTriangle G H e c).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
      | inr b =>
          cases c with
          | inl c =>
              have hacG : Gᶜ.Adj a c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hac
              let e : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hacG
              have ht' : t = leftMixedTriangle G H e b := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [leftMixedTriangle, leftMixedVertices, e, flagEdgeOfAdj]; tauto
              refine ⟨(Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single b 1, 0), ?_⟩
              calc
                mixedBoundaryMap G H
                    (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single b 1, 0) =
                    leftMixedBoundaryExpected G H e b :=
                  mixedBoundaryMap_left_basis G H e b
                _ = triangleBoundary (G ⊕g H)ᶜ (leftMixedTriangle G H e b) :=
                  (triangleBoundary_leftMixedTriangle G H e b).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
          | inr c =>
              have hbcH : Hᶜ.Adj b c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hbc
              let e : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hbcH
              have ht' : t = rightMixedTriangle G H a e := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [rightMixedTriangle, rightMixedVertices, e, flagEdgeOfAdj]
              refine ⟨(0, Finsupp.single a 1 ⊗ₜ[F₂] Finsupp.single e 1), ?_⟩
              calc
                mixedBoundaryMap G H
                    (0, Finsupp.single a 1 ⊗ₜ[F₂] Finsupp.single e 1) =
                    rightMixedBoundaryExpected G H a e :=
                  mixedBoundaryMap_right_basis G H a e
                _ = triangleBoundary (G ⊕g H)ᶜ (rightMixedTriangle G H a e) :=
                  (triangleBoundary_rightMixedTriangle G H a e).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
  | inr a =>
      cases b with
      | inl b =>
          cases c with
          | inl c =>
              have hbcG : Gᶜ.Adj b c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hbc
              let e : FlagEdge Gᶜ := flagEdgeOfAdj Gᶜ hbcG
              have ht' : t = leftMixedTriangle G H e a := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [leftMixedTriangle, leftMixedVertices, e, flagEdgeOfAdj]; tauto
              refine ⟨(Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single a 1, 0), ?_⟩
              calc
                mixedBoundaryMap G H
                    (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single a 1, 0) =
                    leftMixedBoundaryExpected G H e a :=
                  mixedBoundaryMap_left_basis G H e a
                _ = triangleBoundary (G ⊕g H)ᶜ (leftMixedTriangle G H e a) :=
                  (triangleBoundary_leftMixedTriangle G H e a).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
          | inr c =>
              have hacH : Hᶜ.Adj a c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hac
              let e : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hacH
              have ht' : t = rightMixedTriangle G H b e := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [rightMixedTriangle, rightMixedVertices, e, flagEdgeOfAdj]; tauto
              refine ⟨(0, Finsupp.single b 1 ⊗ₜ[F₂] Finsupp.single e 1), ?_⟩
              calc
                mixedBoundaryMap G H
                    (0, Finsupp.single b 1 ⊗ₜ[F₂] Finsupp.single e 1) =
                    rightMixedBoundaryExpected G H b e :=
                  mixedBoundaryMap_right_basis G H b e
                _ = triangleBoundary (G ⊕g H)ᶜ (rightMixedTriangle G H b e) :=
                  (triangleBoundary_rightMixedTriangle G H b e).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
      | inr b =>
          cases c with
          | inl c =>
              have habH : Hᶜ.Adj a b := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hab
              let e : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ habH
              have ht' : t = rightMixedTriangle G H c e := by
                apply Subtype.ext
                ext x
                rw [ht]
                simp [rightMixedTriangle, rightMixedVertices, e, flagEdgeOfAdj]; tauto
              refine ⟨(0, Finsupp.single c 1 ⊗ₜ[F₂] Finsupp.single e 1), ?_⟩
              calc
                mixedBoundaryMap G H
                    (0, Finsupp.single c 1 ⊗ₜ[F₂] Finsupp.single e 1) =
                    rightMixedBoundaryExpected G H c e :=
                  mixedBoundaryMap_right_basis G H c e
                _ = triangleBoundary (G ⊕g H)ᶜ (rightMixedTriangle G H c e) :=
                  (triangleBoundary_rightMixedTriangle G H c e).symm
                _ = triangleBoundary (G ⊕g H)ᶜ t :=
                  congrArg (triangleBoundary (G ⊕g H)ᶜ) ht'.symm
          | inr c =>
              have habH : Hᶜ.Adj a b := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hab
              have hacH : Hᶜ.Adj a c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hac
              have hbcH : Hᶜ.Adj b c := by
                simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using hbc
              let eab : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ habH
              let eac : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hacH
              let ebc : FlagEdge Hᶜ := flagEdgeOfAdj Hᶜ hbcH
              let v : V := Classical.choice inferInstance
              refine ⟨
                (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single eab 1) +
                  (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single eac 1) +
                  (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single ebc 1), ?_⟩
              rw [map_add, map_add,
                mixedBoundaryMap_right_basis, mixedBoundaryMap_right_basis,
                mixedBoundaryMap_right_basis,
                sum_rightMixedBoundaryExpected_eq_internal G H v habH hacH hbcH]
              have heab : rightJoinedEdge G H eab =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hab := by
                apply Subtype.ext
                rfl
              have heac : rightJoinedEdge G H eac =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hac := by
                apply Subtype.ext
                rfl
              have hebc : rightJoinedEdge G H ebc =
                  flagEdgeOfAdj (G ⊕g H)ᶜ hbc := by
                apply Subtype.ext
                rfl
              rw [heab, heac, hebc]
              exact (triangleBoundary_eq_three_edges
                (G ⊕g H)ᶜ t hab hac hbc (fun x ↦ by
                  have hx := Finset.ext_iff.mp ht x
                  simpa only [Finset.mem_insert, Finset.mem_singleton] using hx)).symm

/-- The literal triangular boundary space of the joined complement is already
generated by its two mixed-face families.  Pure-side triangular faces are
the sums of three mixed faces through one fixed vertex on the opposite side. -/
theorem range_flagD2_eq_range_mixedBoundaryMap
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    LinearMap.range (flagD2 (G ⊕g H)ᶜ) =
      LinearMap.range (mixedBoundaryMap G H) := by
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy =>
        rw [map_add]
        exact (LinearMap.range (mixedBoundaryMap G H)).add_mem hx hy
    | single t r =>
        rw [flagD2, Finsupp.linearCombination_single]
        exact (LinearMap.range (mixedBoundaryMap G H)).smul_mem r
          (triangleBoundary_mem_range_mixedBoundaryMap G H t)
  · rintro _ ⟨c, rfl⟩
    exact ⟨mixedFaceMap G H c, by rfl⟩

end

end ExtremalUnorderedMixedFaces
