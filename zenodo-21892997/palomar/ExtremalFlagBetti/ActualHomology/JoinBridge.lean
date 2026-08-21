/-
This file composes the three independently checked unordered join layers into
the literal degree-one homology equivalence required by Proposition 3.1.

Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import ExtremalFlagBetti.ActualHomology.UnorderedJoin
import ExtremalFlagBetti.ActualHomology.MixedFaces
import ExtremalFlagBetti.ActualHomology.JoinAlgebra

open Finset SimpleGraph

namespace ExtremalFullJoinBridge

abbrev F₂ := ZMod 2

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]

local instance : DecidableEq V := Classical.decEq V
local instance : DecidableEq W := Classical.decEq W

omit [Fintype V] [Fintype W] in
@[simp] lemma mixed_leftJoinedEdge_eq
    (G : SimpleGraph V) (H : SimpleGraph W) (e : ExtremalUnorderedJoin.FlagEdge Gᶜ) :
    ExtremalUnorderedMixedFaces.leftJoinedEdge G H e = ExtremalUnorderedJoin.leftJoinedEdge G H e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v => rfl

omit [Fintype V] [Fintype W] in
@[simp] lemma mixed_crossJoinedEdge_eq
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) :
    ExtremalUnorderedMixedFaces.crossJoinedEdge G H v w = ExtremalUnorderedJoin.crossJoinedEdge G H v w := by
  rfl

omit [Fintype V] [Fintype W] in
@[simp] lemma mixed_rightJoinedEdge_eq
    (G : SimpleGraph V) (H : SimpleGraph W) (e : ExtremalUnorderedJoin.FlagEdge Hᶜ) :
    ExtremalUnorderedMixedFaces.rightJoinedEdge G H e = ExtremalUnorderedJoin.rightJoinedEdge G H e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ w w' => rfl

omit [Fintype V] [Fintype W] in
lemma vertexAugmentation_edgeBoundary
    (K : SimpleGraph V) (e : ExtremalUnorderedJoin.FlagEdge K) :
    ExtremalUnorderedJoin.vertexAugmentation V (ExtremalUnorderedJoin.edgeBoundary K e) = 0 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp only [ExtremalUnorderedJoin.edgeBoundary, Sym2.lift_mk, ExtremalUnorderedJoin.vertexAugmentation,
        Finsupp.lsum_apply]
      rw [Finsupp.sum_add_index'] <;> simp [ExtremalUnorderedJoin.f2_add_self]

omit [Fintype V] in
lemma vertexAugmentation_flagD1
    (K : SimpleGraph V) (c : ExtremalUnorderedJoin.FlagChain1 K) :
    ExtremalUnorderedJoin.vertexAugmentation V (ExtremalUnorderedJoin.flagD1 K c) = 0 := by
  classical
  rw [ExtremalUnorderedJoin.flagD1, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul, vertexAugmentation_edgeBoundary, smul_zero,
    Finsupp.sum_fun_zero]

omit [Fintype V] [Fintype W] in
/-- The generic abstract joined boundary specializes definitionally to the
literal split graph boundary. -/
lemma splitJoinD1_eq_abstractJoinD1 (G : SimpleGraph V) (H : SimpleGraph W) :
    ExtremalUnorderedJoin.splitJoinD1 G H =
      ExtremalJoinLemma.abstractJoinD1 (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W) := by
  rfl

omit [Fintype W] in
lemma joinedEdgeCoordinates_leftMixedBoundaryExpected
    (G : SimpleGraph V) (H : SimpleGraph W)
    (e : ExtremalUnorderedJoin.FlagEdge Gᶜ) (w : W) :
    ExtremalUnorderedJoin.joinedEdgeCoordinates G H (ExtremalUnorderedMixedFaces.leftMixedBoundaryExpected G H e w) =
      ExtremalJoinLemma.abstractJoinMixedD2 (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W)
        (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single w 1, 0) := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      simp [ExtremalUnorderedMixedFaces.leftMixedBoundaryExpected, ExtremalUnorderedMixedFaces.leftCrossBoundary,
        ExtremalJoinLemma.abstractJoinMixedD2, ExtremalJoinLemma.rightMarginal, ExtremalJoinLemma.leftMarginal,
        ExtremalUnorderedJoin.flagD1, ExtremalUnorderedJoin.edgeBoundary, ExtremalUnorderedJoin.vertexAugmentation,
        TensorProduct.add_tmul]

omit [Fintype V] in
lemma joinedEdgeCoordinates_rightMixedBoundaryExpected
    (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (e : ExtremalUnorderedJoin.FlagEdge Hᶜ) :
    ExtremalUnorderedJoin.joinedEdgeCoordinates G H (ExtremalUnorderedMixedFaces.rightMixedBoundaryExpected G H v e) =
      ExtremalJoinLemma.abstractJoinMixedD2 (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W)
        (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single e 1) := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      simp [ExtremalUnorderedMixedFaces.rightMixedBoundaryExpected, ExtremalUnorderedMixedFaces.rightCrossBoundary,
        ExtremalJoinLemma.abstractJoinMixedD2, ExtremalJoinLemma.rightMarginal, ExtremalJoinLemma.leftMarginal,
        ExtremalUnorderedJoin.flagD1, ExtremalUnorderedJoin.edgeBoundary, ExtremalUnorderedJoin.vertexAugmentation,
        TensorProduct.tmul_add]

private def actualLeftMixedBoundaryMap
    (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (ExtremalUnorderedJoin.FlagChain0 W) →ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
  (ExtremalUnorderedJoin.joinedEdgeCoordinates G H).toLinearMap.comp
    ((ExtremalUnorderedMixedFaces.mixedBoundaryMap G H).comp
      (LinearMap.inl F₂ _ _))

private def abstractLeftMixedBoundaryMap
    (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (ExtremalUnorderedJoin.FlagChain0 W) →ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
  (ExtremalJoinLemma.abstractJoinMixedD2
    (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
    (ExtremalUnorderedJoin.vertexAugmentation V)
    (ExtremalUnorderedJoin.vertexAugmentation W)).comp (LinearMap.inl F₂ _ _)

private lemma actualLeftMixedBoundaryMap_eq_abstract
    (G : SimpleGraph V) (H : SimpleGraph W) :
    actualLeftMixedBoundaryMap G H = abstractLeftMixedBoundaryMap G H := by
  apply TensorProduct.curry_injective
  apply Finsupp.lhom_ext'
  intro e
  apply LinearMap.ext
  intro r
  apply Finsupp.lhom_ext'
  intro w
  apply LinearMap.ext
  intro s
  have he : Finsupp.single e r =
      r • (Finsupp.single e (1 : F₂)) := by simp
  have hw : Finsupp.single w s =
      s • (Finsupp.single w (1 : F₂)) := by simp
  change actualLeftMixedBoundaryMap G H
      (Finsupp.single e r ⊗ₜ[F₂] Finsupp.single w s) =
    abstractLeftMixedBoundaryMap G H
      (Finsupp.single e r ⊗ₜ[F₂] Finsupp.single w s)
  rw [he, hw, TensorProduct.smul_tmul_smul, map_smul, map_smul]
  change (r * s) •
      (ExtremalUnorderedJoin.joinedEdgeCoordinates G H
        (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H
          (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single w 1, 0))) =
    (r * s) •
      (ExtremalJoinLemma.abstractJoinMixedD2
        (ExtremalUnorderedJoin.flagD1 Gᶜ)
        (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W)
        (Finsupp.single e 1 ⊗ₜ[F₂] Finsupp.single w 1, 0))
  rw [ExtremalUnorderedMixedFaces.mixedBoundaryMap_left_basis,
    joinedEdgeCoordinates_leftMixedBoundaryExpected]

private def actualRightMixedBoundaryMap
    (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V)
        (ExtremalUnorderedJoin.FlagChain1 Hᶜ) →ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
  (ExtremalUnorderedJoin.joinedEdgeCoordinates G H).toLinearMap.comp
    ((ExtremalUnorderedMixedFaces.mixedBoundaryMap G H).comp
      (LinearMap.inr F₂ _ _))

private def abstractRightMixedBoundaryMap
    (G : SimpleGraph V) (H : SimpleGraph W) :
    TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V)
        (ExtremalUnorderedJoin.FlagChain1 Hᶜ) →ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
  (ExtremalJoinLemma.abstractJoinMixedD2
    (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
    (ExtremalUnorderedJoin.vertexAugmentation V)
    (ExtremalUnorderedJoin.vertexAugmentation W)).comp (LinearMap.inr F₂ _ _)

private lemma actualRightMixedBoundaryMap_eq_abstract
    (G : SimpleGraph V) (H : SimpleGraph W) :
    actualRightMixedBoundaryMap G H = abstractRightMixedBoundaryMap G H := by
  apply TensorProduct.curry_injective
  apply Finsupp.lhom_ext'
  intro v
  apply LinearMap.ext
  intro r
  apply Finsupp.lhom_ext'
  intro e
  apply LinearMap.ext
  intro s
  have hv : Finsupp.single v r =
      r • (Finsupp.single v (1 : F₂)) := by simp
  have he : Finsupp.single e s =
      s • (Finsupp.single e (1 : F₂)) := by simp
  change actualRightMixedBoundaryMap G H
      (Finsupp.single v r ⊗ₜ[F₂] Finsupp.single e s) =
    abstractRightMixedBoundaryMap G H
      (Finsupp.single v r ⊗ₜ[F₂] Finsupp.single e s)
  rw [hv, he, TensorProduct.smul_tmul_smul, map_smul, map_smul]
  change (r * s) •
      (ExtremalUnorderedJoin.joinedEdgeCoordinates G H
        (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H
          (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single e 1))) =
    (r * s) •
      (ExtremalJoinLemma.abstractJoinMixedD2
        (ExtremalUnorderedJoin.flagD1 Gᶜ)
        (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W)
        (0, Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single e 1))
  rw [ExtremalUnorderedMixedFaces.mixedBoundaryMap_right_basis,
    joinedEdgeCoordinates_rightMixedBoundaryExpected]

/-- Exact coordinate identity for the two literal mixed-face families. -/
theorem joinedEdgeCoordinates_mixedBoundaryMap
    (G : SimpleGraph V) (H : SimpleGraph W)
    (c : TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ) (ExtremalUnorderedJoin.FlagChain0 W) ×
      TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V) (ExtremalUnorderedJoin.FlagChain1 Hᶜ)) :
    ExtremalUnorderedJoin.joinedEdgeCoordinates G H (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H c) =
      ExtremalJoinLemma.abstractJoinMixedD2 (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W) c := by
  let actual :
      (TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ)
          (ExtremalUnorderedJoin.FlagChain0 W) ×
        TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V)
          (ExtremalUnorderedJoin.FlagChain1 Hᶜ)) →ₗ[F₂]
        ExtremalJoinLemma.AbstractJoinChain1
          (A := ExtremalUnorderedJoin.FlagChain0 V)
          (B := ExtremalUnorderedJoin.FlagChain0 W)
          (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
          (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
    LinearMap.coprod (actualLeftMixedBoundaryMap G H)
      (actualRightMixedBoundaryMap G H)
  let abstract :
      (TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ)
          (ExtremalUnorderedJoin.FlagChain0 W) ×
        TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V)
          (ExtremalUnorderedJoin.FlagChain1 Hᶜ)) →ₗ[F₂]
        ExtremalJoinLemma.AbstractJoinChain1
          (A := ExtremalUnorderedJoin.FlagChain0 V)
          (B := ExtremalUnorderedJoin.FlagChain0 W)
          (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
          (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ) :=
    LinearMap.coprod (abstractLeftMixedBoundaryMap G H)
      (abstractRightMixedBoundaryMap G H)
  have hmaps : actual = abstract := by
    dsimp [actual, abstract]
    rw [actualLeftMixedBoundaryMap_eq_abstract,
      actualRightMixedBoundaryMap_eq_abstract]
  calc
    _ = actual c := by
      rcases c with ⟨x, y⟩
      change ExtremalUnorderedJoin.joinedEdgeCoordinates G H
          (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H (x, y)) =
        ExtremalUnorderedJoin.joinedEdgeCoordinates G H
            (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H (x, 0)) +
          ExtremalUnorderedJoin.joinedEdgeCoordinates G H
            (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H (0, y))
      rw [show (x, y) = (x, 0) + (0, y) by ext <;> simp,
        map_add, map_add]
    _ = abstract c := LinearMap.congr_fun hmaps c
    _ = _ := by
      rcases c with ⟨x, y⟩
      simp [abstract, abstractLeftMixedBoundaryMap,
        abstractRightMixedBoundaryMap]

/-! ### Transport of the actual cycle and boundary quotient -/

def flagD2Cycle (K : SimpleGraph V) :
    ExtremalUnorderedMixedFaces.FlagChain2 K →ₗ[F₂] ExtremalUnorderedJoin.FlagCycle K where
  toFun c := ⟨ExtremalUnorderedMixedFaces.flagD2 K c, by
    classical
    induction c using Finsupp.induction_linear with
    | zero =>
        change ExtremalUnorderedJoin.flagD1 K 0 = 0
        rw [map_zero]
    | add x y hx hy =>
        change ExtremalUnorderedJoin.flagD1 K
          (ExtremalUnorderedMixedFaces.flagD2 K (x + y)) = 0
        change ExtremalUnorderedJoin.flagD1 K
          (ExtremalUnorderedMixedFaces.flagD2 K x) = 0 at hx
        change ExtremalUnorderedJoin.flagD1 K
          (ExtremalUnorderedMixedFaces.flagD2 K y) = 0 at hy
        rw [map_add, map_add, hx, hy, add_zero]
    | single t r =>
        change ExtremalUnorderedJoin.flagD1 K
          (ExtremalUnorderedMixedFaces.flagD2 K (Finsupp.single t r)) = 0
        rw [ExtremalUnorderedMixedFaces.flagD2,
          Finsupp.linearCombination_single, map_smul]
        suffices ExtremalUnorderedJoin.flagD1 K
            (ExtremalUnorderedMixedFaces.triangleBoundary K t) = 0 by
          rw [this, smul_zero]
        obtain ⟨a, b, c, hab, hac, hbc, ht⟩ :=
          SimpleGraph.is3Clique_iff.mp
            (⟨t.2.2, t.2.1⟩ : K.IsNClique 3 t.1)
        rw [ExtremalUnorderedMixedFaces.triangleBoundary_eq_three_edges K t hab hac hbc (fun x ↦ by
          have hx := Finset.ext_iff.mp ht x
          simpa only [Finset.mem_insert, Finset.mem_singleton] using hx),
          map_add, map_add]
        simp only [ExtremalUnorderedJoin.flagD1, Finsupp.linearCombination_single,
          ExtremalUnorderedMixedFaces.flagEdgeOfAdj, ExtremalUnorderedJoin.edgeBoundary, Sym2.lift_mk, one_smul]
        calc
          (Finsupp.single a (1 : F₂) + Finsupp.single b 1) +
              (Finsupp.single a 1 + Finsupp.single c 1) +
              (Finsupp.single b 1 + Finsupp.single c 1) =
            (Finsupp.single a (1 : F₂) + Finsupp.single a 1) +
              (Finsupp.single b 1 + Finsupp.single b 1) +
              (Finsupp.single c 1 + Finsupp.single c 1) := by
                abel
          _ = 0 := by
            rw [ExtremalUnorderedJoin.f2_add_self
                  (Finsupp.single a (1 : F₂)),
              ExtremalUnorderedJoin.f2_add_self
                  (Finsupp.single b (1 : F₂)),
              ExtremalUnorderedJoin.f2_add_self
                  (Finsupp.single c (1 : F₂))]
            simp
    ⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp [ExtremalUnorderedMixedFaces.flagD2]
  map_smul' _ _ := by
    apply Subtype.ext
    simp [ExtremalUnorderedMixedFaces.flagD2]

def JoinedBoundarySubmodule (K : SimpleGraph V) :
    Submodule F₂ (ExtremalUnorderedJoin.FlagCycle K) :=
  LinearMap.range (flagD2Cycle K)

abbrev JoinedFlagH1 (K : SimpleGraph V) :=
  ExtremalUnorderedJoin.FlagCycle K ⧸ JoinedBoundarySubmodule K

def abstractGraphMixedD2Cycle (G : SimpleGraph V) (H : SimpleGraph W) :
    (TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ) (ExtremalUnorderedJoin.FlagChain0 W) ×
      TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V) (ExtremalUnorderedJoin.FlagChain1 Hᶜ)) →ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinCycle (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W) :=
  ExtremalJoinLemma.abstractJoinMixedD2Cycle (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
    (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W)
    (vertexAugmentation_flagD1 Gᶜ) (vertexAugmentation_flagD1 Hᶜ)

def splitCycleEquivAbstract (G : SimpleGraph V) (H : SimpleGraph W) :
    ExtremalUnorderedJoin.SplitJoinCycle G H ≃ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinCycle (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W) where
  toFun c := ⟨c.1, by
    change ExtremalJoinLemma.abstractJoinD1
        (ExtremalUnorderedJoin.flagD1 Gᶜ)
        (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W) c.1 = 0
    rw [← splitJoinD1_eq_abstractJoinD1]
    exact c.2⟩
  invFun c := ⟨c.1, by
    change ExtremalUnorderedJoin.splitJoinD1 G H c.1 = 0
    rw [splitJoinD1_eq_abstractJoinD1]
    exact c.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    rfl
  map_smul' _ _ := by
    apply Subtype.ext
    rfl
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl

def joinedCycleEquivAbstract (G : SimpleGraph V) (H : SimpleGraph W) :
    ExtremalUnorderedJoin.FlagCycle (G ⊕g H)ᶜ ≃ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinCycle (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W) :=
  (ExtremalUnorderedJoin.joinedCycleEquivSplit G H).trans (splitCycleEquivAbstract G H)

lemma joinedCycleEquivAbstract_mixedBoundary
    (G : SimpleGraph V) (H : SimpleGraph W)
    (c : TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain1 Gᶜ) (ExtremalUnorderedJoin.FlagChain0 W) ×
      TensorProduct F₂ (ExtremalUnorderedJoin.FlagChain0 V) (ExtremalUnorderedJoin.FlagChain1 Hᶜ)) :
    joinedCycleEquivAbstract G H
        ⟨ExtremalUnorderedMixedFaces.mixedBoundaryMap G H c, by
          rw [ExtremalUnorderedMixedFaces.mixedBoundaryMap]
          exact (flagD2Cycle (G ⊕g H)ᶜ (ExtremalUnorderedMixedFaces.mixedFaceMap G H c)).2⟩ =
      abstractGraphMixedD2Cycle G H c := by
  apply Subtype.ext
  exact joinedEdgeCoordinates_mixedBoundaryMap G H c

lemma joinedBoundary_map_eq_abstractBoundary
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    (JoinedBoundarySubmodule (G ⊕g H)ᶜ).map
        (joinedCycleEquivAbstract G H : _ →ₗ[F₂] _) =
      ExtremalJoinLemma.AbstractJoinBoundarySubmodule (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W)
        (vertexAugmentation_flagD1 Gᶜ) (vertexAugmentation_flagD1 Hᶜ) := by
  apply le_antisymm
  · rintro y ⟨x, ⟨c, rfl⟩, rfl⟩
    have hc : ExtremalUnorderedMixedFaces.flagD2 (G ⊕g H)ᶜ c ∈
        LinearMap.range (ExtremalUnorderedMixedFaces.mixedBoundaryMap G H) := by
      rw [← ExtremalUnorderedMixedFaces.range_flagD2_eq_range_mixedBoundaryMap G H]
      exact LinearMap.mem_range_self _ c
    obtain ⟨m, hm⟩ := hc
    refine ⟨m, ?_⟩
    apply Subtype.ext
    symm
    change ExtremalUnorderedJoin.joinedEdgeCoordinates G H (ExtremalUnorderedMixedFaces.flagD2 (G ⊕g H)ᶜ c) = _
    rw [← hm, joinedEdgeCoordinates_mixedBoundaryMap]
    rfl
  · rintro y ⟨m, rfl⟩
    refine ⟨⟨ExtremalUnorderedMixedFaces.mixedBoundaryMap G H m, by
      rw [ExtremalUnorderedMixedFaces.mixedBoundaryMap]
      exact (flagD2Cycle (G ⊕g H)ᶜ (ExtremalUnorderedMixedFaces.mixedFaceMap G H m)).2⟩, ?_, ?_⟩
    · refine ⟨ExtremalUnorderedMixedFaces.mixedFaceMap G H m, ?_⟩
      apply Subtype.ext
      rfl
    · exact joinedCycleEquivAbstract_mixedBoundary G H m

/-- Literal flag `H₁` of the joined complement is the abstract joined-cycle
quotient.  The only ingredients are exact edge coordinates and the theorem
that all triangular boundaries are generated by literal mixed faces. -/
noncomputable def joinedFlagH1EquivAbstract
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    JoinedFlagH1 (G ⊕g H)ᶜ ≃ₗ[F₂]
      ExtremalJoinLemma.AbstractJoinH1 (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V) (ExtremalUnorderedJoin.vertexAugmentation W)
        (vertexAugmentation_flagD1 Gᶜ) (vertexAugmentation_flagD1 Hᶜ) := by
  letI : AddCommGroup
      (ExtremalJoinLemma.AbstractJoinCycle
        (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W)) :=
    @Submodule.addCommGroup F₂
      (ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ))
      inferInstance inferInstance inferInstance
      (ExtremalJoinLemma.AbstractJoinCycleSubmodule
        (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W))
  letI : Module F₂
      (ExtremalJoinLemma.AbstractJoinCycle
        (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W)) :=
    @Submodule.module F₂
      (ExtremalJoinLemma.AbstractJoinChain1
        (A := ExtremalUnorderedJoin.FlagChain0 V)
        (B := ExtremalUnorderedJoin.FlagChain0 W)
        (EA := ExtremalUnorderedJoin.FlagChain1 Gᶜ)
        (EB := ExtremalUnorderedJoin.FlagChain1 Hᶜ))
      inferInstance inferInstance inferInstance
      (ExtremalJoinLemma.AbstractJoinCycleSubmodule
        (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (ExtremalUnorderedJoin.vertexAugmentation W))
  exact Submodule.Quotient.equiv
    (JoinedBoundarySubmodule (G ⊕g H)ᶜ)
    (ExtremalJoinLemma.AbstractJoinBoundarySubmodule
      (ExtremalUnorderedJoin.flagD1 Gᶜ) (ExtremalUnorderedJoin.flagD1 Hᶜ)
      (ExtremalUnorderedJoin.vertexAugmentation V)
      (ExtremalUnorderedJoin.vertexAugmentation W)
      (vertexAugmentation_flagD1 Gᶜ) (vertexAugmentation_flagD1 Hᶜ))
    (joinedCycleEquivAbstract G H)
    (joinedBoundary_map_eq_abstractBoundary G H)

/-! ### Component-coordinate quotient and the final tensor formula -/

omit [Fintype V] [Fintype W] in
lemma vertexComponentMap_surjective
    (K : SimpleGraph V) :
    Function.Surjective (ExtremalUnorderedJoin.vertexComponentMap K) := by
  classical
  intro c
  induction c using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | single C r =>
      refine ⟨Finsupp.single C.out r, ?_⟩
      simp only [ExtremalUnorderedJoin.vertexComponentMap,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      have hC : K.connectedComponentMk C.out = C := Quot.out_eq C
      rw [hC]

noncomputable def componentQuotientEquiv (K : SimpleGraph V) :
    (ExtremalUnorderedJoin.FlagChain0 V ⧸
        LinearMap.range (ExtremalUnorderedJoin.flagD1 K)) ≃ₗ[F₂]
      (K.ConnectedComponent →₀ F₂) :=
  (Submodule.quotEquivOfEq
      (LinearMap.range (ExtremalUnorderedJoin.flagD1 K))
      (LinearMap.ker (ExtremalUnorderedJoin.vertexComponentMap K))
      (ExtremalUnorderedJoin.ker_vertexComponentMap_eq_range_flagD1 K).symm).trans
    ((ExtremalUnorderedJoin.vertexComponentMap K).quotKerEquivOfSurjective
      (vertexComponentMap_surjective K))

omit [Fintype V] [Fintype W] in
lemma componentQuotientEquiv_augmentation
    (K : SimpleGraph V)
    (x : ExtremalUnorderedJoin.FlagChain0 V ⧸
      LinearMap.range (ExtremalUnorderedJoin.flagD1 K)) :
    ExtremalUnorderedJoin.componentAugmentation K
        (componentQuotientEquiv K x) =
      ExtremalJoinLemma.quotientAugmentation
        (ExtremalUnorderedJoin.flagD1 K)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (vertexAugmentation_flagD1 K) x := by
  induction x using Submodule.Quotient.induction_on with
  | _ a =>
      change ExtremalUnorderedJoin.componentAugmentation K
          (ExtremalUnorderedJoin.vertexComponentMap K a) =
        ExtremalUnorderedJoin.vertexAugmentation V a
      exact LinearMap.congr_fun
        (ExtremalUnorderedJoin.componentAugmentation_vertexComponentMap K) a

noncomputable def quotientReducedEquiv (K : SimpleGraph V) :
    LinearMap.ker
        (ExtremalJoinLemma.quotientAugmentation
          (ExtremalUnorderedJoin.flagD1 K)
          (ExtremalUnorderedJoin.vertexAugmentation V)
          (vertexAugmentation_flagD1 K)) ≃ₗ[F₂]
      LinearMap.ker (ExtremalUnorderedJoin.componentAugmentation K) where
  toFun x := ⟨componentQuotientEquiv K x.1, by
    change ExtremalUnorderedJoin.componentAugmentation K
      (componentQuotientEquiv K x.1) = 0
    rw [componentQuotientEquiv_augmentation]
    exact x.2⟩
  invFun y := ⟨(componentQuotientEquiv K).symm y.1, by
    change ExtremalJoinLemma.quotientAugmentation
      (ExtremalUnorderedJoin.flagD1 K)
      (ExtremalUnorderedJoin.vertexAugmentation V)
      (vertexAugmentation_flagD1 K)
      ((componentQuotientEquiv K).symm y.1) = 0
    rw [← componentQuotientEquiv_augmentation]
    simpa using y.2⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp

/-- The literal unordered flag-homology join formula, including the graph
component quotient rather than only the abstract double-marginal kernel. -/
noncomputable def joinedFlagH1EquivTensorReduced
    [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) :
    JoinedFlagH1 (G ⊕g H)ᶜ ≃ₗ[F₂]
      TensorProduct F₂
        (LinearMap.ker (ExtremalUnorderedJoin.componentAugmentation Gᶜ))
        (LinearMap.ker (ExtremalUnorderedJoin.componentAugmentation Hᶜ)) := by
  let a : ExtremalUnorderedJoin.FlagChain0 V :=
    Finsupp.single (Classical.choice (inferInstance : Nonempty V)) 1
  let b : ExtremalUnorderedJoin.FlagChain0 W :=
    Finsupp.single (Classical.choice (inferInstance : Nonempty W)) 1
  let aQ : ExtremalUnorderedJoin.FlagChain0 V ⧸
      LinearMap.range (ExtremalUnorderedJoin.flagD1 Gᶜ) :=
    Submodule.Quotient.mk a
  let bQ : ExtremalUnorderedJoin.FlagChain0 W ⧸
      LinearMap.range (ExtremalUnorderedJoin.flagD1 Hᶜ) :=
    Submodule.Quotient.mk b
  have ha : ExtremalUnorderedJoin.vertexAugmentation V a = 1 := by
    simp [a, ExtremalUnorderedJoin.vertexAugmentation]
  have hb : ExtremalUnorderedJoin.vertexAugmentation W b = 1 := by
    simp [b, ExtremalUnorderedJoin.vertexAugmentation]
  have haQ : ExtremalJoinLemma.quotientAugmentation
      (ExtremalUnorderedJoin.flagD1 Gᶜ)
      (ExtremalUnorderedJoin.vertexAugmentation V)
      (vertexAugmentation_flagD1 Gᶜ) aQ = 1 := by
    simpa [aQ] using ha
  have hbQ : ExtremalJoinLemma.quotientAugmentation
      (ExtremalUnorderedJoin.flagD1 Hᶜ)
      (ExtremalUnorderedJoin.vertexAugmentation W)
      (vertexAugmentation_flagD1 Hᶜ) bQ = 1 := by
    simpa [bQ] using hb
  exact (joinedFlagH1EquivAbstract G H).trans <|
    (ExtremalJoinLemma.abstractJoinH1EquivDoubleMarginal
      (ExtremalUnorderedJoin.flagD1 Gᶜ)
      (ExtremalUnorderedJoin.flagD1 Hᶜ)
      (ExtremalUnorderedJoin.vertexAugmentation V)
      (ExtremalUnorderedJoin.vertexAugmentation W)
      (vertexAugmentation_flagD1 Gᶜ) (vertexAugmentation_flagD1 Hᶜ)
      a ha b hb).trans <|
    (ExtremalJoinLemma.tensor_reduced_equiv_doubleMarginalKernel
      (ExtremalJoinLemma.quotientAugmentation
        (ExtremalUnorderedJoin.flagD1 Gᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation V)
        (vertexAugmentation_flagD1 Gᶜ))
      (ExtremalJoinLemma.quotientAugmentation
        (ExtremalUnorderedJoin.flagD1 Hᶜ)
        (ExtremalUnorderedJoin.vertexAugmentation W)
        (vertexAugmentation_flagD1 Hᶜ))
      aQ haQ bQ hbQ).symm.trans <|
    TensorProduct.congr (quotientReducedEquiv Gᶜ)
      (quotientReducedEquiv Hᶜ)

end

end ExtremalFullJoinBridge
