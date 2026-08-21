/-
Canonical unordered graph-level bridge for the degree-one join formula used
in Proposition 3.1.

Authors: Lennart Rudolph, Sol, Fable
-/

import Mathlib
import Mathlib.LinearAlgebra.DirectSum.Finsupp

open Finset SimpleGraph

namespace ExtremalUnorderedJoin

abbrev F₂ := ZMod 2

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]

lemma f2_add_self {M : Type*} [AddCommGroup M] [Module F₂ M]
    (x : M) : x + x = 0 := by
  calc
    x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
    _ = ((1 : F₂) + 1) • x := by rw [add_smul]
    _ = 0 := by
      have htwo : (1 : F₂) + 1 = 0 := by decide
      rw [htwo, zero_smul]

abbrev FlagEdge (G : SimpleGraph V) := {e : Sym2 V // e ∈ G.edgeSet}
abbrev FlagChain0 (V : Type*) := V →₀ F₂
abbrev FlagChain1 (G : SimpleGraph V) := FlagEdge G →₀ F₂

/-- The canonical three-way decomposition of an unordered pair on a sum:
left-left, left-right, or right-right. -/
def sym2SumEquiv :
    Sym2 (V ⊕ W) ≃ Sym2 V ⊕ ((V × W) ⊕ Sym2 W) where
  toFun := Sym2.lift
    ⟨fun x y ↦ match x, y with
      | .inl v, .inl v' => .inl s(v, v')
      | .inl v, .inr w => .inr (.inl (v, w))
      | .inr w, .inl v => .inr (.inl (v, w))
      | .inr w, .inr w' => .inr (.inr s(w, w')),
    by
      intro x y
      cases x <;> cases y <;> simp only
      · exact congrArg Sum.inl Sym2.eq_swap
      · exact congrArg (fun e ↦ Sum.inr (Sum.inr e)) Sym2.eq_swap⟩
  invFun
    | .inl e => Sym2.map Sum.inl e
    | .inr (.inl (v, w)) => s(Sum.inl v, Sum.inr w)
    | .inr (.inr e) => Sym2.map Sum.inr e
  left_inv e := by
    induction e using Sym2.inductionOn with
    | _ x y => cases x <;> cases y <;> simp [Sym2.eq_swap]
  right_inv e := by
    rcases e with e | e
    · induction e using Sym2.inductionOn with
      | _ v v' => rfl
    · rcases e with vw | e
      · rfl
      · induction e using Sym2.inductionOn with
        | _ w w' => rfl

def IsJoinedEdgeCoord (G : SimpleGraph V) (H : SimpleGraph W) :
    Sym2 V ⊕ ((V × W) ⊕ Sym2 W) → Prop
  | .inl eV => eV ∈ Gᶜ.edgeSet
  | .inr (.inl _) => True
  | .inr (.inr eW) => eW ∈ Hᶜ.edgeSet

omit [Fintype V] [Fintype W] in
/-- Membership in the complement of a graph sum, expressed in the canonical
three edge coordinates.  Cross pairs are always edges. -/
lemma mem_sum_compl_edgeSet_iff (G : SimpleGraph V) (H : SimpleGraph W)
    (e : Sym2 (V ⊕ W)) :
    e ∈ (G ⊕g H)ᶜ.edgeSet ↔
      IsJoinedEdgeCoord G H (sym2SumEquiv e) := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      cases x <;> cases y <;>
        simp [sym2SumEquiv, IsJoinedEdgeCoord, SimpleGraph.compl_adj,
          SimpleGraph.sum]

/-- Distribute the coordinate predicate over the three summands. -/
def joinedEdgeCoordSubtypeEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    {e // IsJoinedEdgeCoord G H e} ≃
      FlagEdge Gᶜ ⊕ ((V × W) ⊕ FlagEdge Hᶜ) where
  toFun e := match e.1, e.2 with
    | .inl eV, he => .inl ⟨eV, he⟩
    | .inr (.inl vw), _ => .inr (.inl vw)
    | .inr (.inr eW), he => .inr (.inr ⟨eW, he⟩)
  invFun
    | .inl eV => ⟨.inl eV.1, eV.2⟩
    | .inr (.inl vw) => ⟨.inr (.inl vw), trivial⟩
    | .inr (.inr eW) => ⟨.inr (.inr eW.1), eW.2⟩
  left_inv e := by
    rcases e with ⟨e, he⟩
    rcases e with e | rest
    · rfl
    · rcases rest with vw | e
      · rfl
      · rfl
  right_inv e := by
    rcases e with e | rest
    · rfl
    · rcases rest with vw | e
      · rfl
      · rfl

/-- Actual joined edges are exactly left internal edges, all cross pairs,
and right internal edges. -/
def joinedEdgeEquiv (G : SimpleGraph V) (H : SimpleGraph W) :
    FlagEdge (G ⊕g H)ᶜ ≃
      FlagEdge Gᶜ ⊕ ((V × W) ⊕ FlagEdge Hᶜ) :=
  ((sym2SumEquiv (V := V) (W := W)).subtypeEquiv
      (mem_sum_compl_edgeSet_iff G H)).trans
    (joinedEdgeCoordSubtypeEquiv G H)

/-- Finsupp coordinates induced by the joined-edge basis equivalence. -/
def joinedEdgeCoordinates (G : SimpleGraph V) (H : SimpleGraph W) :
    FlagChain1 (G ⊕g H)ᶜ ≃ₗ[F₂]
      ((FlagChain1 Gᶜ) ×
        (TensorProduct F₂ (FlagChain0 V) (FlagChain0 W) × FlagChain1 Hᶜ)) :=
  Finsupp.lcongr (joinedEdgeEquiv G H) (LinearEquiv.refl F₂ F₂) ≪≫ₗ
    Finsupp.sumFinsuppLEquivProdFinsupp F₂ ≪≫ₗ
    LinearEquiv.prodCongr (LinearEquiv.refl F₂ (FlagChain1 Gᶜ))
      (Finsupp.sumFinsuppLEquivProdFinsupp F₂ ≪≫ₗ
        LinearEquiv.prodCongr
          (finsuppTensorFinsupp' F₂ V W).symm
          (LinearEquiv.refl F₂ (FlagChain1 Hᶜ)))

/-! ### The component quotient of the vertex boundary -/

/-- The two endpoints of an unordered edge, added over `F₂`. -/
def edgeBoundary (G : SimpleGraph V) (e : FlagEdge G) : FlagChain0 V :=
  Sym2.lift
    ⟨fun u v ↦ Finsupp.single u 1 + Finsupp.single v 1,
      fun u v ↦ by dsimp; rw [add_comm]⟩ e.1

/-- The ordinary degree-one boundary of the flag complex. -/
def flagD1 (G : SimpleGraph V) : FlagChain1 G →ₗ[F₂] FlagChain0 V :=
  Finsupp.linearCombination F₂ (edgeBoundary G)

/-- Sum all vertex coefficients belonging to the same graph component. -/
noncomputable def vertexComponentMap (G : SimpleGraph V) :
    FlagChain0 V →ₗ[F₂] (G.ConnectedComponent →₀ F₂) :=
  Finsupp.lmapDomain F₂ F₂ G.connectedComponentMk

/-- Total augmentation on vertex chains. -/
noncomputable def vertexAugmentation (V : Type*) :
    FlagChain0 V →ₗ[F₂] F₂ :=
  Finsupp.lsum F₂ (fun _ ↦ LinearMap.id)

/-- Total augmentation on component-coordinate chains. -/
noncomputable def componentAugmentation (G : SimpleGraph V) :
    (G.ConnectedComponent →₀ F₂) →ₗ[F₂] F₂ :=
  Finsupp.lsum F₂ (fun _ ↦ LinearMap.id)

omit [Fintype V] in
/-- Aggregating first by connected component and then globally gives the
ordinary vertex augmentation. -/
lemma componentAugmentation_vertexComponentMap (G : SimpleGraph V) :
    (componentAugmentation G).comp (vertexComponentMap G) =
      vertexAugmentation V := by
  classical
  ext v
  simp [componentAugmentation, vertexComponentMap, vertexAugmentation]

omit [Fintype V] in
/-- The boundary of an edge has zero sum in every connected component. -/
lemma vertexComponentMap_edgeBoundary_eq_zero (G : SimpleGraph V)
    (e : FlagEdge G) :
    vertexComponentMap G (edgeBoundary G e) = 0 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by simpa using he
      have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
        ConnectedComponent.connectedComponentMk_eq_of_adj huv
      simp only [edgeBoundary, Sym2.lift_mk, vertexComponentMap, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_add, Finsupp.mapDomain_single]
      rw [hcomp]
      exact f2_add_self _

omit [Fintype V] in
/-- Hence every graph boundary dies after aggregation by components. -/
lemma range_flagD1_le_ker_vertexComponentMap (G : SimpleGraph V) :
    LinearMap.range (flagD1 G) ≤ LinearMap.ker (vertexComponentMap G) := by
  rintro _ ⟨c, rfl⟩
  change vertexComponentMap G (flagD1 G c) = 0
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa using congrArg₂ (.+.) hx hy
  | single e r =>
      simp only [flagD1, Finsupp.linearCombination_single]
      rw [map_smul, vertexComponentMap_edgeBoundary_eq_zero]
      simp

/- A canonical representative vertex for a connected component. -/
noncomputable def componentRoot (G : SimpleGraph V)
    (C : G.ConnectedComponent) : V :=
  C.out

omit [Fintype V] in
@[simp]
lemma connectedComponentMk_componentRoot (G : SimpleGraph V)
    (C : G.ConnectedComponent) :
    G.connectedComponentMk (componentRoot G C) = C := by
  exact Quot.out_eq C

/-- A chosen walk from a vertex to the canonical representative of its
connected component.  This choice is used only to construct a preimage under
the boundary map. -/
noncomputable def walkToComponentRoot (G : SimpleGraph V) (v : V) :
    G.Walk v (componentRoot G (G.connectedComponentMk v)) :=
  (ConnectedComponent.exact (by
    rw [connectedComponentMk_componentRoot])).some

/-- The edge chain traversed by a walk. -/
def walkEdgeChain (G : SimpleGraph V) :
    {u v : V} → G.Walk u v → FlagChain1 G
  | _, _, .nil => 0
  | u, _, .cons (v := v) h p =>
      Finsupp.single ⟨s(u, v), by simpa using h⟩ 1 + walkEdgeChain G p

omit [Fintype V] in
/-- A walk has boundary equal to the sum of its two endpoints over `F₂`. -/
lemma flagD1_walkEdgeChain (G : SimpleGraph V) {u v : V}
    (p : G.Walk u v) :
    flagD1 G (walkEdgeChain G p) =
      Finsupp.single u 1 + Finsupp.single v 1 := by
  induction p with
  | nil =>
      simp only [walkEdgeChain, map_zero]
      exact (f2_add_self _).symm
  | @cons u v w h p ih =>
      simp only [walkEdgeChain, map_add]
      rw [ih]
      simp only [flagD1, Finsupp.linearCombination_single, edgeBoundary,
        Sym2.lift_mk, one_smul]
      have hv := f2_add_self (Finsupp.single v (1 : F₂))
      calc
        (Finsupp.single u (1 : F₂) + Finsupp.single v 1) +
              (Finsupp.single v 1 + Finsupp.single w 1) =
            Finsupp.single u 1 +
              (Finsupp.single v 1 + Finsupp.single v 1) +
              Finsupp.single w 1 := by abel
        _ = Finsupp.single u 1 + Finsupp.single w 1 := by
          simp only [hv, add_zero]

/-- Send each component coordinate back to its chosen root vertex. -/
noncomputable def componentRootMap (G : SimpleGraph V) :
    (G.ConnectedComponent →₀ F₂) →ₗ[F₂] FlagChain0 V :=
  Finsupp.lmapDomain F₂ F₂ (componentRoot G)

/-- Lift a vertex chain to chosen root walks. -/
noncomputable def rootWalkLift (G : SimpleGraph V) :
    FlagChain0 V →ₗ[F₂] FlagChain1 G :=
  Finsupp.linearCombination F₂
    (fun v ↦ walkEdgeChain G (walkToComponentRoot G v))

omit [Fintype V] in
/-- The chosen-root lift witnesses a vertex chain up to its component sums. -/
lemma flagD1_rootWalkLift (G : SimpleGraph V) (c : FlagChain0 V) :
    flagD1 G (rootWalkLift G c) =
      c + componentRootMap G (vertexComponentMap G c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      rw [hx, hy]
      module
  | single v r =>
      simp only [rootWalkLift, Finsupp.linearCombination_single, map_smul,
        flagD1_walkEdgeChain, smul_add]
      simp [componentRootMap, vertexComponentMap]

omit [Fintype V] in
/-- The graph boundary quotient is exactly the free `F₂`-space on connected
components.  This is the arbitrary-component form of the standard connected
incidence lemma. -/
theorem ker_vertexComponentMap_eq_range_flagD1 (G : SimpleGraph V) :
    LinearMap.ker (vertexComponentMap G) = LinearMap.range (flagD1 G) := by
  apply le_antisymm
  · intro c hc
    refine ⟨rootWalkLift G c, ?_⟩
    rw [flagD1_rootWalkLift, LinearMap.mem_ker.mp hc]
    simp
  · exact range_flagD1_le_ker_vertexComponentMap G

/-! ### Joined boundary in canonical split coordinates -/

def leftJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Gᶜ) : FlagEdge (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨Sym2.map Sum.inl e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : Gᶜ.Adj u v := by simpa using he
      simp [SimpleGraph.compl_adj, SimpleGraph.sum,
        (G.compl_adj u v).mp huv]

def rightJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (e : FlagEdge Hᶜ) : FlagEdge (G ⊕g H)ᶜ := by
  rcases e with ⟨e, he⟩
  refine ⟨Sym2.map Sum.inr e, ?_⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      have hww' : Hᶜ.Adj w w' := by simpa using he
      simp [SimpleGraph.compl_adj, SimpleGraph.sum,
        (H.compl_adj w w').mp hww']

def crossJoinedEdge (G : SimpleGraph V) (H : SimpleGraph W)
    (v : V) (w : W) : FlagEdge (G ⊕g H)ᶜ :=
  ⟨s(Sum.inl v, Sum.inr w), by
    simp [SimpleGraph.compl_adj, SimpleGraph.sum]⟩

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeEquiv_leftJoinedEdge
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Gᶜ) :
    joinedEdgeEquiv G H (leftJoinedEdge G H e) = Sum.inl e := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v => rfl

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeEquiv_crossJoinedEdge
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) :
    joinedEdgeEquiv G H (crossJoinedEdge G H v w) =
      Sum.inr (Sum.inl (v, w)) := by
  rfl

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeEquiv_rightJoinedEdge
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Hᶜ) :
    joinedEdgeEquiv G H (rightJoinedEdge G H e) =
      Sum.inr (Sum.inr e) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ w w' => rfl

def joinedVertexCoordinates :
    FlagChain0 (V ⊕ W) ≃ₗ[F₂] (FlagChain0 V × FlagChain0 W) :=
  Finsupp.sumFinsuppLEquivProdFinsupp F₂

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedVertexCoordinates_single_inl (v : V) (r : F₂) :
    joinedVertexCoordinates (V := V) (W := W) (Finsupp.single (Sum.inl v) r) =
      (Finsupp.single v r, 0) := by
  ext x <;> simp [joinedVertexCoordinates]

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedVertexCoordinates_single_inr (w : W) (r : F₂) :
    joinedVertexCoordinates (V := V) (W := W) (Finsupp.single (Sum.inr w) r) =
      (0, Finsupp.single w r) := by
  ext x <;> simp [joinedVertexCoordinates]

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeCoordinates_single_left
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Gᶜ) (r : F₂) :
    joinedEdgeCoordinates G H (Finsupp.single (leftJoinedEdge G H e) r) =
      (Finsupp.single e r, (0, 0)) := by
  simp [joinedEdgeCoordinates]

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeCoordinates_single_cross
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) (r : F₂) :
    joinedEdgeCoordinates G H (Finsupp.single (crossJoinedEdge G H v w) r) =
      (0, (Finsupp.single v 1 ⊗ₜ[F₂] Finsupp.single w r, 0)) := by
  simp [joinedEdgeCoordinates,
    finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

omit [Fintype V] [Fintype W] in
@[simp] lemma joinedEdgeCoordinates_single_right
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Hᶜ) (r : F₂) :
    joinedEdgeCoordinates G H (Finsupp.single (rightJoinedEdge G H e) r) =
      (0, (0, Finsupp.single e r)) := by
  simp [joinedEdgeCoordinates]

def rightMarginal (εB : FlagChain0 W →ₗ[F₂] F₂) :
    TensorProduct F₂ (FlagChain0 V) (FlagChain0 W) →ₗ[F₂] FlagChain0 V :=
  (TensorProduct.rid F₂ (FlagChain0 V)).toLinearMap.comp
    (εB.lTensor (FlagChain0 V))

def leftMarginal (εA : FlagChain0 V →ₗ[F₂] F₂) :
    TensorProduct F₂ (FlagChain0 V) (FlagChain0 W) →ₗ[F₂] FlagChain0 W :=
  (TensorProduct.lid F₂ (FlagChain0 W)).toLinearMap.comp
    (εA.rTensor (FlagChain0 W))

omit [Fintype V] [Fintype W] in
@[simp] lemma rightMarginal_tmul (εB : FlagChain0 W →ₗ[F₂] F₂)
    (a : FlagChain0 V) (b : FlagChain0 W) :
    rightMarginal εB (a ⊗ₜ b) = εB b • a := by
  simp [rightMarginal]

omit [Fintype V] [Fintype W] in
@[simp] lemma leftMarginal_tmul (εA : FlagChain0 V →ₗ[F₂] F₂)
    (a : FlagChain0 V) (b : FlagChain0 W) :
    leftMarginal εA (a ⊗ₜ b) = εA a • b := by
  simp [leftMarginal]

/-- The ordinary joined edge boundary, expressed in left-internal,
cross-matrix, right-internal coordinates. -/
def splitJoinD1 (G : SimpleGraph V) (H : SimpleGraph W) :
    (FlagChain1 Gᶜ ×
      (TensorProduct F₂ (FlagChain0 V) (FlagChain0 W) × FlagChain1 Hᶜ)) →ₗ[F₂]
      (FlagChain0 V × FlagChain0 W) where
  toFun c :=
    (flagD1 Gᶜ c.1 + rightMarginal (vertexAugmentation W) c.2.1,
      leftMarginal (vertexAugmentation V) c.2.1 + flagD1 Hᶜ c.2.2)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    all_goals abel
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
      RingHom.id_apply]

omit [Fintype V] [Fintype W] in
lemma joinedVertexCoordinates_edgeBoundary_left
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Gᶜ) :
    joinedVertexCoordinates (V := V) (W := W)
        (edgeBoundary (G ⊕g H)ᶜ (leftJoinedEdge G H e)) =
      (edgeBoundary Gᶜ e, 0) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      apply Prod.ext
      · ext x
        by_cases hu : u = x <;> by_cases hv : v = x <;>
          simp [joinedVertexCoordinates, edgeBoundary, leftJoinedEdge,
            hu, hv]
      · ext w
        simp [joinedVertexCoordinates, edgeBoundary, leftJoinedEdge]

omit [Fintype V] [Fintype W] in
lemma joinedVertexCoordinates_edgeBoundary_cross
    (G : SimpleGraph V) (H : SimpleGraph W) (v : V) (w : W) :
    joinedVertexCoordinates (V := V) (W := W)
        (edgeBoundary (G ⊕g H)ᶜ (crossJoinedEdge G H v w)) =
      (Finsupp.single v 1, Finsupp.single w 1) := by
  apply Prod.ext
  · ext x
    by_cases hv : v = x <;>
      simp [joinedVertexCoordinates, edgeBoundary, crossJoinedEdge,
        hv]
  · ext y
    by_cases hw : w = y <;>
      simp [joinedVertexCoordinates, edgeBoundary, crossJoinedEdge,
        hw]

omit [Fintype V] [Fintype W] in
lemma joinedVertexCoordinates_edgeBoundary_right
    (G : SimpleGraph V) (H : SimpleGraph W) (e : FlagEdge Hᶜ) :
    joinedVertexCoordinates (V := V) (W := W)
        (edgeBoundary (G ⊕g H)ᶜ (rightJoinedEdge G H e)) =
      (0, edgeBoundary Hᶜ e) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ w w' =>
      apply Prod.ext
      · ext v
        simp [joinedVertexCoordinates, edgeBoundary, rightJoinedEdge]
      · ext x
        by_cases hw : w = x <;> by_cases hw' : w' = x <;>
          simp [joinedVertexCoordinates, edgeBoundary, rightJoinedEdge,
            hw, hw']

omit [Fintype V] in
/-- Exact chain-level intertwining of the literal joined boundary with the
abstract split boundary. -/
theorem joinedVertexCoordinates_flagD1
    (G : SimpleGraph V) (H : SimpleGraph W) (c : FlagChain1 (G ⊕g H)ᶜ) :
    joinedVertexCoordinates (V := V) (W := W) (flagD1 (G ⊕g H)ᶜ c) =
      splitJoinD1 G H (joinedEdgeCoordinates G H c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single e r =>
      rcases e with ⟨e, he⟩
      induction e using Sym2.inductionOn with
      | _ x y =>
          cases x with
          | inl v =>
              cases y with
              | inl v' =>
                  have hvv' : Gᶜ.Adj v v' := by
                    simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using he
                  let eG : FlagEdge Gᶜ := ⟨s(v, v'), by simpa using hvv'⟩
                  have heq : (⟨s(Sum.inl v, Sum.inl v'), he⟩ :
                      FlagEdge (G ⊕g H)ᶜ) = leftJoinedEdge G H eG := by
                    apply Subtype.ext
                    rfl
                  rw [heq]
                  simp [flagD1, splitJoinD1,
                    joinedVertexCoordinates_edgeBoundary_left]
              | inr w =>
                  have heq : (⟨s(Sum.inl v, Sum.inr w), he⟩ :
                      FlagEdge (G ⊕g H)ᶜ) = crossJoinedEdge G H v w := by
                    apply Subtype.ext
                    rfl
                  rw [heq]
                  simp [flagD1, splitJoinD1, vertexAugmentation,
                    joinedVertexCoordinates_edgeBoundary_cross]
          | inr w =>
              cases y with
              | inl v =>
                  have heq : (⟨s(Sum.inr w, Sum.inl v), he⟩ :
                      FlagEdge (G ⊕g H)ᶜ) = crossJoinedEdge G H v w := by
                    apply Subtype.ext
                    exact Sym2.eq_swap
                  rw [heq]
                  simp [flagD1, splitJoinD1, vertexAugmentation,
                    joinedVertexCoordinates_edgeBoundary_cross]
              | inr w' =>
                  have hww' : Hᶜ.Adj w w' := by
                    simpa [SimpleGraph.compl_adj, SimpleGraph.sum] using he
                  let eH : FlagEdge Hᶜ := ⟨s(w, w'), by simpa using hww'⟩
                  have heq : (⟨s(Sum.inr w, Sum.inr w'), he⟩ :
                      FlagEdge (G ⊕g H)ᶜ) = rightJoinedEdge G H eH := by
                    apply Subtype.ext
                    rfl
                  rw [heq]
                  simp [flagD1, splitJoinD1,
                    joinedVertexCoordinates_edgeBoundary_right]

def FlagCycleSubmodule (K : SimpleGraph V) : Submodule F₂ (FlagChain1 K) :=
  LinearMap.ker (flagD1 K)

abbrev FlagCycle (K : SimpleGraph V) := FlagCycleSubmodule K

def SplitJoinCycleSubmodule (G : SimpleGraph V) (H : SimpleGraph W) :
    Submodule F₂
      (FlagChain1 Gᶜ ×
        (TensorProduct F₂ (FlagChain0 V) (FlagChain0 W) × FlagChain1 Hᶜ)) :=
  LinearMap.ker (splitJoinD1 G H)

abbrev SplitJoinCycle (G : SimpleGraph V) (H : SimpleGraph W) :=
  SplitJoinCycleSubmodule G H

/-- The literal cycle space of the joined complement is the kernel of the
split marginal boundary, with no dimension or source-normal-form assumption. -/
def joinedCycleEquivSplit (G : SimpleGraph V) (H : SimpleGraph W) :
    FlagCycle (G ⊕g H)ᶜ ≃ₗ[F₂] SplitJoinCycle G H where
  toFun c := ⟨joinedEdgeCoordinates G H c.1, by
    change splitJoinD1 G H (joinedEdgeCoordinates G H c.1) = 0
    rw [← joinedVertexCoordinates_flagD1]
    rw [c.2, map_zero]⟩
  invFun c := ⟨(joinedEdgeCoordinates G H).symm c.1, by
    apply (joinedVertexCoordinates (V := V) (W := W)).injective
    rw [joinedVertexCoordinates_flagD1,
      (joinedEdgeCoordinates G H).apply_symm_apply]
    rw [c.2, map_zero]⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp
  left_inv c := by
    apply Subtype.ext
    exact (joinedEdgeCoordinates G H).symm_apply_apply c.1
  right_inv c := by
    apply Subtype.ext
    exact (joinedEdgeCoordinates G H).apply_symm_apply c.1

end


end ExtremalUnorderedJoin
