/-
Canonical unordered-basis F₂ flag-homology formalization of Theorem 1.1 and
Proposition 3.1 of
"An Infinite Dense Counterexample Family for Extremal First Betti Numbers
of Flag Complexes".

Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import ExtremalFlagBetti
import ExtremalFlagBetti.Homology
import ExtremalFlagBetti.ActualHomology.JoinBridge

open Finset SimpleGraph

namespace ExtremalFlagBetti.ActualHomology

abbrev F₂ := ZMod 2

noncomputable section

section FlagChains

variable {V W : Type*} [Fintype V]
variable (G : SimpleGraph V)

/-- A genuine unoriented graph edge.  Unlike the ordered scratch, this
basis has no auxiliary vertex order and is functorial under graph isomorphism. -/
abbrev FlagEdge := {e : Sym2 V // e ∈ G.edgeSet}

/-- A triangular flag face, represented canonically by its three-element
vertex finset. -/
abbrev FlagTriangle :=
  {s : Finset V // s.card = 3 ∧ G.IsClique s}

abbrev FlagChain0 := V →₀ F₂
abbrev FlagChain1 := FlagEdge G →₀ F₂
abbrev FlagChain2 := FlagTriangle G →₀ F₂

/-- The two endpoints of an unordered edge, added over F₂. -/
def edgeBoundary (e : FlagEdge G) : FlagChain0 (V := V) :=
  Sym2.lift
    ⟨fun u v ↦ Finsupp.single u 1 + Finsupp.single v 1,
      fun u v ↦ by dsimp; rw [add_comm]⟩ e.1

/-- The three non-diagonal unordered pairs in a triangular clique.
Filtering by `edgeSet` removes the three diagonal pairs from `s.sym2`;
cliqueness guarantees that the remaining three pairs are graph edges. -/
noncomputable def triangleBoundary (t : FlagTriangle G) : FlagChain1 G := by
  classical
  let es : Finset (Sym2 V) := t.1.sym2.filter (fun e ↦ e ∈ G.edgeSet)
  exact es.attach.sum fun e ↦
    Finsupp.single ⟨e.1, (mem_filter.mp e.2).2⟩ 1

/-- The ordinary unoriented F₂ edge boundary. -/
def flagD1 : FlagChain1 G →ₗ[F₂] FlagChain0 (V := V) :=
  Finsupp.linearCombination F₂ (edgeBoundary G)

/-- The ordinary F₂ boundary of triangular flag faces. -/
noncomputable def flagD2 : FlagChain2 G →ₗ[F₂] FlagChain1 G :=
  Finsupp.linearCombination F₂ (triangleBoundary G)

lemma f2_add_self {M : Type*} [AddCommGroup M] [Module F₂ M] (x : M) : x + x = 0 := by
  calc
    x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
    _ = ((1 : F₂) + 1) • x := by rw [add_smul]
    _ = 0 := by
      have htwo : (1 : F₂) + 1 = 0 := by decide
      rw [htwo, zero_smul]

def flagEdgeOfAdj {u v : V} (h : G.Adj u v) : FlagEdge G :=
  ⟨s(u, v), G.mem_edgeSet.mpr h⟩

@[simp] lemma edgeBoundary_flagEdgeOfAdj
    {u v : V} (h : G.Adj u v) :
    edgeBoundary G (flagEdgeOfAdj G h) =
      Finsupp.single u 1 + Finsupp.single v 1 := by
  rfl

lemma flagD1_single_flagEdgeOfAdj
    {u v : V} (h : G.Adj u v) (a : F₂) :
    flagD1 G (Finsupp.single (flagEdgeOfAdj G h) a) =
      Finsupp.single u a + Finsupp.single v a := by
  simp [flagD1, edgeBoundary_flagEdgeOfAdj, smul_add]

lemma triangleBoundary_apply [DecidableEq V]
    (t : FlagTriangle G) (e : FlagEdge G) :
    triangleBoundary G t e = if e.1 ∈ t.1.sym2 then 1 else 0 := by
  classical
  let es : Finset (Sym2 V) := t.1.sym2.filter (fun z ↦ z ∈ G.edgeSet)
  change
    (es.attach.sum fun z ↦
      Finsupp.single ⟨z.1, (mem_filter.mp z.2).2⟩ 1) e = _
  simp only [Finsupp.finsetSum_apply]
  by_cases he : e.1 ∈ t.1.sym2
  · rw [if_pos he]
    let x : es := ⟨e.1, mem_filter.mpr ⟨he, e.2⟩⟩
    rw [Finset.sum_eq_single_of_mem x (by simp)]
    · simp [x]
    · intro z _ hzx
      have hne :
          (⟨z.1, (mem_filter.mp z.2).2⟩ : FlagEdge G) ≠ e := by
        intro h
        have hval : z.1 = e.1 :=
          congrArg (fun q : FlagEdge G ↦ q.1) h
        apply hzx
        exact Subtype.ext hval
      simp [hne]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro z _
    have hne :
        (⟨z.1, (mem_filter.mp z.2).2⟩ : FlagEdge G) ≠ e := by
      intro h
      apply he
      have hzmem : z.1 ∈ t.1.sym2 := (mem_filter.mp z.2).1
      have hval : z.1 = e.1 :=
        congrArg (fun q : FlagEdge G ↦ q.1) h
      rw [← hval]
      exact hzmem
    simp [hne]

lemma triangleBoundary_eq_three_edges [DecidableEq V]
    (t : FlagTriangle G) {a b c : V}
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (ht : t.1 = {a, b, c}) :
    triangleBoundary G t =
      Finsupp.single (flagEdgeOfAdj G hab) 1 +
      Finsupp.single (flagEdgeOfAdj G hac) 1 +
      Finsupp.single (flagEdgeOfAdj G hbc) 1 := by
  classical
  ext e
  rw [triangleBoundary_apply]
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : G.Adj x y := G.mem_edgeSet.mp he
      simp only [ht, Finset.mk_mem_sym2_iff]
      simp [flagEdgeOfAdj, Finsupp.single_apply, Subtype.ext_iff,
        Sym2.mk_eq_mk_iff, hxy.ne, hab.ne, hac.ne, hbc.ne]
      aesop

lemma flagD1_triangleBoundary (t : FlagTriangle G) :
    flagD1 G (triangleBoundary G t) = 0 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ht⟩ :=
    SimpleGraph.is3Clique_iff.mp
      (⟨t.2.2, t.2.1⟩ : G.IsNClique 3 t.1)
  rw [triangleBoundary_eq_three_edges G t hab hac hbc ht,
    map_add, map_add,
    flagD1_single_flagEdgeOfAdj G hab,
    flagD1_single_flagEdgeOfAdj G hac,
    flagD1_single_flagEdgeOfAdj G hbc]
  calc
    (Finsupp.single a (1 : F₂) + Finsupp.single b 1) +
        (Finsupp.single a 1 + Finsupp.single c 1) +
        (Finsupp.single b 1 + Finsupp.single c 1) =
        (Finsupp.single a 1 + Finsupp.single a 1) +
        (Finsupp.single b 1 + Finsupp.single b 1) +
        (Finsupp.single c 1 + Finsupp.single c 1) := by abel
    _ = 0 := by
      rw [f2_add_self (Finsupp.single a 1),
        f2_add_self (Finsupp.single b 1),
        f2_add_self (Finsupp.single c 1)]
      simp

/-- Every vertex of a three-element face occurs in exactly two of its
three non-diagonal pairs. -/
lemma flagD1_flagD2 (c : FlagChain2 G) : flagD1 G (flagD2 G c) = 0 := by
  classical
  rw [flagD2, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul, flagD1_triangleBoundary, smul_zero, Finsupp.sum_zero]

def FlagCycleSubmodule : Submodule F₂ (FlagChain1 G) :=
  LinearMap.ker (flagD1 G)

abbrev FlagCycle := FlagCycleSubmodule G

def flagD2Cycle : FlagChain2 G →ₗ[F₂] FlagCycle G where
  toFun c := ⟨flagD2 G c, flagD1_flagD2 G c⟩
  map_add' _ _ := by ext; simp [flagD2]
  map_smul' _ _ := by ext; simp [flagD2]

def FlagBoundarySubmodule : Submodule F₂ (FlagCycle G) :=
  LinearMap.range (flagD2Cycle G)

/-- Actual first simplicial homology of the graph's flag complex over F₂. -/
abbrev FlagH1F2 := FlagCycle G ⧸ FlagBoundarySubmodule G

noncomputable def flagBeta1F2 : ℕ := Module.finrank F₂ (FlagH1F2 G)

def FlagH1F2AtMostTwo : Prop := flagBeta1F2 G ≤ 2
def FlagH1F2ExactlyTwo : Prop := flagBeta1F2 G = 2

noncomputable def vertexAugmentation : FlagChain0 (V := V) →ₗ[F₂] F₂ :=
  Finsupp.lsum F₂ (fun _ ↦ LinearMap.id)

noncomputable def ReducedVertexChains : Submodule F₂ (FlagChain0 (V := V)) :=
  LinearMap.ker vertexAugmentation

private def walkChain {u v : V} : G.Walk u v → F₂ → FlagChain1 G
  | .nil, _ => 0
  | .cons h p, a =>
      Finsupp.single (flagEdgeOfAdj G h) a + walkChain p a

private lemma flagD1_walkChain {u v : V} (p : G.Walk u v) (a : F₂) :
    flagD1 G (walkChain G p a) =
      Finsupp.single u a + Finsupp.single v a := by
  induction p with
  | nil =>
      simp [walkChain, f2_add_self]
  | @cons u v w h p ih =>
      rw [walkChain, map_add, flagD1_single_flagEdgeOfAdj G h a, ih]
      calc
        (Finsupp.single u a + Finsupp.single v a) +
            (Finsupp.single v a + Finsupp.single w a) =
            Finsupp.single u a +
              (Finsupp.single v a + Finsupp.single v a) +
                Finsupp.single w a := by abel
        _ = Finsupp.single u a + Finsupp.single w a := by
          rw [f2_add_self (Finsupp.single v a)]
          simp

private lemma vertexAugmentation_edgeBoundary (e : FlagEdge G) :
    vertexAugmentation (edgeBoundary G e) = 0 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      simp only [edgeBoundary, Sym2.lift_mk, vertexAugmentation,
        Finsupp.lsum_apply]
      rw [Finsupp.sum_add_index'] <;> simp [f2_add_self]

private lemma vertexAugmentation_flagD1 (c : FlagChain1 G) :
    vertexAugmentation (flagD1 G c) = 0 := by
  classical
  rw [flagD1, Finsupp.linearCombination_apply, map_finsuppSum]
  simp only [map_smul, vertexAugmentation_edgeBoundary, smul_zero,
    Finsupp.sum_zero]

theorem range_flagD1_eq_reducedVertices_of_connected
    (hG : G.Connected) :
    LinearMap.range (flagD1 G) = ReducedVertexChains (V := V) := by
  classical
  apply le_antisymm
  · rintro _ ⟨c, rfl⟩
    change vertexAugmentation (flagD1 G c) = 0
    exact vertexAugmentation_flagD1 G c
  · intro z hz
    change vertexAugmentation z = 0 at hz
    let r : V := Classical.choice hG.nonempty
    let p : ∀ u : V, G.Walk u r := fun u ↦ Classical.choice (hG u r)
    refine ⟨z.sum (fun u a ↦ walkChain G (p u) a), ?_⟩
    rw [map_finsuppSum]
    simp_rw [flagD1_walkChain]
    rw [Finsupp.sum_add, Finsupp.sum_single, ← Finsupp.single_sum]
    have hsum : z.sum (fun _ a ↦ a) = 0 := by
      simpa [vertexAugmentation, Finsupp.lsum_apply] using hz
    rw [hsum]
    simp

private theorem finrank_reducedVertexChains (hV : Nonempty V) :
    Module.finrank F₂ (ReducedVertexChains (V := V)) =
      Fintype.card V - 1 := by
  classical
  letI : Nonempty V := hV
  have hsurj : Function.Surjective (vertexAugmentation (V := V)) := by
    intro a
    let r : V := Classical.choice hV
    refine ⟨Finsupp.single r a, ?_⟩
    simp [vertexAugmentation, Finsupp.lsum_apply]
  have hrange : LinearMap.range (vertexAugmentation (V := V)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hdim :=
    LinearMap.finrank_range_add_finrank_ker (vertexAugmentation (V := V))
  rw [hrange, finrank_top, Module.finrank_self,
    Module.finrank_finsupp_self] at hdim
  change Module.finrank F₂ (LinearMap.ker (vertexAugmentation (V := V))) = _
  omega

theorem finrank_flagCycles_of_connected (hG : G.Connected) :
    Module.finrank F₂ (FlagCycle G) =
      Fintype.card (FlagEdge G) - (Fintype.card V - 1) := by
  have hred := finrank_reducedVertexChains (V := V) hG.nonempty
  have hdim := LinearMap.finrank_range_add_finrank_ker (flagD1 G)
  rw [range_flagD1_eq_reducedVertices_of_connected G hG, hred,
    Module.finrank_finsupp_self] at hdim
  change Module.finrank F₂ (LinearMap.ker (flagD1 G)) = _
  exact Nat.eq_sub_of_add_eq (by simpa [add_comm] using hdim)

theorem flagBeta1_of_connected_triangleFree
    (hG : G.Connected) (htri : G.CliqueFree 3) :
    flagBeta1F2 G =
      Fintype.card (FlagEdge G) - (Fintype.card V - 1) := by
  classical
  letI : IsEmpty (FlagTriangle G) := ⟨by
    rintro ⟨s, hcard, hclique⟩
    exact htri s (⟨hclique, hcard⟩ : G.IsNClique 3 s)⟩
  have hchain2 (c : FlagChain2 G) : c = 0 := by
    ext t
    exact isEmptyElim t
  have hboundary : FlagBoundarySubmodule G = ⊥ := by
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      rw [hchain2 c]
      simp
    · exact bot_le
  change Module.finrank F₂ (FlagCycle G ⧸ FlagBoundarySubmodule G) = _
  rw [Submodule.finrank_quotient, hboundary, finrank_bot, Nat.sub_zero]
  exact finrank_flagCycles_of_connected G hG

noncomputable def componentAugmentation :
    (G.ConnectedComponent →₀ F₂) →ₗ[F₂] F₂ :=
  Finsupp.lsum F₂ (fun _ ↦ LinearMap.id)

noncomputable def ReducedComponentSubmodule :
    Submodule F₂ (G.ConnectedComponent →₀ F₂) :=
  LinearMap.ker (componentAugmentation G)

abbrev ReducedComponentCode := ReducedComponentSubmodule G

/-- Sum all vertex coefficients belonging to the same graph component. -/
noncomputable def vertexComponentMap :
    FlagChain0 (V := V) →ₗ[F₂] (G.ConnectedComponent →₀ F₂) :=
  Finsupp.lmapDomain F₂ F₂ G.connectedComponentMk

omit [Fintype V] in
/-- Aggregating first by connected component and then globally gives the
ordinary vertex augmentation. -/
lemma componentAugmentation_vertexComponentMap :
    (componentAugmentation G).comp (vertexComponentMap G) =
      vertexAugmentation (V := V) := by
  classical
  ext v
  simp [componentAugmentation, vertexComponentMap, vertexAugmentation]

omit [Fintype V] in
private lemma vertexComponentMap_edgeBoundary_eq_zero (e : FlagEdge G) :
    vertexComponentMap G (edgeBoundary G e) = 0 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huv : G.Adj u v := by simpa using he
      have hcomp : G.connectedComponentMk u = G.connectedComponentMk v :=
        ConnectedComponent.connectedComponentMk_eq_of_adj huv
      simp only [edgeBoundary, Sym2.lift_mk, vertexComponentMap,
        Finsupp.lmapDomain_apply, Finsupp.mapDomain_add,
        Finsupp.mapDomain_single]
      rw [hcomp]
      exact f2_add_self _

omit [Fintype V] in
private lemma range_flagD1_le_ker_vertexComponentMap :
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

private noncomputable def componentRoot (C : G.ConnectedComponent) : V :=
  C.out

omit [Fintype V] in
@[simp] private lemma connectedComponentMk_componentRoot
    (C : G.ConnectedComponent) :
    G.connectedComponentMk (componentRoot G C) = C := by
  exact Quot.out_eq C

private noncomputable def walkToComponentRoot (v : V) :
    G.Walk v (componentRoot G (G.connectedComponentMk v)) :=
  (ConnectedComponent.exact (by
    rw [connectedComponentMk_componentRoot])).some

private def walkEdgeChainToRoot :
    {u v : V} → G.Walk u v → FlagChain1 G
  | _, _, .nil => 0
  | u, _, .cons (v := v) h p =>
      Finsupp.single ⟨s(u, v), by simpa using h⟩ 1 +
        walkEdgeChainToRoot p

omit [Fintype V] in
private lemma flagD1_walkEdgeChainToRoot {u v : V}
    (p : G.Walk u v) :
    flagD1 G (walkEdgeChainToRoot G p) =
      Finsupp.single u 1 + Finsupp.single v 1 := by
  induction p with
  | nil =>
      simp only [walkEdgeChainToRoot, map_zero]
      exact (f2_add_self _).symm
  | @cons u v w h p ih =>
      simp only [walkEdgeChainToRoot, map_add]
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
          simp only [hv, add_zero, zero_add]

private noncomputable def componentRootMap :
    (G.ConnectedComponent →₀ F₂) →ₗ[F₂] FlagChain0 (V := V) :=
  Finsupp.lmapDomain F₂ F₂ (componentRoot G)

private noncomputable def rootWalkLift :
    FlagChain0 (V := V) →ₗ[F₂] FlagChain1 G :=
  Finsupp.linearCombination F₂
    (fun v ↦ walkEdgeChainToRoot G (walkToComponentRoot G v))

private lemma flagD1_rootWalkLift (c : FlagChain0 (V := V)) :
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
        flagD1_walkEdgeChainToRoot, smul_add]
      simp [componentRootMap, vertexComponentMap]

/-- The graph boundary quotient is exactly the free `F₂`-space on connected
components. -/
theorem ker_vertexComponentMap_eq_range_flagD1 :
    LinearMap.ker (vertexComponentMap G) = LinearMap.range (flagD1 G) := by
  apply le_antisymm
  · intro c hc
    refine ⟨rootWalkLift G c, ?_⟩
    rw [flagD1_rootWalkLift, LinearMap.mem_ker.mp hc]
    simp
  · exact range_flagD1_le_ker_vertexComponentMap G

theorem finrank_reducedComponentCode [Fintype G.ConnectedComponent]
    [DecidableRel G.Adj] :
    Module.finrank F₂ (ReducedComponentCode G) =
      Fintype.card G.ConnectedComponent - 1 := by
  classical
  by_cases hC : Nonempty G.ConnectedComponent
  · letI : Nonempty G.ConnectedComponent := hC
    have hsurj : Function.Surjective (componentAugmentation G) := by
      intro a
      let c : G.ConnectedComponent := Classical.choice hC
      refine ⟨Finsupp.single c a, ?_⟩
      simp [componentAugmentation]
    have hrange : LinearMap.range (componentAugmentation G) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hdim := LinearMap.finrank_range_add_finrank_ker (componentAugmentation G)
    rw [hrange, finrank_top, Module.finrank_self,
      Module.finrank_finsupp_self] at hdim
    change Module.finrank F₂ (LinearMap.ker (componentAugmentation G)) = _
    omega
  · haveI : IsEmpty G.ConnectedComponent := not_nonempty_iff.mp hC
    have hker : LinearMap.ker (componentAugmentation G) = ⊥ := by
      ext z
      constructor
      · intro _
        exact Subsingleton.elim z 0
      · rintro rfl
        exact Submodule.zero_mem _
    change Module.finrank F₂ (LinearMap.ker (componentAugmentation G)) = _
    rw [hker]
    simp

/-- Reduced component-code dimension is invariant under graph isomorphism. -/
theorem finrank_reducedComponentCode_congr
    {W : Type*} [Fintype W] (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : G ≃g H) :
    Module.finrank F₂ (ReducedComponentCode G) =
      Module.finrank F₂ (ReducedComponentCode H) := by
  rw [finrank_reducedComponentCode G, finrank_reducedComponentCode H]
  have hcard :
      Fintype.card G.ConnectedComponent =
        Fintype.card H.ConnectedComponent :=
    Fintype.card_congr e.connectedComponentEquiv
  omega

section Iso

variable [Fintype W] {H : SimpleGraph W}

def isoTriangleEquiv (e : G ≃g H) : FlagTriangle G ≃ FlagTriangle H where
  toFun t :=
    ⟨t.1.map e.toEquiv.toEmbedding, by
      constructor
      · simpa using t.2.1
      · intro x hx y hy huv
        change x ∈ t.1.map e.toEquiv.toEmbedding at hx
        change y ∈ t.1.map e.toEquiv.toEmbedding at hy
        rw [Finset.mem_map] at hx hy
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨v, hv, rfl⟩ := hy
        exact e.toHom.map_adj
          (t.2.2 hu hv (fun h ↦ huv (congrArg e h)))⟩
  invFun t :=
    ⟨t.1.map e.toEquiv.symm.toEmbedding, by
      constructor
      · simpa using t.2.1
      · intro x hx y hy huv
        change x ∈ t.1.map e.toEquiv.symm.toEmbedding at hx
        change y ∈ t.1.map e.toEquiv.symm.toEmbedding at hy
        rw [Finset.mem_map] at hx hy
        obtain ⟨u, hu, rfl⟩ := hx
        obtain ⟨v, hv, rfl⟩ := hy
        exact e.symm.toHom.map_adj
          (t.2.2 hu hv (fun h ↦ huv (congrArg e.symm h)))⟩
  left_inv t := by
    apply Subtype.ext
    ext u
    change u ∈ (t.1.map e.toEquiv.toEmbedding).map
      e.toEquiv.symm.toEmbedding ↔ u ∈ t.1
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, hw⟩
      have hvu : v = u := by
        calc
          v = e.symm (e v) := (e.symm_apply_apply v).symm
          _ = u := hw
      simpa [← hvu] using hv
    · intro hu
      exact ⟨e u, ⟨u, hu, rfl⟩, e.toEquiv.symm_apply_apply u⟩
  right_inv t := by
    apply Subtype.ext
    ext u
    change u ∈ (t.1.map e.toEquiv.symm.toEmbedding).map
      e.toEquiv.toEmbedding ↔ u ∈ t.1
    simp only [Finset.mem_map]
    constructor
    · rintro ⟨w, ⟨v, hv, rfl⟩, hw⟩
      have hvu : v = u := by
        calc
          v = e (e.symm v) := (e.apply_symm_apply v).symm
          _ = u := hw
      simpa [← hvu] using hv
    · intro hu
      exact ⟨e.symm u, ⟨u, hu, rfl⟩,
        e.toEquiv.apply_symm_apply u⟩

def isoVertexChains (e : G ≃g H) :
    FlagChain0 (V := V) ≃ₗ[F₂] FlagChain0 (V := W) :=
  Finsupp.mapDomain.linearEquiv F₂ F₂ e.toEquiv

def isoEdgeChains (e : G ≃g H) : FlagChain1 G ≃ₗ[F₂] FlagChain1 H :=
  Finsupp.mapDomain.linearEquiv F₂ F₂ e.mapEdgeSet

def isoTriangleChains (e : G ≃g H) : FlagChain2 G ≃ₗ[F₂] FlagChain2 H :=
  Finsupp.mapDomain.linearEquiv F₂ F₂ (isoTriangleEquiv G e)

private lemma iso_edgeBoundary (e : G ≃g H) (x : FlagEdge G) :
    isoVertexChains G e (edgeBoundary G x) =
      edgeBoundary H (e.mapEdgeSet x) := by
  rcases x with ⟨x, hx⟩
  induction x using Sym2.ind with
  | _ u v =>
      simp only [isoVertexChains, edgeBoundary, SimpleGraph.Iso.mapEdgeSet,
        SimpleGraph.Hom.mapEdgeSet, Finsupp.mapDomain.coe_linearEquiv,
        Sym2.lift_mk]
      rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single,
        Finsupp.mapDomain_single]
      change
        (Finsupp.single (e u) 1 + Finsupp.single (e v) 1) =
          Sym2.lift _ s(e u, e v)
      rw [Sym2.lift_mk]

private lemma iso_flagD1 (e : G ≃g H) (c : FlagChain1 G) :
    isoVertexChains G e (flagD1 G c) =
      flagD1 H (isoEdgeChains G e c) := by
  change
    ((isoVertexChains G e).toLinearMap.comp (flagD1 G)) c =
      ((flagD1 H).comp (isoEdgeChains G e).toLinearMap) c
  have hmap :
      (isoVertexChains G e).toLinearMap.comp (flagD1 G) =
        (flagD1 H).comp (isoEdgeChains G e).toLinearMap := by
    apply Finsupp.lhom_ext'
    intro x
    apply LinearMap.ext
    intro a
    simp [flagD1, isoEdgeChains, iso_edgeBoundary, smul_eq_mul]
  exact LinearMap.congr_fun hmap c

private lemma iso_triangleBoundary (e : G ≃g H) (t : FlagTriangle G) :
    isoEdgeChains G e (triangleBoundary G t) =
      triangleBoundary H (isoTriangleEquiv G e t) := by
  classical
  ext y
  let x : FlagEdge G := e.mapEdgeSet.symm y
  have hy : e.mapEdgeSet x = y := e.mapEdgeSet.apply_symm_apply y
  rw [← hy]
  change (Finsupp.mapDomain e.mapEdgeSet (triangleBoundary G t))
      (e.mapEdgeSet x) = _
  rw [Finsupp.mapDomain_apply e.mapEdgeSet.injective]
  rw [triangleBoundary_apply, triangleBoundary_apply]
  congr 1
  change (x.1 ∈ t.1.sym2) =
    ((e.mapEdgeSet x).1 ∈ (t.1.map e.toEquiv.toEmbedding).sym2)
  rw [Finset.sym2_map]
  change (x.1 ∈ t.1.sym2) =
    (Sym2.map e x.1 ∈ t.1.sym2.map e.toEquiv.toEmbedding.sym2Map)
  rw [Finset.mem_map]
  apply propext
  constructor
  · intro hx
    exact ⟨x.1, hx, rfl⟩
  · rintro ⟨z, hz, heq⟩
    have heq' : e.toEquiv.toEmbedding.sym2Map z =
        e.toEquiv.toEmbedding.sym2Map x.1 := by
      simpa using heq
    have hzx : z = x.1 := e.toEquiv.toEmbedding.sym2Map.injective heq'
    simpa [hzx] using hz

private lemma iso_flagD2 (e : G ≃g H) (c : FlagChain2 G) :
    isoEdgeChains G e (flagD2 G c) =
      flagD2 H (isoTriangleChains G e c) := by
  change
    ((isoEdgeChains G e).toLinearMap.comp (flagD2 G)) c =
      ((flagD2 H).comp (isoTriangleChains G e).toLinearMap) c
  have hmap :
      (isoEdgeChains G e).toLinearMap.comp (flagD2 G) =
        (flagD2 H).comp (isoTriangleChains G e).toLinearMap := by
    apply Finsupp.lhom_ext'
    intro t
    apply LinearMap.ext
    intro a
    simp [flagD2, isoTriangleChains, iso_triangleBoundary]
  exact LinearMap.congr_fun hmap c

private lemma iso_cycles_map (e : G ≃g H) :
    (FlagCycleSubmodule G).map (isoEdgeChains G e).toLinearMap =
      FlagCycleSubmodule H := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change flagD1 H (isoEdgeChains G e x) = 0
    rw [← iso_flagD1, hx, map_zero]
  · intro hy
    refine ⟨(isoEdgeChains G e).symm y, ?_, by simp⟩
    change flagD1 G ((isoEdgeChains G e).symm y) = 0
    apply (isoVertexChains G e).injective
    rw [iso_flagD1]
    simpa using hy

def isoCycleEquiv (e : G ≃g H) : FlagCycle G ≃ₗ[F₂] FlagCycle H :=
  (isoEdgeChains G e).ofSubmodules _ _ (iso_cycles_map G e)

private lemma iso_boundary_map (e : G ≃g H) :
    (FlagBoundarySubmodule G).map (isoCycleEquiv G e).toLinearMap =
      FlagBoundarySubmodule H := by
  ext y
  constructor
  · rintro ⟨x, ⟨c, rfl⟩, rfl⟩
    refine ⟨isoTriangleChains G e c, ?_⟩
    apply Subtype.ext
    change flagD2 H (isoTriangleChains G e c) =
      isoEdgeChains G e (flagD2 G c)
    exact (iso_flagD2 G e c).symm
  · rintro ⟨c, rfl⟩
    let c' := (isoTriangleChains G e).symm c
    refine ⟨flagD2Cycle G c', ⟨c', rfl⟩, ?_⟩
    apply Subtype.ext
    change isoEdgeChains G e (flagD2 G c') = flagD2 H c
    simpa [c'] using iso_flagD2 G e c'

/-- Graph isomorphisms now act by direct `Sym2.map` and `Finset.image`; no
sorting or transported linear order appears in the proof. -/
theorem flagH1F2_congr
    {W : Type*} [Fintype W]
    (H : SimpleGraph W) (e : G ≃g H) :
    Nonempty (FlagH1F2 G ≃ₗ[F₂] FlagH1F2 H) := by
  exact ⟨Submodule.Quotient.equiv _ _ (isoCycleEquiv G e)
    (iso_boundary_map G e)⟩

end Iso

end FlagChains

section PaperGraphs

/-- The sparse complement family in Equation (1) of the paper.  This public
definition is written out here so Comparator sees the same closed statement
dependency in `Challenge` and `Solution`. -/
def FamilyH (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 0 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
    (u.val = 0 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0) ∨
    (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 3) ∨
    (u.val = 4 ∧ 5 ≤ v.val) ∨ (v.val = 4 ∧ 5 ≤ u.val)
  symm := by
    intro u v h
    simpa only [and_comm, or_comm, or_left_comm, or_assoc] using h
  loopless := ⟨by intro u; omega⟩

instance (n : ℕ) : DecidableRel (FamilyH n).Adj := by
  unfold FamilyH
  infer_instance

/-- The dense family `Gₙ = complement Hₙ`. -/
def FamilyG (n : ℕ) : SimpleGraph (Fin n) := (FamilyH n)ᶜ

instance (n : ℕ) : DecidableRel (FamilyG n).Adj := by
  unfold FamilyG
  infer_instance

def CoreVertex {n : ℕ} (v : Fin n) : Prop :=
  v.val < 3 ∨ v.val = 4 ∨ v.val = 5

instance {n : ℕ} (v : Fin n) : Decidable (CoreVertex v) := by
  unfold CoreVertex
  infer_instance

def familyRetract {n : ℕ} (hn : 7 ≤ n) (v : Fin n) : Fin n :=
  if CoreVertex v then v else ⟨5, by omega⟩

def FamilyCore (n : ℕ) : SimpleGraph {v : Fin n // CoreVertex v} :=
  (FamilyG n).induce {v | CoreVertex v}

private def coreCoord {n : ℕ}
    (v : {v : Fin n // CoreVertex v}) : Fin 3 ⊕ Fin 2 :=
  if hbase : v.1.val < 3 then Sum.inl ⟨v.1.val, hbase⟩
  else if _hfour : v.1.val = 4 then Sum.inr 0
  else Sum.inr 1

private lemma coreCoord_injective {n : ℕ} :
    Function.Injective (coreCoord (n := n)) := by
  intro u v huv
  apply Subtype.ext
  apply Fin.ext
  have huCore := u.2
  have hvCore := v.2
  simp only [CoreVertex] at huCore hvCore
  unfold coreCoord at huv
  split_ifs at huv with hu3 hu4 hv3 hv4
  all_goals simp_all [Fin.ext_iff]

private lemma coreCoord_surjective {n : ℕ} (hn : 7 ≤ n) :
    Function.Surjective (coreCoord (n := n)) := by
  intro z
  rcases z with i | j
  · let v : {v : Fin n // CoreVertex v} :=
      ⟨⟨i.val, by omega⟩, Or.inl i.isLt⟩
    refine ⟨v, ?_⟩
    simp [coreCoord, v]
  · by_cases hj : j.val = 0
    · let v : {v : Fin n // CoreVertex v} :=
        ⟨⟨4, by omega⟩, Or.inr (Or.inl rfl)⟩
      refine ⟨v, ?_⟩
      have hj' : j = 0 := Fin.ext hj
      subst j
      simp [coreCoord, v]
    · have hj1 : j.val = 1 := by omega
      let v : {v : Fin n // CoreVertex v} :=
        ⟨⟨5, by omega⟩, Or.inr (Or.inr rfl)⟩
      refine ⟨v, ?_⟩
      have hj' : j = 1 := Fin.ext hj1
      subst j
      simp [coreCoord, v]

private noncomputable def coreCoordEquiv {n : ℕ} (hn : 7 ≤ n) :
    {v : Fin n // CoreVertex v} ≃ (Fin 3 ⊕ Fin 2) :=
  Equiv.ofBijective coreCoord
    ⟨coreCoord_injective, coreCoord_surjective hn⟩

private noncomputable def familyCoreGraphIso {n : ℕ} (hn : 7 ≤ n) :
    FamilyCore n ≃g completeBipartiteGraph (Fin 3) (Fin 2) where
  toEquiv := coreCoordEquiv hn
  map_rel_iff' := by
    intro u v
    change (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
      (coreCoordEquiv hn u) (coreCoordEquiv hn v) ↔
      (FamilyG n).Adj u.1 v.1
    have huOld : ExtremalFlagBetti.Homology.CoreVertex u.1 := by
      simpa [CoreVertex, ExtremalFlagBetti.Homology.CoreVertex] using u.2
    have hvOld : ExtremalFlagBetti.Homology.CoreVertex v.1 := by
      simpa [CoreVertex, ExtremalFlagBetti.Homology.CoreVertex] using v.2
    change (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
      (coreCoordEquiv hn u) (coreCoordEquiv hn v) ↔
      (ExtremalFlagBetti.FamilyG n).Adj u.1 v.1
    rw [ExtremalFlagBetti.Homology.family_core_adj_iff hn huOld hvOld]
    have huCore := u.2
    have hvCore := v.2
    simp only [CoreVertex] at huCore hvCore
    simp only [ExtremalFlagBetti.Homology.BaseVertex,
      ExtremalFlagBetti.Homology.ApexVertex]
    unfold coreCoordEquiv coreCoord
    simp only [Equiv.ofBijective_apply]
    split_ifs with hu3 hu4 hv3 hv4 <;>
      simp [completeBipartiteGraph] <;> omega

private lemma k32_connected :
    (completeBipartiteGraph (Fin 3) (Fin 2)).Connected := by
  refine ⟨?_⟩
  intro u v
  rcases u with u | u <;> rcases v with v | v
  · exact (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inl u) (Sum.inr 0) by simp).reachable.trans
      (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inr 0) (Sum.inl v) by simp).reachable
  · exact (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inl u) (Sum.inr v) by simp).reachable
  · exact (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inr u) (Sum.inl v) by simp).reachable
  · exact (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inr u) (Sum.inl 0) by simp).reachable.trans
      (show (completeBipartiteGraph (Fin 3) (Fin 2)).Adj
        (Sum.inl 0) (Sum.inr v) by simp).reachable

private lemma k32_triangleFree :
    (completeBipartiteGraph (Fin 3) (Fin 2)).CliqueFree 3 := by
  intro t ht
  classical
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ :=
    SimpleGraph.is3Clique_iff.mp ht
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
    simp [completeBipartiteGraph] at hab hac hbc

private lemma k32_edge_card :
    Fintype.card (FlagEdge (completeBipartiteGraph (Fin 3) (Fin 2))) = 6 := by
  rw [← ENat.coe_inj, Set.coe_fintypeCard]
  simpa using
    (encard_edgeSet_completeBipartiteGraph (W₁ := Fin 3) (W₂ := Fin 2))

theorem family_core_actual_h1_equiv {n : ℕ} (hn : 7 ≤ n) :
    flagBeta1F2 (FamilyCore n) = 2 := by
  let K := completeBipartiteGraph (Fin 3) (Fin 2)
  have hK : flagBeta1F2 K = 2 := by
    rw [flagBeta1_of_connected_triangleFree K k32_connected k32_triangleFree,
      k32_edge_card]
    norm_num
  rcases flagH1F2_congr (FamilyCore n) K (familyCoreGraphIso hn) with ⟨e⟩
  unfold flagBeta1F2
  rw [LinearEquiv.finrank_eq e]
  exact hK

end PaperGraphs

section UpperBoundReductions

variable {V : Type*} [Fintype V]

private noncomputable def coneTriangle
    (G : SimpleGraph V) (v x y : V)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : G.Adj x y) :
    FlagTriangle G := by
  classical
  let hcl : G.IsNClique 3 {v, x, y} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hvx, hvy, hxy⟩
  exact ⟨{v, x, y}, hcl.card_eq, hcl.isClique⟩

private lemma triangleBoundary_coneTriangle
    (G : SimpleGraph V) (v x y : V)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hxy : G.Adj x y) :
    triangleBoundary G (coneTriangle G v x y hvx hvy hxy) =
      Finsupp.single (flagEdgeOfAdj G hvx) 1 +
      Finsupp.single (flagEdgeOfAdj G hvy) 1 +
      Finsupp.single (flagEdgeOfAdj G hxy) 1 := by
  classical
  exact triangleBoundary_eq_three_edges G
    (coneTriangle G v x y hvx hvy hxy) hvx hvy hxy (by
      simp [coneTriangle])

private noncomputable def coneEdgeChain
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) (x : V) : FlagChain1 G := by
  classical
  exact if hx : x = v then 0
    else Finsupp.single (flagEdgeOfAdj G (hv x hx)) 1

private noncomputable def coneTriangleChain
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) (e : FlagEdge G) : FlagChain2 G := by
  classical
  exact Sym2.lift
    ⟨fun x y ↦
        if hx : x = v then 0
        else if hy : y = v then 0
        else if hxy : G.Adj x y then
          Finsupp.single (coneTriangle G v x y (hv x hx) (hv y hy) hxy) 1
        else 0,
      by
        intro x y
        classical
        by_cases hx : x = v <;> by_cases hy : y = v
        · simp [hx, hy]
        · simp [hx, hy]
        · simp [hx, hy]
        · by_cases hxy : G.Adj x y
          · have hyx : G.Adj y x := hxy.symm
            simp only [hx, hy, hxy, hyx, ↓reduceDIte]
            apply congrArg (fun t : FlagTriangle G ↦ Finsupp.single t 1)
            apply Subtype.ext
            simp [coneTriangle, Finset.ext_iff, or_comm, or_left_comm, or_assoc]
          · have hyx : ¬G.Adj y x := fun h ↦ hxy h.symm
            simp [hx, hy, hxy, hyx]⟩ e.1

private noncomputable def coneC0
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) :
    FlagChain0 (V := V) →ₗ[F₂] FlagChain1 G :=
  Finsupp.linearCombination F₂ (coneEdgeChain G v hv)

private noncomputable def coneC1
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) :
    FlagChain1 G →ₗ[F₂] FlagChain2 G :=
  Finsupp.linearCombination F₂ (coneTriangleChain G v hv)

private lemma cone_homotopy_on_edge
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) (e : FlagEdge G) :
    flagD2 G (coneC1 G v hv (Finsupp.single e 1)) +
        coneC0 G v hv (flagD1 G (Finsupp.single e 1)) =
      Finsupp.single e 1 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : G.Adj x y := G.mem_edgeSet.mp he
      by_cases hx : x = v
      · subst x
        have hy : y ≠ v := hxy.ne.symm
        have heq :
            (⟨s(v, y), he⟩ : FlagEdge G) = flagEdgeOfAdj G hxy :=
          Subtype.ext rfl
        have hcone : coneC1 G v hv
            (Finsupp.single (⟨s(v, y), he⟩ : FlagEdge G) 1) = 0 := by
          simp [coneC1, coneTriangleChain]
        rw [hcone, map_zero, zero_add]
        rw [heq, flagD1_single_flagEdgeOfAdj G hxy]
        simp [coneC0, coneEdgeChain, hy]
      · by_cases hy : y = v
        · subst y
          have hvx : G.Adj v x := hxy.symm
          have heq :
              (⟨s(x, v), he⟩ : FlagEdge G) = flagEdgeOfAdj G hxy :=
            Subtype.ext rfl
          have hcone : coneC1 G v hv
              (Finsupp.single (⟨s(x, v), he⟩ : FlagEdge G) 1) = 0 := by
            simp [coneC1, coneTriangleChain]
          rw [hcone, map_zero, zero_add]
          rw [heq, flagD1_single_flagEdgeOfAdj G hxy]
          simp [coneC0, coneEdgeChain, hx,
            hvx, flagEdgeOfAdj, Sym2.eq_swap]
        · have hvx : G.Adj v x := hv x hx
          have hvy : G.Adj v y := hv y hy
          have heq :
              (⟨s(x, y), he⟩ : FlagEdge G) = flagEdgeOfAdj G hxy :=
            Subtype.ext rfl
          rw [heq, flagD1_single_flagEdgeOfAdj G hxy]
          rw [show coneC1 G v hv
                (Finsupp.single (flagEdgeOfAdj G hxy) 1) =
              Finsupp.single (coneTriangle G v x y hvx hvy hxy) 1 by
            simp [coneC1, coneTriangleChain, flagEdgeOfAdj, hx, hy, hxy]]
          rw [show flagD2 G
                (Finsupp.single (coneTriangle G v x y hvx hvy hxy) 1) =
              triangleBoundary G (coneTriangle G v x y hvx hvy hxy) by
            simp [flagD2]]
          rw [triangleBoundary_coneTriangle G v x y hvx hvy hxy]
          simp [coneC0, coneEdgeChain, hx, hy, hvx, hvy, flagEdgeOfAdj]
          let ex : FlagChain1 G := Finsupp.single (flagEdgeOfAdj G hvx) 1
          let ey : FlagChain1 G := Finsupp.single (flagEdgeOfAdj G hvy) 1
          let ez : FlagChain1 G := Finsupp.single (flagEdgeOfAdj G hxy) 1
          change ((ex + ey) + ez) + (ex + ey) = ez
          calc
            ((ex + ey) + ez) + (ex + ey) =
                (ex + ex) + (ey + ey) + ez := by abel
            _ = ez := by rw [f2_add_self ex, f2_add_self ey]; simp

private lemma cone_homotopy
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) (z : FlagChain1 G) :
    flagD2 G (coneC1 G v hv z) + coneC0 G v hv (flagD1 G z) = z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
      simp only [map_add]
      calc
        _ = (flagD2 G (coneC1 G v hv x) + coneC0 G v hv (flagD1 G x)) +
            (flagD2 G (coneC1 G v hv y) + coneC0 G v hv (flagD1 G y)) := by
              abel
        _ = x + y := by rw [hx, hy]
  | single e a =>
      have hb := cone_homotopy_on_edge G v hv e
      rw [← Finsupp.smul_single_one]
      simp only [map_smul, smul_add]
      simpa only [smul_add] using congrArg (fun c : FlagChain1 G ↦ a • c) hb

private lemma cone_homotopy_on_cycle
    (G : SimpleGraph V) (v : V)
    (hv : ∀ w, w ≠ v → G.Adj v w) (z : FlagCycle G) :
    flagD2 G (coneC1 G v hv z.1) = z.1 := by
  have hhom := cone_homotopy G v hv z.1
  have hz : flagD1 G z.1 = 0 := z.2
  simpa [hz] using hhom

theorem flag_h1_cone_at_most_two
    (G : SimpleGraph V)
    (v : V) (hv : ∀ w, w ≠ v → G.Adj v w) :
    FlagH1F2AtMostTwo G := by
  classical
  have htop : FlagBoundarySubmodule G = ⊤ := by
    apply top_unique
    intro z _
    refine ⟨coneC1 G v hv z.1, ?_⟩
    apply Subtype.ext
    exact cone_homotopy_on_cycle G v hv z
  unfold FlagH1F2AtMostTwo flagBeta1F2
  change Module.finrank F₂ (FlagCycle G ⧸ FlagBoundarySubmodule G) ≤ 2
  rw [Submodule.finrank_quotient, htop, finrank_top, Nat.sub_self]
  omega

private abbrev LeafU (Q : SimpleGraph V) (w : V) :=
  {x : V // x ≠ w ∧ ¬Q.Adj w x}

private abbrev LeafRemainder
    (Q : SimpleGraph V) (w : V) : SimpleGraph (LeafU Q w) :=
  Q.induce {x | x ≠ w ∧ ¬Q.Adj w x}

private abbrev LeafComponentGraph
    (Q : SimpleGraph V) (w : V) : SimpleGraph (LeafU Q w) :=
  (LeafRemainder Q w)ᶜ

private lemma leaf_q_adj_vw
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    Q.Adj v w :=
  (hleaf w).2 rfl

private lemma leaf_v_ne_w
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    v ≠ w :=
  (leaf_q_adj_vw Q v w hleaf).ne

private lemma leaf_u_ne_v
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (x : LeafU Q w) : x.1 ≠ v := by
  intro hx
  apply x.2.2
  rw [hx]
  exact (leaf_q_adj_vw Q v w hleaf).symm

private lemma leaf_compl_adj_vu
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (x : LeafU Q w) : Qᶜ.Adj v x.1 := by
  apply (Q.compl_adj v x.1).2
  refine ⟨(leaf_u_ne_v Q v w hleaf x).symm, ?_⟩
  simpa [hleaf x.1] using x.2.1

private lemma leaf_compl_adj_wu
    (Q : SimpleGraph V) (w : V) (x : LeafU Q w) :
    Qᶜ.Adj w x.1 := by
  exact (Q.compl_adj w x.1).2 ⟨x.2.1.symm, x.2.2⟩

private lemma leaf_component_adj_of_compl_adj
    (Q : SimpleGraph V) (w : V) (x y : LeafU Q w)
    (hxy : Qᶜ.Adj x.1 y.1) :
    (LeafComponentGraph Q w).Adj x y := by
  have hdata := (Q.compl_adj x.1 y.1).1 hxy
  apply ((LeafRemainder Q w).compl_adj x y).2
  refine ⟨?_, ?_⟩
  · intro h
    exact hdata.1 (congrArg Subtype.val h)
  · simpa [LeafRemainder] using hdata.2

private def leafVEdge
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (x : LeafU Q w) : FlagEdge Qᶜ :=
  flagEdgeOfAdj Qᶜ (leaf_compl_adj_vu Q v w hleaf x)

private def leafWEdge
    (Q : SimpleGraph V) (w : V)
    (x : LeafU Q w) : FlagEdge Qᶜ :=
  flagEdgeOfAdj Qᶜ (leaf_compl_adj_wu Q w x)

private theorem leafVEdge_injective
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    Function.Injective (leafVEdge Q v w hleaf) := by
  intro x y hxy
  apply Subtype.ext
  have hs : s(v, x.1) = s(v, y.1) :=
    congrArg (fun e : FlagEdge Qᶜ ↦ e.1) hxy
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact hs.2
  · exact (leaf_u_ne_v Q v w hleaf x hs.2).elim

private theorem leafWEdge_injective
    (Q : SimpleGraph V) (w : V) :
    Function.Injective (leafWEdge Q w) := by
  intro x y hxy
  apply Subtype.ext
  have hs : s(w, x.1) = s(w, y.1) :=
    congrArg (fun e : FlagEdge Qᶜ ↦ e.1) hxy
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact hs.2
  · exact (x.2.1 hs.2).elim

private lemma leafVEdge_ne_leafWEdge
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (x y : LeafU Q w) :
    leafVEdge Q v w hleaf x ≠ leafWEdge Q w y := by
  intro hxy
  have hs : s(v, x.1) = s(w, y.1) :=
    congrArg (fun e : FlagEdge Qᶜ ↦ e.1) hxy
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact (leaf_v_ne_w Q v w hleaf hs.1).elim
  · exact (leaf_u_ne_v Q v w hleaf y hs.1.symm).elim

private noncomputable def leafArmProjection
    (Q : SimpleGraph V) (w : V) :
    FlagChain1 Qᶜ →ₗ[F₂] FlagChain0 (V := LeafU Q w) :=
  Finsupp.lcomapDomain (leafWEdge Q w) (leafWEdge_injective Q w)

private noncomputable def leafArmLift
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    FlagChain0 (V := LeafU Q w) →ₗ[F₂] FlagChain1 Qᶜ :=
  Finsupp.lmapDomain F₂ F₂ (leafVEdge Q v w hleaf) +
    Finsupp.lmapDomain F₂ F₂ (leafWEdge Q w)

private lemma leafArmProjection_armLift
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (a : FlagChain0 (V := LeafU Q w)) :
    leafArmProjection Q w (leafArmLift Q v w hleaf a) = a := by
  classical
  change Finsupp.lcomapDomain (R := F₂) (M := F₂)
      (leafWEdge Q w) (leafWEdge_injective Q w)
      (Finsupp.mapDomain (leafVEdge Q v w hleaf) a +
        Finsupp.mapDomain (leafWEdge Q w) a) = a
  rw [map_add]
  have hv : Finsupp.comapDomain (leafWEdge Q w)
      (Finsupp.mapDomain (leafVEdge Q v w hleaf) a)
      (leafWEdge_injective Q w).injOn = 0 := by
    ext x
    rw [Finsupp.comapDomain_apply]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨y, hy⟩
    exact leafVEdge_ne_leafWEdge Q v w hleaf y x hy
  have hv' :
      (Finsupp.lcomapDomain (R := F₂) (M := F₂)
        (leafWEdge Q w) (leafWEdge_injective Q w))
        (Finsupp.mapDomain (leafVEdge Q v w hleaf) a) = 0 := hv
  rw [hv', zero_add]
  exact Finsupp.comapDomain_mapDomain
    (leafWEdge Q w) (leafWEdge_injective Q w) a

private lemma flagD1_leafArmLift
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (a : FlagChain0 (V := LeafU Q w)) :
    flagD1 Qᶜ (leafArmLift Q v w hleaf a) =
      Finsupp.single v (vertexAugmentation a) +
        Finsupp.single w (vertexAugmentation a) := by
  classical
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      calc
        flagD1 Qᶜ (leafArmLift Q v w hleaf (a + b)) =
            flagD1 Qᶜ
              (leafArmLift Q v w hleaf a +
                leafArmLift Q v w hleaf b) := by rw [map_add]
        _ = flagD1 Qᶜ (leafArmLift Q v w hleaf a) +
              flagD1 Qᶜ (leafArmLift Q v w hleaf b) := by rw [map_add]
        _ = (Finsupp.single v (vertexAugmentation a) +
              Finsupp.single w (vertexAugmentation a)) +
            (Finsupp.single v (vertexAugmentation b) +
              Finsupp.single w (vertexAugmentation b)) := by rw [ha, hb]
        _ = (Finsupp.single v (vertexAugmentation a) +
              Finsupp.single v (vertexAugmentation b)) +
            (Finsupp.single w (vertexAugmentation a) +
              Finsupp.single w (vertexAugmentation b)) := by abel
        _ = Finsupp.single v (vertexAugmentation (a + b)) +
            Finsupp.single w (vertexAugmentation (a + b)) := by
          rw [← Finsupp.single_add, ← Finsupp.single_add, map_add]
  | single x r =>
      have hV : leafVEdge Q v w hleaf x =
          flagEdgeOfAdj Qᶜ (leaf_compl_adj_vu Q v w hleaf x) := rfl
      have hW : leafWEdge Q w x =
          flagEdgeOfAdj Qᶜ (leaf_compl_adj_wu Q w x) := rfl
      rw [show leafArmLift Q v w hleaf (Finsupp.single x r) =
          Finsupp.single (leafVEdge Q v w hleaf x) r +
            Finsupp.single (leafWEdge Q w x) r by
        simp [leafArmLift]]
      rw [map_add, hV, hW,
        flagD1_single_flagEdgeOfAdj, flagD1_single_flagEdgeOfAdj]
      have hx2 := f2_add_self (Finsupp.single x.1 r)
      have haug : vertexAugmentation (Finsupp.single x r) = r := by
        simp [vertexAugmentation, Finsupp.lsum_apply]
      rw [haug]
      calc
        (Finsupp.single v r + Finsupp.single x.1 r) +
            (Finsupp.single w r + Finsupp.single x.1 r) =
          Finsupp.single v r + Finsupp.single w r +
            (Finsupp.single x.1 r + Finsupp.single x.1 r) := by abel
        _ = Finsupp.single v r + Finsupp.single w r := by
          rw [hx2]
          simp

private lemma leafArmLift_cycle_of_reduced
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (a : FlagChain0 (V := LeafU Q w))
    (ha : vertexAugmentation a = 0) :
    flagD1 Qᶜ (leafArmLift Q v w hleaf a) = 0 := by
  rw [flagD1_leafArmLift Q v w hleaf a, ha]
  simp

private lemma leafArmProjection_single_leafWEdge
    (Q : SimpleGraph V) (w : V) (x : LeafU Q w) (r : F₂) :
    leafArmProjection Q w
        (Finsupp.single (leafWEdge Q w x) r) =
      Finsupp.single x r := by
  classical
  exact Finsupp.comapDomain_single
    (leafWEdge Q w) x r (leafWEdge_injective Q w).injOn

private lemma flagD1_single_leafWEdge
    (Q : SimpleGraph V) (w : V) (x : LeafU Q w) (r : F₂) :
    flagD1 Qᶜ (Finsupp.single (leafWEdge Q w x) r) =
      Finsupp.single w r + Finsupp.single x.1 r := by
  exact flagD1_single_flagEdgeOfAdj Qᶜ
    (leaf_compl_adj_wu Q w x) r

private lemma leafArmProjection_single_away
    (Q : SimpleGraph V) (w x y : V)
    (hxy : Qᶜ.Adj x y) (hx : x ≠ w) (hy : y ≠ w)
    (r : F₂) :
    leafArmProjection Q w
        (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) r) = 0 := by
  classical
  apply Finsupp.comapDomain_single_of_not_mem_range
  rintro ⟨u, hu⟩
  have hs : s(w, u.1) = s(x, y) :=
    congrArg (fun e : FlagEdge Qᶜ ↦ e.1) hu
  rw [Sym2.eq_iff] at hs
  rcases hs with hs | hs
  · exact hx hs.1.symm
  · exact hy hs.1.symm

private lemma leafArmProjection_augmentation
    (Q : SimpleGraph V) (w : V) (z : FlagChain1 Qᶜ) :
    vertexAugmentation (leafArmProjection Q w z) = flagD1 Qᶜ z w := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add, Finsupp.add_apply, ha, hb]
  | single e r =>
      rcases e with ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
          have hxy : Qᶜ.Adj x y := Qᶜ.mem_edgeSet.mp he
          have heq :
              (⟨s(x, y), he⟩ : FlagEdge Qᶜ) =
                flagEdgeOfAdj Qᶜ hxy := Subtype.ext rfl
          by_cases hx : x = w
          · subst x
            have hdata := (Q.compl_adj w y).1 hxy
            let yu : LeafU Q w := ⟨y, hdata.1.symm, hdata.2⟩
            have heqW :
                flagEdgeOfAdj Qᶜ hxy = leafWEdge Q w yu :=
              Subtype.ext rfl
            rw [heq, heqW,
              leafArmProjection_single_leafWEdge Q w yu r,
              flagD1_single_leafWEdge Q w yu r]
            have hyw : yu.1 ≠ w := yu.2.1
            simp [vertexAugmentation, Finsupp.lsum_apply, hyw.symm]
          · by_cases hy : y = w
            · subst y
              have hdata := (Q.compl_adj x w).1 hxy
              let xu : LeafU Q w := ⟨x, hdata.1, fun h ↦ hdata.2 h.symm⟩
              have heqW :
                  flagEdgeOfAdj Qᶜ hxy = leafWEdge Q w xu := by
                apply Subtype.ext
                exact Sym2.eq_swap
              rw [heq, heqW,
                leafArmProjection_single_leafWEdge Q w xu r,
                flagD1_single_leafWEdge Q w xu r]
              have hxw : xu.1 ≠ w := xu.2.1
              simp [vertexAugmentation, Finsupp.lsum_apply, hxw.symm]
            · rw [heq,
                leafArmProjection_single_away Q w x y hxy hx hy r,
                flagD1_single_flagEdgeOfAdj Qᶜ hxy]
              simp [vertexAugmentation, Finsupp.lsum_apply, hx, hy]

private lemma leafArmProjection_cycle_reduced
    (Q : SimpleGraph V) (w : V) (z : FlagCycle Qᶜ) :
    vertexAugmentation (leafArmProjection Q w z.1) = 0 := by
  rw [leafArmProjection_augmentation Q w z.1, z.2]
  rfl

private def leafUOfWAdj
    (Q : SimpleGraph V) (w x : V) (h : Qᶜ.Adj w x) : LeafU Q w :=
  ⟨x, ((Q.compl_adj w x).1 h).1.symm, ((Q.compl_adj w x).1 h).2⟩

private lemma leafArmProjection_single_w_adj
    (Q : SimpleGraph V) (w x : V) (h : Qᶜ.Adj w x) (r : F₂) :
    leafArmProjection Q w
        (Finsupp.single (flagEdgeOfAdj Qᶜ h) r) =
      Finsupp.single (leafUOfWAdj Q w x h) r := by
  have heq : flagEdgeOfAdj Qᶜ h =
      leafWEdge Q w (leafUOfWAdj Q w x h) := Subtype.ext rfl
  rw [heq, leafArmProjection_single_leafWEdge]

private lemma leafArmProjection_single_adj_w
    (Q : SimpleGraph V) (w x : V) (h : Qᶜ.Adj x w) (r : F₂) :
    leafArmProjection Q w
        (Finsupp.single (flagEdgeOfAdj Qᶜ h) r) =
      Finsupp.single (leafUOfWAdj Q w x h.symm) r := by
  have heq : flagEdgeOfAdj Qᶜ h =
      leafWEdge Q w (leafUOfWAdj Q w x h.symm) := by
    apply Subtype.ext
    exact Sym2.eq_swap
  rw [heq, leafArmProjection_single_leafWEdge]

private lemma leafArmProjection_triangle_component_zero
    (Q : SimpleGraph V) (w : V) (t : FlagTriangle Qᶜ) :
    vertexComponentMap (LeafComponentGraph Q w)
        (leafArmProjection Q w (triangleBoundary Qᶜ t)) = 0 := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ht⟩ :=
    SimpleGraph.is3Clique_iff.mp
      (⟨t.2.2, t.2.1⟩ : Qᶜ.IsNClique 3 t.1)
  rw [triangleBoundary_eq_three_edges Qᶜ t hab hac hbc ht]
  by_cases ha : a = w
  · subst a
    let bu : LeafU Q w := leafUOfWAdj Q w b hab
    let cu : LeafU Q w := leafUOfWAdj Q w c hac
    have hK : (LeafComponentGraph Q w).Adj bu cu :=
      leaf_component_adj_of_compl_adj Q w bu cu hbc
    have hproj :
        leafArmProjection Q w
            (Finsupp.single (flagEdgeOfAdj Qᶜ hab) 1 +
              Finsupp.single (flagEdgeOfAdj Qᶜ hac) 1 +
              Finsupp.single (flagEdgeOfAdj Qᶜ hbc) 1) =
          edgeBoundary (LeafComponentGraph Q w)
            (flagEdgeOfAdj (LeafComponentGraph Q w) hK) := by
      rw [map_add, map_add,
        leafArmProjection_single_w_adj Q w b hab,
        leafArmProjection_single_w_adj Q w c hac,
        leafArmProjection_single_away Q w b c hbc
          (leafUOfWAdj Q w b hab).2.1
          (leafUOfWAdj Q w c hac).2.1]
      rw [edgeBoundary_flagEdgeOfAdj]
      simp [bu, cu]
    rw [hproj]
    exact vertexComponentMap_edgeBoundary_eq_zero
      (LeafComponentGraph Q w) _
  · by_cases hb : b = w
    · subst b
      let au : LeafU Q w := leafUOfWAdj Q w a hab.symm
      let cu : LeafU Q w := leafUOfWAdj Q w c hbc
      have hK : (LeafComponentGraph Q w).Adj au cu :=
        leaf_component_adj_of_compl_adj Q w au cu hac
      have hproj :
          leafArmProjection Q w
              (Finsupp.single (flagEdgeOfAdj Qᶜ hab) 1 +
                Finsupp.single (flagEdgeOfAdj Qᶜ hac) 1 +
                Finsupp.single (flagEdgeOfAdj Qᶜ hbc) 1) =
            edgeBoundary (LeafComponentGraph Q w)
              (flagEdgeOfAdj (LeafComponentGraph Q w) hK) := by
        rw [map_add, map_add,
          leafArmProjection_single_adj_w Q w a hab,
          leafArmProjection_single_away Q w a c hac
            (leafUOfWAdj Q w a hab.symm).2.1
            (leafUOfWAdj Q w c hbc).2.1,
          leafArmProjection_single_w_adj Q w c hbc]
        rw [edgeBoundary_flagEdgeOfAdj]
        simp [au, cu]
      rw [hproj]
      exact vertexComponentMap_edgeBoundary_eq_zero
        (LeafComponentGraph Q w) _
    · by_cases hc : c = w
      · subst c
        let au : LeafU Q w := leafUOfWAdj Q w a hac.symm
        let bu : LeafU Q w := leafUOfWAdj Q w b hbc.symm
        have hK : (LeafComponentGraph Q w).Adj au bu :=
          leaf_component_adj_of_compl_adj Q w au bu hab
        have hproj :
            leafArmProjection Q w
                (Finsupp.single (flagEdgeOfAdj Qᶜ hab) 1 +
                  Finsupp.single (flagEdgeOfAdj Qᶜ hac) 1 +
                  Finsupp.single (flagEdgeOfAdj Qᶜ hbc) 1) =
              edgeBoundary (LeafComponentGraph Q w)
                (flagEdgeOfAdj (LeafComponentGraph Q w) hK) := by
          rw [map_add, map_add,
            leafArmProjection_single_away Q w a b hab ha hb,
            leafArmProjection_single_adj_w Q w a hac,
            leafArmProjection_single_adj_w Q w b hbc]
          rw [edgeBoundary_flagEdgeOfAdj]
          simp [au, bu]
        rw [hproj]
        exact vertexComponentMap_edgeBoundary_eq_zero
          (LeafComponentGraph Q w) _
      · simp only [map_add]
        rw [leafArmProjection_single_away Q w a b hab ha hb,
          leafArmProjection_single_away Q w a c hac ha hc,
          leafArmProjection_single_away Q w b c hbc hb hc]
        simp

private lemma leafArmProjection_flagD2_component_zero
    (Q : SimpleGraph V) (w : V) (c : FlagChain2 Qᶜ) :
    vertexComponentMap (LeafComponentGraph Q w)
        (leafArmProjection Q w (flagD2 Qᶜ c)) = 0 := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single t r =>
      simp only [flagD2, Finsupp.linearCombination_single, map_smul,
        leafArmProjection_triangle_component_zero, smul_zero]

private noncomputable def leafCycleCode
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    FlagCycle Qᶜ →ₗ[F₂] ReducedComponentCode (LeafComponentGraph Q w) where
  toFun z :=
    ⟨vertexComponentMap (LeafComponentGraph Q w)
        (leafArmProjection Q w z.1), by
      change componentAugmentation (LeafComponentGraph Q w)
          (vertexComponentMap (LeafComponentGraph Q w)
            (leafArmProjection Q w z.1)) = 0
      have hcomp := LinearMap.congr_fun
        (componentAugmentation_vertexComponentMap
          (LeafComponentGraph Q w))
        (leafArmProjection Q w z.1)
      change componentAugmentation (LeafComponentGraph Q w)
          (vertexComponentMap (LeafComponentGraph Q w)
            (leafArmProjection Q w z.1)) =
        vertexAugmentation (leafArmProjection Q w z.1) at hcomp
      rw [hcomp]
      exact leafArmProjection_cycle_reduced Q w z⟩
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

private lemma leafCycleCode_flagD2Cycle
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w)
    (c : FlagChain2 Qᶜ) :
    leafCycleCode Q v w hleaf (flagD2Cycle Qᶜ c) = 0 := by
  apply Subtype.ext
  exact leafArmProjection_flagD2_component_zero Q w c

private lemma leaf_boundaries_le_cycleCode_ker
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    FlagBoundarySubmodule Qᶜ ≤ LinearMap.ker (leafCycleCode Q v w hleaf) := by
  rintro _ ⟨c, rfl⟩
  exact leafCycleCode_flagD2Cycle Q v w hleaf c

private lemma leaf_compl_adj_v_of_ne
    (Q : SimpleGraph V) (v w x : V)
    (hleaf : ∀ y, Q.Adj v y ↔ y = w)
    (hxv : x ≠ v) (hxw : x ≠ w) :
    Qᶜ.Adj v x := by
  apply (Q.compl_adj v x).2
  refine ⟨hxv.symm, ?_⟩
  rw [hleaf x]
  exact hxw

private noncomputable def leafConeEdgeChain
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ y, Q.Adj v y ↔ y = w)
    (x : V) : FlagChain1 Qᶜ := by
  classical
  exact if hxv : x = v then 0
    else if hxw : x = w then 0
    else Finsupp.single
      (flagEdgeOfAdj Qᶜ
        (leaf_compl_adj_v_of_ne Q v w x hleaf hxv hxw)) 1

private noncomputable def leafConeTriangleChain
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (e : FlagEdge Qᶜ) : FlagChain2 Qᶜ := by
  classical
  exact Sym2.lift
    ⟨fun x y ↦
        if hxv : x = v then 0
        else if hyv : y = v then 0
        else if hxw : x = w then 0
        else if hyw : y = w then 0
        else if hxy : Qᶜ.Adj x y then
          Finsupp.single
            (coneTriangle Qᶜ v x y
              (leaf_compl_adj_v_of_ne Q v w x hleaf hxv hxw)
              (leaf_compl_adj_v_of_ne Q v w y hleaf hyv hyw)
              hxy) 1
        else 0,
      by
        intro x y
        classical
        by_cases hxv : x = v <;> by_cases hyv : y = v <;>
          by_cases hxw : x = w <;> by_cases hyw : y = w
        all_goals simp [hxv, hyv, hxw, hyw]
        · by_cases hxy : Qᶜ.Adj x y
          · have hyx : Qᶜ.Adj y x := hxy.symm
            have hdata := (Q.compl_adj x y).1 hxy
            have hydata := (Q.compl_adj y x).1 hyx
            rw [dif_pos hdata, dif_pos hydata]
            apply congrArg (fun t : FlagTriangle Qᶜ ↦ Finsupp.single t 1)
            apply Subtype.ext
            simp [coneTriangle, Finset.ext_iff, or_comm, or_left_comm, or_assoc]
          · have hyx : ¬Qᶜ.Adj y x := fun h ↦ hxy h.symm
            have hdata : ¬(x ≠ y ∧ ¬Q.Adj x y) := by
              simpa only [Q.compl_adj] using hxy
            have hydata : ¬(y ≠ x ∧ ¬Q.Adj y x) := by
              simpa only [Q.compl_adj] using hyx
            rw [dif_neg hdata, dif_neg hydata]⟩ e.1

private noncomputable def leafConeC0
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ y, Q.Adj v y ↔ y = w) :
    FlagChain0 (V := V) →ₗ[F₂] FlagChain1 Qᶜ :=
  Finsupp.linearCombination F₂ (leafConeEdgeChain Q v w hleaf)

private noncomputable def leafConeC1
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ y, Q.Adj v y ↔ y = w) :
    FlagChain1 Qᶜ →ₗ[F₂] FlagChain2 Qᶜ :=
  Finsupp.linearCombination F₂ (leafConeTriangleChain Q v w hleaf)

private lemma leafArmLift_single
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ y, Q.Adj v y ↔ y = w)
    (x : LeafU Q w) (r : F₂) :
    leafArmLift Q v w hleaf (Finsupp.single x r) =
      Finsupp.single (leafVEdge Q v w hleaf x) r +
        Finsupp.single (leafWEdge Q w x) r := by
  simp [leafArmLift]

private lemma leaf_homotopy_on_edge
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (e : FlagEdge Qᶜ) :
    flagD2 Qᶜ
          (leafConeC1 Q v w hleaf (Finsupp.single e 1)) +
        leafConeC0 Q v w hleaf
          (flagD1 Qᶜ (Finsupp.single e 1)) +
        leafArmLift Q v w hleaf
          (leafArmProjection Q w (Finsupp.single e 1)) =
      Finsupp.single e 1 := by
  classical
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      have hxy : Qᶜ.Adj x y := Qᶜ.mem_edgeSet.mp he
      have heq :
          (⟨s(x, y), he⟩ : FlagEdge Qᶜ) = flagEdgeOfAdj Qᶜ hxy :=
        Subtype.ext rfl
      by_cases hxv : x = v
      · subst x
        have hyw : y ≠ w := by
          intro hyw
          subst y
          exact ((Q.compl_adj v w).1 hxy).2
            (leaf_q_adj_vw Q v w hleaf)
        have hyv : y ≠ v := hxy.ne.symm
        have hvw := leaf_v_ne_w Q v w hleaf
        rw [heq,
          leafArmProjection_single_away Q w v y hxy hvw hyw]
        have hcone : leafConeC1 Q v w hleaf
            (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1) = 0 := by
          simp [leafConeC1, leafConeTriangleChain, flagEdgeOfAdj]
        rw [hcone, map_zero, flagD1_single_flagEdgeOfAdj]
        simp [leafConeC0, leafConeEdgeChain, hyv, hyw,
          flagEdgeOfAdj]
      · by_cases hyv : y = v
        · subst y
          have hxw : x ≠ w := by
            intro hxw
            subst x
            exact ((Q.compl_adj w v).1 hxy).2
              (leaf_q_adj_vw Q v w hleaf).symm
          have hvw := leaf_v_ne_w Q v w hleaf
          rw [heq,
            leafArmProjection_single_away Q w x v hxy hxw hvw]
          have hcone : leafConeC1 Q v w hleaf
              (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1) = 0 := by
            simp [leafConeC1, leafConeTriangleChain, flagEdgeOfAdj]
          rw [hcone, map_zero, flagD1_single_flagEdgeOfAdj]
          simp [leafConeC0, leafConeEdgeChain, hxv, hxw,
            flagEdgeOfAdj, Sym2.eq_swap]
        · by_cases hxw : x = w
          · subst x
            have hyw : y ≠ w := hxy.ne.symm
            let yu : LeafU Q w := leafUOfWAdj Q w y hxy
            have hproj := leafArmProjection_single_w_adj Q w y hxy (1 : F₂)
            have hW : flagEdgeOfAdj Qᶜ hxy = leafWEdge Q w yu :=
              Subtype.ext rfl
            have hV : flagEdgeOfAdj Qᶜ
                (leaf_compl_adj_v_of_ne Q v w y hleaf hyv hyw) =
                leafVEdge Q v w hleaf yu := Subtype.ext rfl
            rw [heq, hproj, leafArmLift_single]
            have hcone : leafConeC1 Q v w hleaf
                (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1) = 0 := by
              simp [leafConeC1, leafConeTriangleChain, flagEdgeOfAdj, hxv, hyv,
                leaf_v_ne_w Q v w hleaf]
            rw [hcone, map_zero, flagD1_single_flagEdgeOfAdj]
            simp [leafConeC0, leafConeEdgeChain, hyv, hyw, hV, hW, yu]
            let ev : FlagChain1 Qᶜ :=
              Finsupp.single (leafVEdge Q v w hleaf yu) 1
            let ew : FlagChain1 Qᶜ :=
              Finsupp.single (leafWEdge Q w yu) 1
            change ev + (ev + ew) = ew
            calc
              ev + (ev + ew) = (ev + ev) + ew := by abel
              _ = ew := by rw [f2_add_self ev]; simp
          · by_cases hyw : y = w
            · subst y
              let xu : LeafU Q w := leafUOfWAdj Q w x hxy.symm
              have hproj := leafArmProjection_single_adj_w Q w x hxy (1 : F₂)
              have hW : flagEdgeOfAdj Qᶜ hxy = leafWEdge Q w xu := by
                apply Subtype.ext
                exact Sym2.eq_swap
              have hV : flagEdgeOfAdj Qᶜ
                  (leaf_compl_adj_v_of_ne Q v w x hleaf hxv hxw) =
                  leafVEdge Q v w hleaf xu := Subtype.ext rfl
              rw [heq, hproj, leafArmLift_single]
              have hcone : leafConeC1 Q v w hleaf
                  (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1) = 0 := by
                simp [leafConeC1, leafConeTriangleChain, flagEdgeOfAdj, hxv,
                  leaf_v_ne_w Q v w hleaf]
              rw [hcone, map_zero, flagD1_single_flagEdgeOfAdj]
              simp [leafConeC0, leafConeEdgeChain, hxv, hxw, hV, hW, xu]
              let ev : FlagChain1 Qᶜ :=
                Finsupp.single (leafVEdge Q v w hleaf xu) 1
              let ew : FlagChain1 Qᶜ :=
                Finsupp.single (leafWEdge Q w xu) 1
              change ev + (ev + ew) = ew
              calc
                ev + (ev + ew) = (ev + ev) + ew := by abel
                _ = ew := by rw [f2_add_self ev]; simp
            · have hvx := leaf_compl_adj_v_of_ne Q v w x hleaf hxv hxw
              have hvy := leaf_compl_adj_v_of_ne Q v w y hleaf hyv hyw
              rw [heq,
                leafArmProjection_single_away Q w x y hxy hxw hyw]
              rw [show leafConeC1 Q v w hleaf
                    (Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1) =
                  Finsupp.single
                    (coneTriangle Qᶜ v x y hvx hvy hxy) 1 by
                have hdata := (Q.compl_adj x y).1 hxy
                simp [leafConeC1, leafConeTriangleChain, flagEdgeOfAdj,
                  hxv, hyv, hxw, hyw, hdata]]
              rw [show flagD2 Qᶜ
                    (Finsupp.single
                      (coneTriangle Qᶜ v x y hvx hvy hxy) 1) =
                  triangleBoundary Qᶜ
                    (coneTriangle Qᶜ v x y hvx hvy hxy) by
                simp [flagD2]]
              rw [triangleBoundary_coneTriangle Qᶜ v x y hvx hvy hxy,
                flagD1_single_flagEdgeOfAdj]
              simp [leafConeC0, leafConeEdgeChain, hxv, hyv, hxw, hyw,
                flagEdgeOfAdj]
              let ex : FlagChain1 Qᶜ :=
                Finsupp.single (flagEdgeOfAdj Qᶜ hvx) 1
              let ey : FlagChain1 Qᶜ :=
                Finsupp.single (flagEdgeOfAdj Qᶜ hvy) 1
              let ez : FlagChain1 Qᶜ :=
                Finsupp.single (flagEdgeOfAdj Qᶜ hxy) 1
              change ((ex + ey) + ez) + (ex + ey) = ez
              calc
                ((ex + ey) + ez) + (ex + ey) =
                    (ex + ex) + (ey + ey) + ez := by abel
                _ = ez := by rw [f2_add_self ex, f2_add_self ey]; simp

private lemma leaf_homotopy
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (z : FlagChain1 Qᶜ) :
    flagD2 Qᶜ (leafConeC1 Q v w hleaf z) +
        leafConeC0 Q v w hleaf (flagD1 Qᶜ z) +
        leafArmLift Q v w hleaf (leafArmProjection Q w z) = z := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
      simp only [map_add]
      calc
        _ = (flagD2 Qᶜ (leafConeC1 Q v w hleaf a) +
              leafConeC0 Q v w hleaf (flagD1 Qᶜ a) +
              leafArmLift Q v w hleaf (leafArmProjection Q w a)) +
            (flagD2 Qᶜ (leafConeC1 Q v w hleaf b) +
              leafConeC0 Q v w hleaf (flagD1 Qᶜ b) +
              leafArmLift Q v w hleaf (leafArmProjection Q w b)) := by abel
        _ = a + b := by rw [ha, hb]
  | single e r =>
      have hb := leaf_homotopy_on_edge Q v w hleaf e
      rw [← Finsupp.smul_single_one]
      simp only [map_smul]
      simpa only [smul_add] using
        congrArg (fun c : FlagChain1 Qᶜ ↦ r • c) hb

private lemma leaf_homotopy_on_cycle
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (z : FlagCycle Qᶜ) :
    flagD2 Qᶜ (leafConeC1 Q v w hleaf z.1) +
        leafArmLift Q v w hleaf (leafArmProjection Q w z.1) = z.1 := by
  have hhom := leaf_homotopy Q v w hleaf z.1
  rw [z.2, map_zero, add_zero] at hhom
  exact hhom

private lemma leaf_compl_adj_of_component_adj
    (Q : SimpleGraph V) (w : V) (x y : LeafU Q w)
    (hxy : (LeafComponentGraph Q w).Adj x y) :
    Qᶜ.Adj x.1 y.1 := by
  have hdata := ((LeafRemainder Q w).compl_adj x y).1 hxy
  apply (Q.compl_adj x.1 y.1).2
  refine ⟨?_, ?_⟩
  · intro h
    exact hdata.1 (Subtype.ext h)
  · simpa [LeafRemainder] using hdata.2

private noncomputable def leafRelationTriangleChain
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (e : FlagEdge (LeafComponentGraph Q w)) : FlagChain2 Qᶜ := by
  classical
  exact Sym2.lift
    ⟨fun x y ↦
        if hxy : (LeafComponentGraph Q w).Adj x y then
          Finsupp.single
              (coneTriangle Qᶜ v x.1 y.1
                (leaf_compl_adj_vu Q v w hleaf x)
                (leaf_compl_adj_vu Q v w hleaf y)
                (leaf_compl_adj_of_component_adj Q w x y hxy)) 1 +
            Finsupp.single
              (coneTriangle Qᶜ w x.1 y.1
                (leaf_compl_adj_wu Q w x)
                (leaf_compl_adj_wu Q w y)
                (leaf_compl_adj_of_component_adj Q w x y hxy)) 1
        else 0,
      by
        intro x y
        classical
        dsimp only
        by_cases hxy : (LeafComponentGraph Q w).Adj x y
        · have hyx := hxy.symm
          rw [dif_pos hxy, dif_pos hyx]
          congr 1 <;>
            apply congrArg (fun t : FlagTriangle Qᶜ ↦ Finsupp.single t 1) <;>
            apply Subtype.ext <;>
            simp [coneTriangle, Finset.ext_iff, or_comm, or_left_comm, or_assoc]
        · have hyx : ¬(LeafComponentGraph Q w).Adj y x := fun h ↦ hxy h.symm
          rw [dif_neg hxy, dif_neg hyx]⟩ e.1

private lemma leafRelationTriangleChain_flagEdge
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (x y : LeafU Q w)
    (hxy : (LeafComponentGraph Q w).Adj x y) :
    leafRelationTriangleChain Q v w hleaf
        (flagEdgeOfAdj (LeafComponentGraph Q w) hxy) =
      Finsupp.single
          (coneTriangle Qᶜ v x.1 y.1
            (leaf_compl_adj_vu Q v w hleaf x)
            (leaf_compl_adj_vu Q v w hleaf y)
            (leaf_compl_adj_of_component_adj Q w x y hxy)) 1 +
        Finsupp.single
          (coneTriangle Qᶜ w x.1 y.1
            (leaf_compl_adj_wu Q w x)
            (leaf_compl_adj_wu Q w y)
            (leaf_compl_adj_of_component_adj Q w x y hxy)) 1 := by
  classical
  rw [leafRelationTriangleChain]
  change (if h : (LeafComponentGraph Q w).Adj x y then
      Finsupp.single
          (coneTriangle Qᶜ v x.1 y.1
            (leaf_compl_adj_vu Q v w hleaf x)
            (leaf_compl_adj_vu Q v w hleaf y)
            (leaf_compl_adj_of_component_adj Q w x y h)) 1 +
        Finsupp.single
          (coneTriangle Qᶜ w x.1 y.1
            (leaf_compl_adj_wu Q w x)
            (leaf_compl_adj_wu Q w y)
            (leaf_compl_adj_of_component_adj Q w x y h)) 1
    else 0) = _
  rw [dif_pos hxy]

private noncomputable def leafRelationC1
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w) :
    FlagChain1 (LeafComponentGraph Q w) →ₗ[F₂] FlagChain2 Qᶜ :=
  Finsupp.linearCombination F₂ (leafRelationTriangleChain Q v w hleaf)

private lemma flagD2_leafRelationC1
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w)
    (k : FlagChain1 (LeafComponentGraph Q w)) :
    flagD2 Qᶜ (leafRelationC1 Q v w hleaf k) =
      leafArmLift Q v w hleaf
        (flagD1 (LeafComponentGraph Q w) k) := by
  classical
  induction k using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single e r =>
      rcases e with ⟨e, he⟩
      induction e using Sym2.ind with
      | _ x y =>
          have hxy : (LeafComponentGraph Q w).Adj x y :=
            (LeafComponentGraph Q w).mem_edgeSet.mp he
          have hF := leaf_compl_adj_of_component_adj Q w x y hxy
          have hvx := leaf_compl_adj_vu Q v w hleaf x
          have hvy := leaf_compl_adj_vu Q v w hleaf y
          have hwx := leaf_compl_adj_wu Q w x
          have hwy := leaf_compl_adj_wu Q w y
          have heq :
              (⟨s(x, y), he⟩ : FlagEdge (LeafComponentGraph Q w)) =
                flagEdgeOfAdj (LeafComponentGraph Q w) hxy := Subtype.ext rfl
          rw [← Finsupp.smul_single_one]
          simp only [map_smul]
          apply congrArg (fun c : FlagChain1 Qᶜ ↦ r • c)
          rw [heq, flagD1_single_flagEdgeOfAdj]
          rw [show leafRelationC1 Q v w hleaf
                (Finsupp.single
                  (flagEdgeOfAdj (LeafComponentGraph Q w) hxy) 1) =
              Finsupp.single (coneTriangle Qᶜ v x.1 y.1 hvx hvy hF) 1 +
                Finsupp.single (coneTriangle Qᶜ w x.1 y.1 hwx hwy hF) 1 by
            rw [leafRelationC1, Finsupp.linearCombination_single]
            simpa using
              leafRelationTriangleChain_flagEdge Q v w hleaf x y hxy]
          rw [map_add]
          rw [show flagD2 Qᶜ
                (Finsupp.single (coneTriangle Qᶜ v x.1 y.1 hvx hvy hF) 1) =
              triangleBoundary Qᶜ
                (coneTriangle Qᶜ v x.1 y.1 hvx hvy hF) by simp [flagD2]]
          rw [show flagD2 Qᶜ
                (Finsupp.single (coneTriangle Qᶜ w x.1 y.1 hwx hwy hF) 1) =
              triangleBoundary Qᶜ
                (coneTriangle Qᶜ w x.1 y.1 hwx hwy hF) by simp [flagD2]]
          rw [triangleBoundary_coneTriangle Qᶜ v x.1 y.1 hvx hvy hF,
            triangleBoundary_coneTriangle Qᶜ w x.1 y.1 hwx hwy hF]
          rw [show leafArmLift Q v w hleaf
                (Finsupp.single x 1 + Finsupp.single y 1) =
              (Finsupp.single (leafVEdge Q v w hleaf x) 1 +
                  Finsupp.single (leafWEdge Q w x) 1) +
                (Finsupp.single (leafVEdge Q v w hleaf y) 1 +
                  Finsupp.single (leafWEdge Q w y) 1) by
            simp [leafArmLift_single]]
          have hvxeq : flagEdgeOfAdj Qᶜ hvx = leafVEdge Q v w hleaf x :=
            Subtype.ext rfl
          have hvyeq : flagEdgeOfAdj Qᶜ hvy = leafVEdge Q v w hleaf y :=
            Subtype.ext rfl
          have hwxeq : flagEdgeOfAdj Qᶜ hwx = leafWEdge Q w x :=
            Subtype.ext rfl
          have hwyeq : flagEdgeOfAdj Qᶜ hwy = leafWEdge Q w y :=
            Subtype.ext rfl
          rw [hvxeq, hvyeq, hwxeq, hwyeq]
          let exy : FlagChain1 Qᶜ :=
            Finsupp.single (flagEdgeOfAdj Qᶜ hF) 1
          have hxx := f2_add_self exy
          calc
            ((Finsupp.single (leafVEdge Q v w hleaf x) 1 +
                  Finsupp.single (leafVEdge Q v w hleaf y) 1) + exy) +
                ((Finsupp.single (leafWEdge Q w x) 1 +
                  Finsupp.single (leafWEdge Q w y) 1) + exy) =
              (Finsupp.single (leafVEdge Q v w hleaf x) 1 +
                  Finsupp.single (leafWEdge Q w x) 1) +
                (Finsupp.single (leafVEdge Q v w hleaf y) 1 +
                  Finsupp.single (leafWEdge Q w y) 1) + (exy + exy) := by abel
            _ = (Finsupp.single (leafVEdge Q v w hleaf x) 1 +
                  Finsupp.single (leafWEdge Q w x) 1) +
                (Finsupp.single (leafVEdge Q v w hleaf y) 1 +
                  Finsupp.single (leafWEdge Q w y) 1) := by rw [hxx]; simp

private lemma vertexComponentMap_componentRootMap
    (Q : SimpleGraph V) (w : V)
    (K : SimpleGraph (LeafU Q w))
    (c : K.ConnectedComponent →₀ F₂) :
    vertexComponentMap K (componentRootMap K c) = c := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single C r =>
      simp [componentRootMap, vertexComponentMap,
        connectedComponentMk_componentRoot]

private lemma vertexAugmentation_componentRootMap
    (Q : SimpleGraph V) (w : V)
    (K : SimpleGraph (LeafU Q w))
    (c : K.ConnectedComponent →₀ F₂) :
    vertexAugmentation (componentRootMap K c) = componentAugmentation K c := by
  have hcomp := LinearMap.congr_fun
    (componentAugmentation_vertexComponentMap K) (componentRootMap K c)
  change componentAugmentation K
      (vertexComponentMap K (componentRootMap K c)) =
    vertexAugmentation (componentRootMap K c) at hcomp
  rw [vertexComponentMap_componentRootMap Q w K c] at hcomp
  exact hcomp.symm

private theorem leafCycleCode_surjective
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w) :
    Function.Surjective (leafCycleCode Q v w hleaf) := by
  intro c
  let K := LeafComponentGraph Q w
  let a : FlagChain0 (V := LeafU Q w) := componentRootMap K c.1
  have haug : vertexAugmentation a = 0 := by
    rw [show vertexAugmentation a = componentAugmentation K c.1 by
      exact vertexAugmentation_componentRootMap Q w K c.1]
    exact c.2
  let z : FlagCycle Qᶜ :=
    ⟨leafArmLift Q v w hleaf a,
      leafArmLift_cycle_of_reduced Q v w hleaf a haug⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change vertexComponentMap K
      (leafArmProjection Q w (leafArmLift Q v w hleaf a)) = c.1
  rw [leafArmProjection_armLift]
  exact vertexComponentMap_componentRootMap Q w K c.1

private theorem leaf_cycleCode_ker_eq_boundaries
    (Q : SimpleGraph V) (v w : V)
    (hleaf : ∀ z, Q.Adj v z ↔ z = w) :
    LinearMap.ker (leafCycleCode Q v w hleaf) =
      FlagBoundarySubmodule Qᶜ := by
  letI : Fintype (LeafU Q w) := Fintype.ofFinite _
  apply le_antisymm
  · intro z hz
    have hzval := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    change vertexComponentMap (LeafComponentGraph Q w)
        (leafArmProjection Q w z.1) = 0 at hzval
    have ha : leafArmProjection Q w z.1 ∈
        LinearMap.ker (vertexComponentMap (LeafComponentGraph Q w)) := hzval
    rw [ker_vertexComponentMap_eq_range_flagD1] at ha
    obtain ⟨k, hk⟩ := ha
    refine ⟨leafConeC1 Q v w hleaf z.1 +
      leafRelationC1 Q v w hleaf k, ?_⟩
    apply Subtype.ext
    change flagD2 Qᶜ
        (leafConeC1 Q v w hleaf z.1 +
          leafRelationC1 Q v w hleaf k) = z.1
    rw [map_add, flagD2_leafRelationC1, hk]
    exact leaf_homotopy_on_cycle Q v w hleaf z
  · exact leaf_boundaries_le_cycleCode_ker Q v w hleaf

theorem flag_h1_leaf_injects_into_components
    (Q : SimpleGraph V) [DecidableEq V] [DecidableRel Q.Adj]
    (v w : V)
    (hleaf : ∀ x, Q.Adj v x ↔ x = w) :
    let U : Set V := {x | x ≠ w ∧ ¬Q.Adj w x}
    let J : SimpleGraph U := Q.induce U
    Nonempty (FlagH1F2 Qᶜ ≃ₗ[F₂] ReducedComponentCode (Jᶜ)) := by
  classical
  dsimp only
  let f := leafCycleCode Q v w hleaf
  have hsurj : Function.Surjective f :=
    leafCycleCode_surjective Q v w hleaf
  have hker : LinearMap.ker f = FlagBoundarySubmodule Qᶜ :=
    leaf_cycleCode_ker_eq_boundaries Q v w hleaf
  let e₀ : FlagH1F2 Qᶜ ≃ₗ[F₂] (FlagCycle Qᶜ ⧸ LinearMap.ker f) :=
    Submodule.Quotient.equiv
      (FlagBoundarySubmodule Qᶜ) (LinearMap.ker f)
      (LinearEquiv.refl F₂ (FlagCycle Qᶜ)) (by simpa [hker])
  exact ⟨e₀.trans (f.quotKerEquivOfSurjective hsurj)⟩

/-- The paper family's leaf `5` has hub `4`; its remainder is the complete
graph on `0,1,2`, so the component code in the leaf theorem has dimension two.
This is the actual-chain bridge from the all-order family to its five-vertex
core. -/
theorem family_flag_h1_chain_equiv {n : ℕ} (hn : 7 ≤ n) :
    Nonempty (FlagH1F2 (FamilyG n) ≃ₗ[F₂] FlagH1F2 (FamilyCore n)) := by
  classical
  let leaf : Fin n := ⟨5, by omega⟩
  let hub : Fin n := ⟨4, by omega⟩
  let U : Set (Fin n) :=
    {x | x ≠ hub ∧ ¬(FamilyH n).Adj hub x}
  let J : SimpleGraph U := (FamilyH n).induce U
  let K : SimpleGraph U := Jᶜ
  have hcert := ExtremalFlagBetti.family_leaf_triangle_certificate hn
  dsimp only at hcert
  rcases hcert with ⟨hleaf, hU, htri⟩
  have hleaf' : ∀ x, (FamilyH n).Adj leaf x ↔ x = hub := by
    simpa [leaf, hub] using hleaf
  have hU' : ∀ x, x ∈ U ↔ x.val < 3 := by
    intro x
    exact hU x
  have hJtop : J = ⊤ := by
    ext x y
    simp only [J, SimpleGraph.induce_adj, top_adj]
    constructor
    · exact fun h hxy ↦ h.ne (congrArg Subtype.val hxy)
    · intro hxy
      exact htri x.1 y.1 ((hU' x.1).1 x.2) ((hU' y.1).1 y.2)
        (fun h ↦ hxy (Subtype.ext h))
  have hKbot : K = ⊥ := by
    simp [K, hJtop]
  let eU : Fin 3 ≃ U :=
    { toFun := fun i ↦
        ⟨⟨i.1, by omega⟩, (hU' ⟨i.1, by omega⟩).2 i.2⟩
      invFun := fun x ↦ ⟨x.1.1, (hU' x.1).1 x.2⟩
      left_inv := fun i ↦ Fin.ext rfl
      right_inv := fun x ↦ Subtype.ext (Fin.ext rfl) }
  let eComp : U ≃ K.ConnectedComponent :=
    Equiv.ofBijective K.connectedComponentMk ⟨by
      intro x y hxy
      rw [ConnectedComponent.eq, hKbot, reachable_bot] at hxy
      exact hxy, Quot.mk_surjective⟩
  letI : Fintype U := Fintype.ofFinite U
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite K.ConnectedComponent
  have hUcard : Fintype.card U = 3 := by
    simpa using (Fintype.card_congr eU).symm
  have hCcard : Fintype.card K.ConnectedComponent = 3 := by
    calc
      Fintype.card K.ConnectedComponent = Fintype.card U :=
        (Fintype.card_congr eComp).symm
      _ = 3 := hUcard
  have hcode : Module.finrank F₂ (ReducedComponentCode K) = 2 := by
    rw [finrank_reducedComponentCode, hCcard]
  rcases flag_h1_leaf_injects_into_components
      (FamilyH n) leaf hub hleaf' with ⟨eLeaf⟩
  have eLeaf' :
      FlagH1F2 (FamilyG n) ≃ₗ[F₂] ReducedComponentCode K := by
    simpa [FamilyG, U, J, K] using eLeaf
  have hfamily : Module.finrank F₂ (FlagH1F2 (FamilyG n)) = 2 :=
    eLeaf'.finrank_eq.trans hcode
  have hcore : Module.finrank F₂ (FlagH1F2 (FamilyCore n)) = 2 :=
    family_core_actual_h1_equiv hn
  exact FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    (hfamily.trans hcore.symm)

theorem family_actual_flag_h1_exactly_two {n : ℕ} (hn : 7 ≤ n) :
    FlagH1F2ExactlyTwo (FamilyG n) := by
  rcases family_flag_h1_chain_equiv hn with ⟨e⟩
  unfold FlagH1F2ExactlyTwo flagBeta1F2
  rw [LinearEquiv.finrank_eq e]
  exact family_core_actual_h1_equiv hn

theorem leaf_remainder_edges_le_vertices_add_one
    (Q : SimpleGraph V) [DecidableEq V] [DecidableRel Q.Adj]
    (w : V) (hE : #Q.edgeFinset = Fintype.card V) :
    let U : Set V := {x | x ≠ w ∧ ¬Q.Adj w x}
    let J : SimpleGraph U := Q.induce U
    J.edgeFinset.card ≤ Fintype.card U + 1 := by
  classical
  dsimp only
  let U : Set V := {x | x ≠ w ∧ ¬Q.Adj w x}
  let J : SimpleGraph U := Q.induce U
  let D : SimpleGraph V := Q.deleteIncidenceSet w
  change #J.edgeFinset ≤ Fintype.card U + 1
  have hwU : w ∉ U := by simp [U]
  have hDJ : D.induce U = J := by
    simpa [D, J] using Q.induce_deleteIncidenceSet_of_notMem hwU
  have hmapSubset :
      J.edgeFinset.map (Function.Embedding.subtype (fun x ↦ x ∈ U)).sym2Map ⊆
        D.edgeFinset := by
    intro e he
    rw [mem_map] at he
    obtain ⟨eU, heU, rfl⟩ := he
    induction eU using Sym2.ind with
    | h a b =>
        rw [mem_edgeFinset] at heU ⊢
        have hInd : (D.induce U).Adj a b := by
          rw [hDJ]
          exact heU
        exact hInd
  have hJleD : #J.edgeFinset ≤ #D.edgeFinset := by
    rw [← card_map (Function.Embedding.subtype (fun x ↦ x ∈ U)).sym2Map]
    exact card_le_card hmapSubset
  have hDcard : #D.edgeFinset = Fintype.card V - Q.degree w := by
    simpa [D, hE] using Q.card_edgeFinset_deleteIncidenceSet w
  have hUfin : U.toFinset = univ \ insert w (Q.neighborFinset w) := by
    ext x
    simp [U]
  have hUcard :
      Fintype.card U = Fintype.card V - (Q.degree w + 1) := by
    rw [← Set.toFinset_card, hUfin,
      card_sdiff_of_subset (subset_univ _)]
    rw [card_insert_of_notMem (Q.notMem_neighborFinset_self w),
      card_neighborFinset_eq_degree]
    rw [card_univ]
  rw [hDcard] at hJleD
  rw [hUcard]
  have hwdeg := Q.degree_lt_card_verts w
  omega

theorem complement_components_le_three_of_edges_le_vertices_add_one
    (J : SimpleGraph V) [DecidableRel J.Adj]
    [Fintype (Jᶜ).ConnectedComponent]
    (hE : #J.edgeFinset ≤ Fintype.card V + 1) :
    Fintype.card (Jᶜ).ConnectedComponent ≤ 3 := by
  classical
  by_contra hfour
  have hc4 : 4 ≤ Fintype.card (Jᶜ).ConnectedComponent := by omega
  have hc_le_v :
      Fintype.card (Jᶜ).ConnectedComponent ≤ Fintype.card V :=
    Fintype.card_le_of_surjective ((Jᶜ).connectedComponentMk)
      Quot.mk_surjective
  have hdegree : ∀ v : V, 3 ≤ J.degree v := by
    intro v
    let c₀ : (Jᶜ).ConnectedComponent := (Jᶜ).connectedComponentMk v
    let emb : {C : (Jᶜ).ConnectedComponent // C ≠ c₀} ↪ J.neighborFinset v :=
      { toFun := fun C ↦ ⟨C.1.out, by
          rw [mem_neighborFinset]
          have hout : (Jᶜ).connectedComponentMk C.1.out = C.1 :=
            Quot.out_eq C.1
          have hne : v ≠ C.1.out := by
            intro heq
            apply C.2
            change C.1 = (Jᶜ).connectedComponentMk v
            rw [← hout, ← heq]
          have hnadj : ¬(Jᶜ).Adj v C.1.out := by
            intro hadj
            apply C.2
            change C.1 = (Jᶜ).connectedComponentMk v
            rw [← hout]
            exact
              (ConnectedComponent.connectedComponentMk_eq_of_adj hadj).symm
          simpa using (((Jᶜ).compl_adj v C.1.out).2 ⟨hne, hnadj⟩) ⟩
        inj' := by
          intro C D h
          apply Subtype.ext
          have hout : C.1.out = D.1.out := congrArg Subtype.val h
          rw [← Quot.out_eq C.1, ← Quot.out_eq D.1, hout] }
    have hcardEmb := Fintype.card_le_of_injective emb emb.injective
    have hdomain :
        Fintype.card {C : (Jᶜ).ConnectedComponent // C ≠ c₀} =
          Fintype.card (Jᶜ).ConnectedComponent - 1 := by
      simp
    rw [hdomain] at hcardEmb
    have hthree : 3 ≤ Fintype.card (J.neighborFinset v) := by omega
    simpa only [Fintype.card_coe, card_neighborFinset_eq_degree] using hthree
  have hsumLower :
      3 * Fintype.card V ≤ ∑ v : V, J.degree v := by
    calc
      3 * Fintype.card V = ∑ _v : V, 3 := by simp [mul_comm]
      _ ≤ ∑ v : V, J.degree v :=
        Finset.sum_le_sum fun v _ ↦ hdegree v
  rw [J.sum_degrees_eq_twice_card_edges] at hsumLower
  omega

theorem reducedComponentCode_atMostTwo
    (J : SimpleGraph V) [Fintype J.ConnectedComponent]
    [DecidableRel J.Adj]
    (hc : Fintype.card J.ConnectedComponent ≤ 3) :
    Module.finrank F₂ (ReducedComponentCode J) ≤ 2 := by
  rw [finrank_reducedComponentCode]
  omega

theorem two_regular_complement_connected_of_five_le
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hcard : 5 ≤ Fintype.card V)
    (hdeg : ∀ v, Q.degree v = 2) :
    Qᶜ.Connected := by
  classical
  letI : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  refine ⟨?_⟩
  intro u v
  by_cases huvEq : u = v
  · subst v
    exact .rfl
  by_cases huv : Q.Adj u v
  · let s := Q.neighborFinset u ∪ Q.neighborFinset v
    have hsCard : #s ≤ 4 := by
      calc
        #s ≤ #(Q.neighborFinset u) + #(Q.neighborFinset v) := card_union_le _ _
        _ = 4 := by
          rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree,
            hdeg u, hdeg v]
    have hslt : #s < #(univ : Finset V) := by
      simp only [card_univ]
      omega
    obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hslt
    have hwu : w ≠ u := by
      intro h
      subst w
      apply hw
      simp only [s, mem_union, mem_neighborFinset]
      exact Or.inr huv.symm
    have hwv : w ≠ v := by
      intro h
      subst w
      apply hw
      simp only [s, mem_union, mem_neighborFinset]
      exact Or.inl huv
    have hQuw : ¬Q.Adj u w := by
      intro h
      apply hw
      simp only [s, mem_union, mem_neighborFinset]
      exact Or.inl h
    have hQwv : ¬Q.Adj w v := by
      intro h
      apply hw
      simp only [s, mem_union, mem_neighborFinset]
      exact Or.inr h.symm
    exact ((Q.compl_adj u w).2 ⟨hwu.symm, hQuw⟩).reachable.trans
      ((Q.compl_adj w v).2 ⟨hwv, hQwv⟩).reachable
  · exact ((Q.compl_adj u v).2 ⟨huvEq, huv⟩).reachable

section BoundaryColumns

variable {V P : Type*} [Fintype V] [Fintype P] [DecidableEq P]

noncomputable def boundaryColumnMap (G : SimpleGraph V)
    (column : P → FlagChain2 G) :
    (P →₀ F₂) →ₗ[F₂] FlagChain2 G :=
  Finsupp.linearCombination F₂ column

private lemma boundaryColumnMap_eval
    (G : SimpleGraph V) (column : P → FlagChain2 G)
    (pivot : P → FlagEdge G)
    (hdelta : ∀ i j,
      flagD2 G (column j) (pivot i) = if j = i then 1 else 0)
    (c : P →₀ F₂) (i : P) :
    flagD2 G (boundaryColumnMap G column c) (pivot i) = c i := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add, Finsupp.add_apply, hc, hd]
  | single j a =>
      rw [boundaryColumnMap, Finsupp.linearCombination_single, map_smul,
        Finsupp.smul_apply, hdelta]
      by_cases hji : j = i
      · subst j
        simp
      · simp [hji]

private theorem boundaryColumnMap_injective
    (G : SimpleGraph V) (column : P → FlagChain2 G)
    (pivot : P → FlagEdge G)
    (hdelta : ∀ i j,
      flagD2 G (column j) (pivot i) = if j = i then 1 else 0) :
    Function.Injective
      ((flagD2Cycle G).comp (boundaryColumnMap G column)) := by
  intro c d hcd
  ext i
  have hval := congrArg
    (fun z : FlagCycle G ↦ z.1 (pivot i)) hcd
  change flagD2 G (boundaryColumnMap G column c) (pivot i) =
    flagD2 G (boundaryColumnMap G column d) (pivot i) at hval
  simpa [boundaryColumnMap_eval G column pivot hdelta] using hval

/-- If explicit triangular 2-chains have an identity minor whose size is the
connected graph's cycle rank, every 1-cycle is a triangle boundary. -/
theorem flagBeta1_eq_zero_of_boundary_columns
    (G : SimpleGraph V) (hG : G.Connected)
    (column : P → FlagChain2 G) (pivot : P → FlagEdge G)
    (hdelta : ∀ i j,
      flagD2 G (column j) (pivot i) = if j = i then 1 else 0)
    (hcard :
      Fintype.card (FlagEdge G) - (Fintype.card V - 1) ≤
        Fintype.card P) :
    flagBeta1F2 G = 0 := by
  let L := (flagD2Cycle G).comp (boundaryColumnMap G column)
  have hL : Function.Injective L :=
    boundaryColumnMap_injective G column pivot hdelta
  have hsmall := LinearMap.finrank_range_of_inj hL
  have hcycles := finrank_flagCycles_of_connected G hG
  have hle : LinearMap.range L ≤ FlagBoundarySubmodule G := by
    rintro z ⟨c, rfl⟩
    exact ⟨boundaryColumnMap G column c, rfl⟩
  have htop : FlagBoundarySubmodule G = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    apply le_antisymm (Submodule.finrank_le _)
    calc
      Module.finrank F₂ (FlagCycle G) =
          Fintype.card (FlagEdge G) - (Fintype.card V - 1) := hcycles
      _ ≤ Fintype.card P := hcard
      _ = Module.finrank F₂ (LinearMap.range L) := by
        simpa [Module.finrank_finsupp_self] using hsmall.symm
      _ ≤ Module.finrank F₂ (FlagBoundarySubmodule G) :=
        Submodule.finrank_mono hle
  unfold flagBeta1F2
  rw [Submodule.finrank_quotient]
  rw [htop, finrank_top, Nat.sub_self]

end BoundaryColumns

section CycleComplementColumns

abbrev MiddleVertex (n : ℕ) :=
  {v : Fin n // 2 ≤ v.val ∧ v.val + 2 ≤ n}

abbrev LeftArmIndex (n : ℕ) :=
  {v : Fin n // 4 ≤ v.val ∧ v.val + 2 ≤ n}

abbrev RightArmIndex (n : ℕ) :=
  {v : Fin n // 2 ≤ v.val ∧ v.val + 4 ≤ n}

abbrev CycleComplementGraph (n : ℕ) : SimpleGraph (Fin n) :=
  (cycleGraph n)ᶜ

/-- The concrete edge-set enumeration used by the explicit cycle-complement
decomposition.  Keeping it named lets the final dimension estimate be
transported to whatever extensionally equal finite enumeration a caller uses. -/
private noncomputable def cycleFlagEdgeCanonicalFintype (n : ℕ) :
    Fintype (FlagEdge (CycleComplementGraph n)) :=
  inferInstance

/-- The canonical identity between two enumerations of the same edge subtype. -/
private def cycleFlagEdgeCanonicalEquiv (n : ℕ) :
    FlagEdge (CycleComplementGraph n) ≃
      FlagEdge (CycleComplementGraph n) :=
  Equiv.refl _

abbrev MiddleComplementGraph (n : ℕ) : SimpleGraph (MiddleVertex n) :=
  (CycleComplementGraph n).induce
    {v : Fin n | 2 ≤ v.val ∧ v.val + 2 ≤ n}

inductive CycleBoundaryColumn (n : ℕ)
  | middle : FlagEdge (MiddleComplementGraph n) → CycleBoundaryColumn n
  | left : LeftArmIndex n → CycleBoundaryColumn n
  | right : RightArmIndex n → CycleBoundaryColumn n
  | cross : CycleBoundaryColumn n
  deriving Fintype, DecidableEq

private lemma cycleComplement_adj_of_gap {n : ℕ} {u v : Fin n}
    (hgap : u.val + 2 ≤ v.val)
    (hwrap : ¬ (u.val = 0 ∧ v.val + 1 = n)) :
    (CycleComplementGraph n).Adj u v := by
  rw [SimpleGraph.compl_adj]
  refine ⟨by omega, ?_⟩
  rw [cycleGraph_adj']
  push_neg
  constructor
  · intro huv
    have hsub := Fin.intCast_val_sub_eq_sub_add_ite u v
    rw [if_neg (by omega : ¬ v ≤ u), huv] at hsub
    apply hwrap
    constructor <;> omega
  · rw [Fin.sub_val_of_le (by omega : u ≤ v)]
    omega

private lemma cycleGraph_adj_of_succ_val {n : ℕ} {u v : Fin n}
    (h : u.val + 1 = v.val) : (cycleGraph n).Adj u v :=
  pathGraph_le_cycleGraph (pathGraph_adj.mpr (Or.inl h))

private lemma cycleGraph_adj_zero_last {n : ℕ} (hn : 2 ≤ n) :
    (cycleGraph n).Adj ⟨0, by omega⟩ ⟨n - 1, by omega⟩ := by
  by_cases htwo : n = 2
  · subst n
    simpa [cycleGraph_two_eq_top]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
    rw [Nat.add_comm] at hk
    subst n
    simpa [Fin.last] using
      (show (cycleGraph (k + 3)).Adj 0 (Fin.last (k + 2)) by
        simp [cycleGraph_adj])

private def cycleRoot (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨0, by omega⟩
private def cycleLeft (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨1, by omega⟩
private def cycleLeftRoot (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨3, by omega⟩
private def cycleLeftHub (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨6, by omega⟩
private def cycleRight (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨n - 1, by omega⟩
private def cycleRightRoot (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨n - 3, by omega⟩
private def cycleRightHub (n : ℕ) (hn : 8 ≤ n) : Fin n := ⟨n - 6, by omega⟩

@[simp] private lemma cycleRoot_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleRoot n hn).val = 0 := rfl

@[simp] private lemma cycleLeft_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleLeft n hn).val = 1 := rfl

@[simp] private lemma cycleLeftRoot_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleLeftRoot n hn).val = 3 := rfl

@[simp] private lemma cycleLeftHub_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleLeftHub n hn).val = 6 := rfl

@[simp] private lemma cycleRight_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleRight n hn).val = n - 1 := rfl

@[simp] private lemma cycleRightRoot_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleRightRoot n hn).val = n - 3 := rfl

@[simp] private lemma cycleRightHub_val {n : ℕ} (hn : 8 ≤ n) :
    (cycleRightHub n hn).val = n - 6 := rfl

private noncomputable def triangleOfAdj {V : Type*} [Fintype V]
    [DecidableEq V]
    (G : SimpleGraph V) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    FlagTriangle G := by
  let hcl : G.IsNClique 3 {a, b, c} :=
    SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩
  exact ⟨{a, b, c}, hcl.card_eq, hcl.isClique⟩

@[simp] private lemma flagD2_single_triangleOfAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (a b c : V)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) :
    flagD2 G (Finsupp.single (triangleOfAdj G a b c hab hac hbc) 1) =
      Finsupp.single (flagEdgeOfAdj G hab) 1 +
      Finsupp.single (flagEdgeOfAdj G hac) 1 +
      Finsupp.single (flagEdgeOfAdj G hbc) 1 := by
  rw [flagD2, Finsupp.linearCombination_single, one_smul]
  exact triangleBoundary_eq_three_edges G
    (triangleOfAdj G a b c hab hac hbc) hab hac hbc (by rfl)

private lemma cycleRoot_adj_middle {n : ℕ} (hn : 8 ≤ n)
    (v : MiddleVertex n) :
    (CycleComplementGraph n).Adj (cycleRoot n hn) v.1 := by
  have hv := v.2
  apply cycleComplement_adj_of_gap
  · exact v.2.1
  · rintro ⟨-, hv⟩
    omega

private lemma cycleLeft_adj_leftArm {n : ℕ} (hn : 8 ≤ n)
    (v : LeftArmIndex n) :
    (CycleComplementGraph n).Adj (cycleLeft n hn) v.1 := by
  have hv := v.2
  apply cycleComplement_adj_of_gap
  · change 1 + 2 ≤ v.1.val
    omega
  · rintro ⟨hv, -⟩
    simpa using hv

private lemma cycleRight_adj_rightArm {n : ℕ} (hn : 8 ≤ n)
    (v : RightArmIndex n) :
    (CycleComplementGraph n).Adj (cycleRight n hn) v.1 := by
  have hv := v.2
  apply SimpleGraph.Adj.symm
  apply cycleComplement_adj_of_gap
  · change v.1.val + 2 ≤ n - 1
    omega
  · rintro ⟨hv, -⟩
    omega

private noncomputable def middleEdgeLift {n : ℕ}
    (e : FlagEdge (MiddleComplementGraph n)) :
    FlagEdge (CycleComplementGraph n) := by
  let emb : MiddleVertex n ↪ Fin n := Function.Embedding.subtype _
  refine ⟨emb.sym2Map e.1, ?_⟩
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      exact (MiddleComplementGraph n).mem_edgeSet.mp he

private noncomputable def middleRootTriangle {n : ℕ} (hn : 8 ≤ n)
    (e : FlagEdge (MiddleComplementGraph n)) :
    FlagTriangle (CycleComplementGraph n) := by
  classical
  refine ⟨insert (cycleRoot n hn) (middleEdgeLift e).1.toFinset, ?_, ?_⟩
  · rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        have huv : (MiddleComplementGraph n).Adj u v :=
          (MiddleComplementGraph n).mem_edgeSet.mp he
        have hu := u.2
        have hv := v.2
        have hru : cycleRoot n hn ≠ u.1 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega
        have hrv : cycleRoot n hn ≠ v.1 := by
          intro h
          have hval := congrArg Fin.val h
          simp at hval
          omega
        have huv' : u.1 ≠ v.1 := by
          intro h
          exact huv.ne (Subtype.ext h)
        have hlift : (middleEdgeLift ⟨s(u, v), he⟩).1 = s(u.1, v.1) := by
          rfl
        rw [hlift]
        simp only [Sym2.toFinset_mk_eq]
        simp [hru, hrv, huv']
  · rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        have huv : (CycleComplementGraph n).Adj u.1 v.1 :=
          (MiddleComplementGraph n).mem_edgeSet.mp he
        simpa [middleEdgeLift, Sym2.toFinset_mk_eq] using
          (SimpleGraph.is3Clique_triple_iff.mpr
            ⟨cycleRoot_adj_middle hn u, cycleRoot_adj_middle hn v, huv⟩).isClique

private noncomputable def cycleBoundaryPivot {n : ℕ} (hn : 8 ≤ n) :
    CycleBoundaryColumn n → FlagEdge (CycleComplementGraph n)
  | .middle e => middleEdgeLift e
  | .left v => flagEdgeOfAdj _ (cycleLeft_adj_leftArm hn v)
  | .right v => flagEdgeOfAdj _ (cycleRight_adj_rightArm hn v)
  | .cross => flagEdgeOfAdj _ (cycleComplement_adj_of_gap
      (u := cycleLeft n hn) (v := cycleRight n hn)
      (by simp; omega) (by simp))

abbrev CycleTreeIndex (n : ℕ) := MiddleVertex n ⊕ Fin 2

private noncomputable def cycleTreePivot {n : ℕ} (hn : 8 ≤ n) :
    CycleTreeIndex n → FlagEdge (CycleComplementGraph n)
  | .inl v => flagEdgeOfAdj _ (cycleRoot_adj_middle hn v)
  | .inr i =>
      if hi : i = 0 then
        flagEdgeOfAdj _ (cycleComplement_adj_of_gap
          (u := cycleLeft n hn) (v := cycleLeftRoot n hn)
          (by simp) (by simp))
      else
        flagEdgeOfAdj _ (SimpleGraph.Adj.symm (cycleComplement_adj_of_gap
          (u := cycleRightRoot n hn) (v := cycleRight n hn)
          (by
            change n - 3 + 2 ≤ n - 1
            omega)
          (by
            rintro ⟨h, -⟩
            have h' : n - 3 = 0 := by simpa using h
            omega)))

private lemma cycleTreePivot_one_eq_rightRootRight {n : ℕ} (hn : 8 ≤ n)
    (hqb : (CycleComplementGraph n).Adj
      (cycleRightRoot n hn) (cycleRight n hn)) :
    cycleTreePivot hn (.inr 1) =
      flagEdgeOfAdj (CycleComplementGraph n) hqb := by
  rw [cycleTreePivot, dif_neg (by decide : (1 : Fin 2) ≠ 0)]
  apply Subtype.ext
  exact Sym2.eq_swap

private abbrev allCycleEdgeIndex (n : ℕ) :=
  CycleBoundaryColumn n ⊕ CycleTreeIndex n

private noncomputable def allCycleEdge {n : ℕ} (hn : 8 ≤ n) :
    allCycleEdgeIndex n → FlagEdge (CycleComplementGraph n)
  | .inl i => cycleBoundaryPivot hn i
  | .inr t => cycleTreePivot hn t

private def middleVertexEquiv {n : ℕ} (hn : 3 ≤ n) :
    Fin (n - 3) ≃ MiddleVertex n where
  toFun i := ⟨⟨i.val + 2, by have hi := i.isLt; omega⟩, by
    have hi := i.isLt
    change 2 ≤ i.val + 2 ∧ i.val + 2 + 2 ≤ n
    omega⟩
  invFun v := ⟨v.1.val - 2, by
    have hv := v.2
    have hvlt := v.1.isLt
    omega⟩
  left_inv i := by
    apply Fin.ext
    simp
  right_inv v := by
    apply Subtype.ext
    apply Fin.ext
    simp
    have hv := v.2
    have hvlt := v.1.isLt
    omega

private lemma card_cycleTreeIndex {n : ℕ} (hn : 8 ≤ n) :
    Fintype.card (CycleTreeIndex n) = n - 1 := by
  rw [Fintype.card_sum, ← Fintype.card_congr (middleVertexEquiv (by omega)),
    Fintype.card_fin, Fintype.card_fin]
  omega

private lemma allCycleEdge_surjective_ordered {n : ℕ} (hn : 8 ≤ n)
    {x y : Fin n} (hxy : x.val < y.val)
    (hG : (CycleComplementGraph n).Adj x y) :
    ∃ i, allCycleEdge hn i = flagEdgeOfAdj (CycleComplementGraph n) hG := by
  have hnot : ¬(cycleGraph n).Adj x y :=
    ((cycleGraph n).compl_adj x y).mp hG |>.2
  have hsucc : x.val + 1 ≠ y.val := by
    intro h
    exact hnot (cycleGraph_adj_of_succ_val h)
  have hwrap : ¬(x.val = 0 ∧ y.val + 1 = n) := by
    rintro ⟨hx, hy⟩
    have hx' : x = ⟨0, by omega⟩ := Fin.ext hx
    have hy' : y = ⟨n - 1, by omega⟩ := Fin.ext (by
      change y.val = n - 1
      have hylt := y.isLt
      omega)
    apply hnot
    simpa only [hx', hy'] using cycleGraph_adj_zero_last (n := n) (by omega)
  by_cases hx0 : x.val = 0
  · have hx : x = cycleRoot n hn := Fin.ext (by simp [cycleRoot, hx0])
    subst x
    let v : MiddleVertex n := ⟨y, by
      change 2 ≤ y.val ∧ y.val + 2 ≤ n
      simp at hxy hsucc hwrap
      omega⟩
    refine ⟨.inr (.inl v), ?_⟩
    apply Subtype.ext
    rfl
  by_cases hx1 : x.val = 1
  · have hx : x = cycleLeft n hn := Fin.ext (by simp [cycleLeft, hx1])
    subst x
    by_cases hy3 : y.val = 3
    · have hy : y = cycleLeftRoot n hn := Fin.ext (by simp [cycleLeftRoot, hy3])
      subst y
      refine ⟨.inr (.inr 0), ?_⟩
      apply Subtype.ext
      change s(cycleLeft n hn, cycleLeftRoot n hn) =
        s(cycleLeft n hn, cycleLeftRoot n hn)
      rfl
    by_cases hylast : y.val + 1 = n
    · have hy : y = cycleRight n hn := Fin.ext (by simp [cycleRight]; omega)
      subst y
      refine ⟨.inl .cross, ?_⟩
      apply Subtype.ext
      change s(cycleLeft n hn, cycleRight n hn) =
        s(cycleLeft n hn, cycleRight n hn)
      rfl
    · let v : LeftArmIndex n := ⟨y, by simp [cycleLeft] at hxy hsucc ⊢; omega⟩
      refine ⟨.inl (.left v), ?_⟩
      apply Subtype.ext
      change s(cycleLeft n hn, v.1) = s(cycleLeft n hn, v.1)
      rfl
  · by_cases hylast : y.val + 1 = n
    · by_cases hxroot : x.val = n - 3
      · have hx : x = cycleRightRoot n hn := Fin.ext (by simp [cycleRightRoot, hxroot])
        have hy : y = cycleRight n hn := Fin.ext (by simp [cycleRight]; omega)
        subst x
        subst y
        refine ⟨.inr (.inr 1), ?_⟩
        apply Subtype.ext
        have hs : s(cycleRightRoot n hn, cycleRight n hn) =
            s(cycleRight n hn, cycleRightRoot n hn) := Sym2.eq_swap
        simpa [allCycleEdge, cycleTreePivot, flagEdgeOfAdj] using hs
      · let v : RightArmIndex n := ⟨x, by omega⟩
        have hy : y = cycleRight n hn := Fin.ext (by simp [cycleRight]; omega)
        subst y
        refine ⟨.inl (.right v), ?_⟩
        apply Subtype.ext
        change s(cycleRight n hn, v.1) = s(v.1, cycleRight n hn)
        exact Sym2.eq_swap
    · let u : MiddleVertex n := ⟨x, by omega⟩
      let v : MiddleVertex n := ⟨y, by omega⟩
      have huv : (MiddleComplementGraph n).Adj u v := hG
      let e : FlagEdge (MiddleComplementGraph n) :=
        flagEdgeOfAdj (MiddleComplementGraph n) huv
      refine ⟨.inl (.middle e), ?_⟩
      apply Subtype.ext
      change s(u.1, v.1) = s(x, y)
      rfl

private theorem allCycleEdge_surjective {n : ℕ} (hn : 8 ≤ n) :
    Function.Surjective (allCycleEdge hn) := by
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      have hG : (CycleComplementGraph n).Adj x y :=
        (CycleComplementGraph n).mem_edgeSet.mp he
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hG.ne) with hxy | hyx
      · obtain ⟨i, hi⟩ := allCycleEdge_surjective_ordered hn hxy hG
        exact ⟨i, by simpa [flagEdgeOfAdj] using hi⟩
      · obtain ⟨i, hi⟩ :=
          allCycleEdge_surjective_ordered hn hyx hG.symm
        refine ⟨i, ?_⟩
        simpa [flagEdgeOfAdj, Sym2.eq_swap] using hi

private lemma cycleBoundaryColumn_card_lower {n : ℕ} (hn : 8 ≤ n) :
    @Fintype.card (FlagEdge (CycleComplementGraph n))
        (cycleFlagEdgeCanonicalFintype n) - (n - 1) ≤
      Fintype.card (CycleBoundaryColumn n) := by
  letI : Fintype (FlagEdge (CycleComplementGraph n)) :=
    cycleFlagEdgeCanonicalFintype n
  have hcard := Fintype.card_le_of_surjective (allCycleEdge hn)
    (allCycleEdge_surjective hn)
  rw [Fintype.card_sum, card_cycleTreeIndex hn] at hcard
  omega

private lemma cycleBoundaryColumn_card_lower_for {n : ℕ} (hn : 8 ≤ n)
    (edgeFintype : Fintype (FlagEdge (CycleComplementGraph n))) :
    @Fintype.card (FlagEdge (CycleComplementGraph n)) edgeFintype - (n - 1) ≤
      Fintype.card (CycleBoundaryColumn n) := by
  have hcard := cycleBoundaryColumn_card_lower hn
  have hcanonical :
      @Fintype.card (FlagEdge (CycleComplementGraph n))
          (cycleFlagEdgeCanonicalFintype n) =
        @Fintype.card (FlagEdge (CycleComplementGraph n)) edgeFintype :=
    @Fintype.card_congr _ _ (cycleFlagEdgeCanonicalFintype n) edgeFintype
      (cycleFlagEdgeCanonicalEquiv n)
  omega

private theorem cycleComplement_connected {n : ℕ} (hn : 8 ≤ n) :
    (CycleComplementGraph n).Connected := by
  classical
  letI : Nonempty (Fin n) := ⟨cycleRoot n hn⟩
  refine ⟨?_⟩
  intro u v
  by_cases huvEq : u = v
  · subst v
    exact .rfl
  by_cases huv : (cycleGraph n).Adj u v
  · let s := (cycleGraph n).neighborFinset u ∪
        (cycleGraph n).neighborFinset v
    have hdeg : ∀ x : Fin n, (cycleGraph n).degree x = 2 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n by omega)
      rw [Nat.add_comm] at hk
      subst n
      intro x
      simpa [Nat.add_assoc] using
        (cycleGraph_degree_three_le (n := k) (v := x))
    have hsCard : #s ≤ 4 := by
      calc
        #s ≤ #((cycleGraph n).neighborFinset u) +
            #((cycleGraph n).neighborFinset v) := card_union_le _ _
        _ = 4 := by
          rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree,
            hdeg u, hdeg v]
    have hslt : #s < #(univ : Finset (Fin n)) := by
      simp only [card_univ, Fintype.card_fin]
      omega
    obtain ⟨w, -, hw⟩ := exists_mem_notMem_of_card_lt_card hslt
    have hwu : w ≠ u := by
      intro h
      subst w
      apply hw
      exact mem_union_right _ (by simpa using huv.symm)
    have hwv : w ≠ v := by
      intro h
      subst w
      apply hw
      exact mem_union_left _ (by simpa using huv)
    have hQuw : ¬(cycleGraph n).Adj u w := by
      intro h
      apply hw
      exact mem_union_left _ (by simpa using h)
    have hQwv : ¬(cycleGraph n).Adj w v := by
      intro h
      apply hw
      exact mem_union_right _ (by simpa using h.symm)
    exact (((cycleGraph n).compl_adj u w).2 ⟨hwu.symm, hQuw⟩).reachable.trans
      (((cycleGraph n).compl_adj w v).2 ⟨hwv, hQwv⟩).reachable
  · exact (((cycleGraph n).compl_adj u v).2 ⟨huvEq, huv⟩).reachable

private lemma middleEdgeLift_val {n : ℕ}
    (e : FlagEdge (MiddleComplementGraph n)) :
    (middleEdgeLift e).1 =
      (Function.Embedding.subtype
        (p := fun v : Fin n ↦ 2 ≤ v.val ∧ v.val + 2 ≤ n)).sym2Map e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v => rfl

private theorem middleEdgeLift_injective {n : ℕ} :
    Function.Injective (middleEdgeLift (n := n)) := by
  intro e f hef
  apply Subtype.ext
  apply (Function.Embedding.subtype
    (p := fun v : Fin n ↦ 2 ≤ v.val ∧ v.val + 2 ≤ n)).sym2Map.injective
  rw [← middleEdgeLift_val e, ← middleEdgeLift_val f]
  exact congrArg Subtype.val hef

private def edgeValPair {n : ℕ}
    (e : FlagEdge (CycleComplementGraph n)) : ℕ × ℕ :=
  Sym2.lift
    ⟨fun u v ↦ (min u.val v.val, max u.val v.val),
      by intro u v; simp [min_comm, max_comm]⟩ e.1

@[simp] private lemma edgeValPair_flagEdgeOfAdj {n : ℕ} {u v : Fin n}
    (h : (CycleComplementGraph n).Adj u v) :
    edgeValPair (flagEdgeOfAdj _ h) =
      (min u.val v.val, max u.val v.val) := by
  rfl

private lemma edgeValPair_middleEdgeLift {n : ℕ}
    (e : FlagEdge (MiddleComplementGraph n)) :
    edgeValPair (middleEdgeLift e) =
      Sym2.lift
        ⟨fun u v ↦ (min u.1.val v.1.val, max u.1.val v.1.val),
          by intro u v; simp [min_comm, max_comm]⟩ e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v => rfl

private lemma edgeValPair_middle_bounds {n : ℕ}
    (e : FlagEdge (MiddleComplementGraph n)) :
    2 ≤ (edgeValPair (middleEdgeLift e)).1 ∧
      (edgeValPair (middleEdgeLift e)).2 + 2 ≤ n := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      change 2 ≤ min u.1.val v.1.val ∧ max u.1.val v.1.val + 2 ≤ n
      have hu := u.2
      have hv := v.2
      omega

private lemma edgeValPair_cycleBoundaryPivot_left {n : ℕ} (hn : 8 ≤ n)
    (v : LeftArmIndex n) :
    edgeValPair (cycleBoundaryPivot hn (.left v)) = (1, v.1.val) := by
  change (min 1 v.1.val, max 1 v.1.val) = (1, v.1.val)
  have hv := v.2
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

private lemma edgeValPair_cycleBoundaryPivot_right {n : ℕ} (hn : 8 ≤ n)
    (v : RightArmIndex n) :
    edgeValPair (cycleBoundaryPivot hn (.right v)) = (v.1.val, n - 1) := by
  change (min (n - 1) v.1.val, max (n - 1) v.1.val) =
    (v.1.val, n - 1)
  have hv := v.2
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

private lemma edgeValPair_cycleBoundaryPivot_cross {n : ℕ} (hn : 8 ≤ n) :
    edgeValPair (cycleBoundaryPivot hn .cross) = (1, n - 1) := by
  change (min 1 (n - 1), max 1 (n - 1)) = (1, n - 1)
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

private lemma edgeValPair_cycleTreePivot_middle {n : ℕ} (hn : 8 ≤ n)
    (v : MiddleVertex n) :
    edgeValPair (cycleTreePivot hn (.inl v)) = (0, v.1.val) := by
  change (min 0 v.1.val, max 0 v.1.val) = (0, v.1.val)
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

private lemma edgeValPair_cycleTreePivot_zero {n : ℕ} (hn : 8 ≤ n) :
    edgeValPair (cycleTreePivot hn (.inr 0)) = (1, 3) := by
  rw [cycleTreePivot, dif_pos rfl, edgeValPair_flagEdgeOfAdj]
  norm_num

private lemma edgeValPair_cycleTreePivot_one {n : ℕ} (hn : 8 ≤ n) :
    edgeValPair (cycleTreePivot hn (.inr 1)) = (n - 3, n - 1) := by
  rw [cycleTreePivot, dif_neg (by decide : (1 : Fin 2) ≠ 0),
    edgeValPair_flagEdgeOfAdj]
  change (min (n - 1) (n - 3), max (n - 1) (n - 3)) =
    (n - 3, n - 1)
  apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

private theorem cycleBoundaryPivot_injective {n : ℕ} (hn : 8 ≤ n) :
    Function.Injective (cycleBoundaryPivot hn) := by
  intro i j hij
  rcases i with ei | vi | vi | _
  · rcases j with ej | vj | vj | _
    · apply congrArg (CycleBoundaryColumn.middle (n := n))
      apply middleEdgeLift_injective
      simpa only [cycleBoundaryPivot] using hij
    · have hp : edgeValPair (middleEdgeLift ei) = (1, vj.1.val) := by
        calc
          edgeValPair (middleEdgeLift ei) =
              edgeValPair (cycleBoundaryPivot hn (.left vj)) := by
                simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
          _ = (1, vj.1.val) := edgeValPair_cycleBoundaryPivot_left hn vj
      have hb := edgeValPair_middle_bounds ei
      have hp1 := congrArg Prod.fst hp
      omega
    · have hp : edgeValPair (middleEdgeLift ei) = (vj.1.val, n - 1) := by
        calc
          edgeValPair (middleEdgeLift ei) =
              edgeValPair (cycleBoundaryPivot hn (.right vj)) := by
                simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
          _ = (vj.1.val, n - 1) := edgeValPair_cycleBoundaryPivot_right hn vj
      have hb := edgeValPair_middle_bounds ei
      have hp2 := congrArg Prod.snd hp
      omega
    · have hp : edgeValPair (middleEdgeLift ei) = (1, n - 1) := by
        calc
          edgeValPair (middleEdgeLift ei) =
              edgeValPair (cycleBoundaryPivot hn .cross) := by
                simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
          _ = (1, n - 1) := edgeValPair_cycleBoundaryPivot_cross hn
      have hb := edgeValPair_middle_bounds ei
      have hp1 := congrArg Prod.fst hp
      omega
  · rcases j with ej | vj | vj | _
    · have hp : (1, vi.1.val) = edgeValPair (middleEdgeLift ej) := by
        calc
          (1, vi.1.val) = edgeValPair (cycleBoundaryPivot hn (.left vi)) :=
            (edgeValPair_cycleBoundaryPivot_left hn vi).symm
          _ = edgeValPair (middleEdgeLift ej) := by
            simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
      have hb := edgeValPair_middle_bounds ej
      have hp1 := congrArg Prod.fst hp
      omega
    · have hp : (1, vi.1.val) = (1, vj.1.val) := by
        calc
          (1, vi.1.val) = edgeValPair (cycleBoundaryPivot hn (.left vi)) :=
            (edgeValPair_cycleBoundaryPivot_left hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.left vj)) :=
            congrArg edgeValPair hij
          _ = (1, vj.1.val) := edgeValPair_cycleBoundaryPivot_left hn vj
      congr 1
      apply Subtype.ext
      apply Fin.ext
      exact congrArg Prod.snd hp
    · have hp : (1, vi.1.val) = (vj.1.val, n - 1) := by
        calc
          (1, vi.1.val) = edgeValPair (cycleBoundaryPivot hn (.left vi)) :=
            (edgeValPair_cycleBoundaryPivot_left hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.right vj)) :=
            congrArg edgeValPair hij
          _ = (vj.1.val, n - 1) := edgeValPair_cycleBoundaryPivot_right hn vj
      have hvi := vi.2
      have hp2 := congrArg Prod.snd hp
      omega
    · have hp : (1, vi.1.val) = (1, n - 1) := by
        calc
          (1, vi.1.val) = edgeValPair (cycleBoundaryPivot hn (.left vi)) :=
            (edgeValPair_cycleBoundaryPivot_left hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn .cross) := congrArg edgeValPair hij
          _ = (1, n - 1) := edgeValPair_cycleBoundaryPivot_cross hn
      have hvi := vi.2
      have hp2 := congrArg Prod.snd hp
      omega
  · rcases j with ej | vj | vj | _
    · have hp : (vi.1.val, n - 1) = edgeValPair (middleEdgeLift ej) := by
        calc
          (vi.1.val, n - 1) = edgeValPair (cycleBoundaryPivot hn (.right vi)) :=
            (edgeValPair_cycleBoundaryPivot_right hn vi).symm
          _ = edgeValPair (middleEdgeLift ej) := by
            simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
      have hb := edgeValPair_middle_bounds ej
      have hp2 := congrArg Prod.snd hp
      omega
    · have hp : (vi.1.val, n - 1) = (1, vj.1.val) := by
        calc
          (vi.1.val, n - 1) = edgeValPair (cycleBoundaryPivot hn (.right vi)) :=
            (edgeValPair_cycleBoundaryPivot_right hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.left vj)) := congrArg edgeValPair hij
          _ = (1, vj.1.val) := edgeValPair_cycleBoundaryPivot_left hn vj
      have hvj := vj.2
      have hp2 := congrArg Prod.snd hp
      omega
    · have hp : (vi.1.val, n - 1) = (vj.1.val, n - 1) := by
        calc
          (vi.1.val, n - 1) = edgeValPair (cycleBoundaryPivot hn (.right vi)) :=
            (edgeValPair_cycleBoundaryPivot_right hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.right vj)) := congrArg edgeValPair hij
          _ = (vj.1.val, n - 1) := edgeValPair_cycleBoundaryPivot_right hn vj
      congr 1
      apply Subtype.ext
      apply Fin.ext
      exact congrArg Prod.fst hp
    · have hp : (vi.1.val, n - 1) = (1, n - 1) := by
        calc
          (vi.1.val, n - 1) = edgeValPair (cycleBoundaryPivot hn (.right vi)) :=
            (edgeValPair_cycleBoundaryPivot_right hn vi).symm
          _ = edgeValPair (cycleBoundaryPivot hn .cross) := congrArg edgeValPair hij
          _ = (1, n - 1) := edgeValPair_cycleBoundaryPivot_cross hn
      have hvi := vi.2
      have hp1 := congrArg Prod.fst hp
      omega
  · rcases j with ej | vj | vj | _
    · have hp : (1, n - 1) = edgeValPair (middleEdgeLift ej) := by
        calc
          (1, n - 1) = edgeValPair (cycleBoundaryPivot hn .cross) :=
            (edgeValPair_cycleBoundaryPivot_cross hn).symm
          _ = edgeValPair (middleEdgeLift ej) := by
            simpa only [cycleBoundaryPivot] using congrArg edgeValPair hij
      have hb := edgeValPair_middle_bounds ej
      have hp1 := congrArg Prod.fst hp
      omega
    · have hp : (1, n - 1) = (1, vj.1.val) := by
        calc
          (1, n - 1) = edgeValPair (cycleBoundaryPivot hn .cross) :=
            (edgeValPair_cycleBoundaryPivot_cross hn).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.left vj)) := congrArg edgeValPair hij
          _ = (1, vj.1.val) := edgeValPair_cycleBoundaryPivot_left hn vj
      have hvj := vj.2
      have hp2 := congrArg Prod.snd hp
      omega
    · have hp : (1, n - 1) = (vj.1.val, n - 1) := by
        calc
          (1, n - 1) = edgeValPair (cycleBoundaryPivot hn .cross) :=
            (edgeValPair_cycleBoundaryPivot_cross hn).symm
          _ = edgeValPair (cycleBoundaryPivot hn (.right vj)) := congrArg edgeValPair hij
          _ = (vj.1.val, n - 1) := edgeValPair_cycleBoundaryPivot_right hn vj
      have hvj := vj.2
      have hp1 := congrArg Prod.fst hp
      omega
    · rfl

private theorem cycleBoundaryPivot_ne_cycleTreePivot {n : ℕ} (hn : 8 ≤ n)
    (i : CycleBoundaryColumn n) (t : CycleTreeIndex n) :
    cycleBoundaryPivot hn i ≠ cycleTreePivot hn t := by
  intro hit
  have hp := congrArg edgeValPair hit
  rcases i with ei | vi | vi | _
  · have hb := edgeValPair_middle_bounds ei
    change edgeValPair (middleEdgeLift ei) = edgeValPair (cycleTreePivot hn t) at hp
    rcases t with v | k
    · rw [edgeValPair_cycleTreePivot_middle] at hp
      have hp1 := congrArg Prod.fst hp
      omega
    · have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · rw [edgeValPair_cycleTreePivot_zero] at hp
        have hp1 := congrArg Prod.fst hp
        omega
      · rw [edgeValPair_cycleTreePivot_one] at hp
        have hp2 := congrArg Prod.snd hp
        omega
  · rw [edgeValPair_cycleBoundaryPivot_left] at hp
    rcases t with v | k
    · rw [edgeValPair_cycleTreePivot_middle] at hp
      have hp1 := congrArg Prod.fst hp
      omega
    · have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · rw [edgeValPair_cycleTreePivot_zero] at hp
        have hvi := vi.2
        have hp2 := congrArg Prod.snd hp
        omega
      · rw [edgeValPair_cycleTreePivot_one] at hp
        have hp1 := congrArg Prod.fst hp
        omega
  · rw [edgeValPair_cycleBoundaryPivot_right] at hp
    rcases t with v | k
    · rw [edgeValPair_cycleTreePivot_middle] at hp
      have hv := v.2
      have hp2 := congrArg Prod.snd hp
      omega
    · have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · rw [edgeValPair_cycleTreePivot_zero] at hp
        have hp2 := congrArg Prod.snd hp
        omega
      · rw [edgeValPair_cycleTreePivot_one] at hp
        have hvi := vi.2
        have hp1 := congrArg Prod.fst hp
        omega
  · rw [edgeValPair_cycleBoundaryPivot_cross] at hp
    rcases t with v | k
    · rw [edgeValPair_cycleTreePivot_middle] at hp
      have hv := v.2
      have hp2 := congrArg Prod.snd hp
      omega
    · have hk : k = 0 ∨ k = 1 := by omega
      rcases hk with rfl | rfl
      · rw [edgeValPair_cycleTreePivot_zero] at hp
        have hp2 := congrArg Prod.snd hp
        omega
      · rw [edgeValPair_cycleTreePivot_one] at hp
        have hp1 := congrArg Prod.fst hp
        omega

private noncomputable def cycleBoundaryColumn {n : ℕ} (hn : 8 ≤ n) :
    CycleBoundaryColumn n → FlagChain2 (CycleComplementGraph n)
  | .middle e => Finsupp.single (middleRootTriangle hn e) 1
  | .left v =>
      have hvbounds := v.2
      if hv : v.1.val = 4 then
        let a := cycleLeft n hn
        let p := cycleLeftRoot n hn
        let h := cycleLeftHub n hn
        let r := cycleRoot n hn
        let av : (CycleComplementGraph n).Adj a v.1 := cycleLeft_adj_leftArm hn v
        let ap : (CycleComplementGraph n).Adj a p :=
          cycleComplement_adj_of_gap (by simp [a, p]) (by simp [a, p])
        let ah : (CycleComplementGraph n).Adj a h :=
          cycleComplement_adj_of_gap (by simp [a, h]) (by simp [a, h])
        let ph : (CycleComplementGraph n).Adj p h :=
          cycleComplement_adj_of_gap (by simp [p, h]) (by simp [p, h])
        let vh : (CycleComplementGraph n).Adj v.1 h :=
          cycleComplement_adj_of_gap (by simp [h]; omega) (by simp [h]; omega)
        let rp : (CycleComplementGraph n).Adj r p :=
          cycleComplement_adj_of_gap (by simp [r, p]) (by simp [r, p]; omega)
        let rh : (CycleComplementGraph n).Adj r h :=
          cycleComplement_adj_of_gap (by simp [r, h]) (by simp [r, h]; omega)
        let rv : (CycleComplementGraph n).Adj r v.1 :=
          cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
        Finsupp.single (triangleOfAdj _ a p h ap ah ph) 1 +
          Finsupp.single (triangleOfAdj _ a v.1 h av ah vh) 1 +
          Finsupp.single (triangleOfAdj _ r p h rp rh ph) 1 +
          Finsupp.single (triangleOfAdj _ r v.1 h rv rh vh) 1
      else
        let a := cycleLeft n hn
        let p := cycleLeftRoot n hn
        let r := cycleRoot n hn
        let av : (CycleComplementGraph n).Adj a v.1 := cycleLeft_adj_leftArm hn v
        let ap : (CycleComplementGraph n).Adj a p :=
          cycleComplement_adj_of_gap (by simp [a, p]) (by simp [a, p])
        let pv : (CycleComplementGraph n).Adj p v.1 :=
          cycleComplement_adj_of_gap (by simp [p]; omega) (by simp [p])
        let rp : (CycleComplementGraph n).Adj r p :=
          cycleComplement_adj_of_gap (by simp [r, p]) (by simp [r, p]; omega)
        let rv : (CycleComplementGraph n).Adj r v.1 :=
          cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
        Finsupp.single (triangleOfAdj _ a p v.1 ap av pv) 1 +
          Finsupp.single (triangleOfAdj _ r p v.1 rp rv pv) 1
  | .right v =>
      have hvbounds := v.2
      if hv : v.1.val = n - 4 then
        let b := cycleRight n hn
        let q := cycleRightRoot n hn
        let h := cycleRightHub n hn
        let r := cycleRoot n hn
        let bv : (CycleComplementGraph n).Adj b v.1 := cycleRight_adj_rightArm hn v
        let bq : (CycleComplementGraph n).Adj b q := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [b, q] <;> omega
        let bh : (CycleComplementGraph n).Adj b h := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [b, h] <;> omega
        let qh : (CycleComplementGraph n).Adj q h := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [q, h] <;> omega
        let vh : (CycleComplementGraph n).Adj v.1 h := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [h] <;> omega
        let rq : (CycleComplementGraph n).Adj r q :=
          cycleComplement_adj_of_gap (by simp [r, q]; omega) (by simp [r, q]; omega)
        let rh : (CycleComplementGraph n).Adj r h :=
          cycleComplement_adj_of_gap (by simp [r, h]; omega) (by simp [r, h]; omega)
        let rv : (CycleComplementGraph n).Adj r v.1 :=
          cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
        Finsupp.single (triangleOfAdj _ b q h bq bh qh) 1 +
          Finsupp.single (triangleOfAdj _ b v.1 h bv bh vh) 1 +
          Finsupp.single (triangleOfAdj _ r q h rq rh qh) 1 +
          Finsupp.single (triangleOfAdj _ r v.1 h rv rh vh) 1
      else
        let b := cycleRight n hn
        let q := cycleRightRoot n hn
        let r := cycleRoot n hn
        let bv : (CycleComplementGraph n).Adj b v.1 := cycleRight_adj_rightArm hn v
        let bq : (CycleComplementGraph n).Adj b q := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [b, q] <;> omega
        let qv : (CycleComplementGraph n).Adj q v.1 := by
          apply SimpleGraph.Adj.symm
          apply cycleComplement_adj_of_gap <;> simp [q] <;> omega
        let rq : (CycleComplementGraph n).Adj r q :=
          cycleComplement_adj_of_gap (by simp [r, q]; omega) (by simp [r, q]; omega)
        let rv : (CycleComplementGraph n).Adj r v.1 :=
          cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
        Finsupp.single (triangleOfAdj _ b q v.1 bq bv qv) 1 +
          Finsupp.single (triangleOfAdj _ r q v.1 rq rv qv) 1
  | .cross =>
      let a := cycleLeft n hn
      let p := cycleLeftRoot n hn
      let r := cycleRoot n hn
      let q := cycleRightRoot n hn
      let b := cycleRight n hn
      let ap : (CycleComplementGraph n).Adj a p :=
        cycleComplement_adj_of_gap (by simp [a, p]) (by simp [a, p])
      let ab : (CycleComplementGraph n).Adj a b :=
        cycleComplement_adj_of_gap (by simp [a, b]; omega) (by simp [a, b])
      let pb : (CycleComplementGraph n).Adj p b :=
        cycleComplement_adj_of_gap (by simp [p, b]; omega) (by simp [p, b])
      let pq : (CycleComplementGraph n).Adj p q :=
        cycleComplement_adj_of_gap (by simp [p, q]; omega) (by simp [p, q])
      let qb : (CycleComplementGraph n).Adj q b :=
        cycleComplement_adj_of_gap (by simp [q, b]; omega) (by simp [q, b]; omega)
      let rp : (CycleComplementGraph n).Adj r p :=
        cycleComplement_adj_of_gap (by simp [r, p]) (by simp [r, p]; omega)
      let rq : (CycleComplementGraph n).Adj r q :=
        cycleComplement_adj_of_gap (by simp [r, q]; omega) (by simp [r, q]; omega)
      Finsupp.single (triangleOfAdj _ a p b ap ab pb) 1 +
        Finsupp.single (triangleOfAdj _ p q b pq pb qb) 1 +
        Finsupp.single (triangleOfAdj _ r p q rp rq pq) 1

private lemma flagD2_cycleBoundaryColumn_middle {n : ℕ} (hn : 8 ≤ n)
    (e : FlagEdge (MiddleComplementGraph n)) :
    flagD2 (CycleComplementGraph n)
        (cycleBoundaryColumn hn (.middle e)) =
      Finsupp.single (middleEdgeLift e) 1 +
        Sym2.lift
          ⟨fun u v ↦
              Finsupp.single
                  (flagEdgeOfAdj _ (cycleRoot_adj_middle hn u)) 1 +
                Finsupp.single
                  (flagEdgeOfAdj _ (cycleRoot_adj_middle hn v)) 1,
            by intro u v; exact add_comm _ _⟩ e.1 := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
      have huv : (CycleComplementGraph n).Adj u.1 v.1 :=
        (MiddleComplementGraph n).mem_edgeSet.mp he
      rw [cycleBoundaryColumn, flagD2, Finsupp.linearCombination_single,
        one_smul]
      rw [triangleBoundary_eq_three_edges _ (middleRootTriangle hn
        ⟨s(u, v), he⟩) (cycleRoot_adj_middle hn u)
        (cycleRoot_adj_middle hn v) huv (by
          simp [middleRootTriangle, middleEdgeLift, Sym2.toFinset_mk_eq] <;> rfl)]
      have hmiddle : middleEdgeLift ⟨s(u, v), he⟩ =
          flagEdgeOfAdj (CycleComplementGraph n) huv := by
        apply Subtype.ext
        rfl
      simp only [Sym2.lift_mk]
      rw [hmiddle]
      ext z
      simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
      split_ifs <;> decide

private lemma flagD2_cycleBoundaryColumn_left {n : ℕ} (hn : 8 ≤ n)
    (v : LeftArmIndex n) :
    let G := CycleComplementGraph n
    let a := cycleLeft n hn
    let p := cycleLeftRoot n hn
    let r := cycleRoot n hn
    let av : G.Adj a v.1 := cycleLeft_adj_leftArm hn v
    let ap : G.Adj a p :=
      cycleComplement_adj_of_gap (by simp [a, p]) (by simp [a, p])
    let rp : G.Adj r p :=
      cycleComplement_adj_of_gap (by simp [r, p]) (by simp [r, p]; omega)
    let rv : G.Adj r v.1 :=
      cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
    flagD2 G (cycleBoundaryColumn hn (.left v)) =
      Finsupp.single (flagEdgeOfAdj G ap) 1 +
        Finsupp.single (flagEdgeOfAdj G av) 1 +
        Finsupp.single (flagEdgeOfAdj G rp) 1 +
        Finsupp.single (flagEdgeOfAdj G rv) 1 := by
  dsimp only
  by_cases hv : v.1.val = 4
  · simp only [cycleBoundaryColumn, dif_pos hv, map_add,
      flagD2_single_triangleOfAdj]
    ext z
    simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
    split_ifs <;> decide
  · simp only [cycleBoundaryColumn, dif_neg hv, map_add,
      flagD2_single_triangleOfAdj]
    ext z
    simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
    split_ifs <;> decide

private lemma flagD2_cycleBoundaryColumn_right {n : ℕ} (hn : 8 ≤ n)
    (v : RightArmIndex n) :
    let G := CycleComplementGraph n
    let b := cycleRight n hn
    let q := cycleRightRoot n hn
    let r := cycleRoot n hn
    let bv : G.Adj b v.1 := cycleRight_adj_rightArm hn v
    let bq : G.Adj b q := by
      apply SimpleGraph.Adj.symm
      apply cycleComplement_adj_of_gap <;> simp [b, q] <;> omega
    let rq : G.Adj r q :=
      cycleComplement_adj_of_gap (by simp [r, q]; omega) (by simp [r, q]; omega)
    let rv : G.Adj r v.1 :=
      cycleComplement_adj_of_gap (by simp [r]; omega) (by simp [r]; omega)
    flagD2 G (cycleBoundaryColumn hn (.right v)) =
      Finsupp.single (flagEdgeOfAdj G bq) 1 +
        Finsupp.single (flagEdgeOfAdj G bv) 1 +
        Finsupp.single (flagEdgeOfAdj G rq) 1 +
        Finsupp.single (flagEdgeOfAdj G rv) 1 := by
  dsimp only
  by_cases hv : v.1.val = n - 4
  · simp only [cycleBoundaryColumn, dif_pos hv, map_add,
      flagD2_single_triangleOfAdj]
    ext z
    simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
    split_ifs <;> decide
  · simp only [cycleBoundaryColumn, dif_neg hv, map_add,
      flagD2_single_triangleOfAdj]
    ext z
    simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
    split_ifs <;> decide

private lemma flagD2_cycleBoundaryColumn_cross {n : ℕ} (hn : 8 ≤ n) :
    let G := CycleComplementGraph n
    let a := cycleLeft n hn
    let p := cycleLeftRoot n hn
    let r := cycleRoot n hn
    let q := cycleRightRoot n hn
    let b := cycleRight n hn
    let ap : G.Adj a p :=
      cycleComplement_adj_of_gap (by simp [a, p]) (by simp [a, p])
    let ab : G.Adj a b :=
      cycleComplement_adj_of_gap (by simp [a, b]; omega) (by simp [a, b])
    let qb : G.Adj q b :=
      cycleComplement_adj_of_gap (by simp [q, b]; omega) (by simp [q, b]; omega)
    let rp : G.Adj r p :=
      cycleComplement_adj_of_gap (by simp [r, p]) (by simp [r, p]; omega)
    let rq : G.Adj r q :=
      cycleComplement_adj_of_gap (by simp [r, q]; omega) (by simp [r, q]; omega)
    flagD2 G (cycleBoundaryColumn hn .cross) =
      Finsupp.single (flagEdgeOfAdj G ap) 1 +
        Finsupp.single (flagEdgeOfAdj G ab) 1 +
        Finsupp.single (flagEdgeOfAdj G qb) 1 +
        Finsupp.single (flagEdgeOfAdj G rp) 1 +
        Finsupp.single (flagEdgeOfAdj G rq) 1 := by
  dsimp only
  simp only [cycleBoundaryColumn, map_add, flagD2_single_triangleOfAdj]
  ext z
  simp only [Finsupp.add_apply, Finsupp.single_apply, Subtype.ext_iff]
  split_ifs <;> decide

private noncomputable def cycleTreeChainMap {n : ℕ} (hn : 8 ≤ n) :
    (CycleTreeIndex n →₀ F₂) →ₗ[F₂] FlagChain1 (CycleComplementGraph n) :=
  Finsupp.linearCombination F₂
    (fun t ↦ Finsupp.single (cycleTreePivot hn t) 1)

private def leftRootMiddle {n : ℕ} (hn : 8 ≤ n) : MiddleVertex n :=
  ⟨cycleLeftRoot n hn, by simp [cycleLeftRoot]; omega⟩

private def rightRootMiddle {n : ℕ} (hn : 8 ≤ n) : MiddleVertex n :=
  ⟨cycleRightRoot n hn, by simp [cycleRightRoot]; omega⟩

private def leftArmMiddle {n : ℕ} (v : LeftArmIndex n) : MiddleVertex n :=
  ⟨v.1, by have hv := v.2; omega⟩

private def rightArmMiddle {n : ℕ} (v : RightArmIndex n) : MiddleVertex n :=
  ⟨v.1, by have hv := v.2; omega⟩

private noncomputable def cycleBoundaryTreeChain {n : ℕ} (hn : 8 ≤ n) :
    CycleBoundaryColumn n → (CycleTreeIndex n →₀ F₂)
  | .middle e =>
      Sym2.lift
        ⟨fun u v ↦ Finsupp.single (.inl u) 1 + Finsupp.single (.inl v) 1,
          by intro u v; exact add_comm _ _⟩ e.1
  | .left v =>
      Finsupp.single (.inr 0) 1 +
        Finsupp.single (.inl (leftRootMiddle hn)) 1 +
        Finsupp.single (.inl (leftArmMiddle v)) 1
  | .right v =>
      Finsupp.single (.inr 1) 1 +
        Finsupp.single (.inl (rightRootMiddle hn)) 1 +
        Finsupp.single (.inl (rightArmMiddle v)) 1
  | .cross =>
      Finsupp.single (.inr 0) 1 + Finsupp.single (.inr 1) 1 +
        Finsupp.single (.inl (leftRootMiddle hn)) 1 +
        Finsupp.single (.inl (rightRootMiddle hn)) 1

private lemma cycleTreeChainMap_cross_expand {n : ℕ} (hn : 8 ≤ n)
    (hqb : (CycleComplementGraph n).Adj
      (cycleRightRoot n hn) (cycleRight n hn)) :
    cycleTreeChainMap hn (cycleBoundaryTreeChain hn .cross) =
      Finsupp.single (cycleTreePivot hn (.inr 0)) 1 +
        Finsupp.single (flagEdgeOfAdj (CycleComplementGraph n) hqb) 1 +
        Finsupp.single (cycleTreePivot hn (.inl (leftRootMiddle hn))) 1 +
        Finsupp.single (cycleTreePivot hn (.inl (rightRootMiddle hn))) 1 := by
  simp only [cycleBoundaryTreeChain, map_add, cycleTreeChainMap,
    Finsupp.linearCombination_single, one_smul]
  rw [cycleTreePivot_one_eq_rightRootRight hn hqb]

private lemma flagD2_cycleBoundaryColumn_normal {n : ℕ} (hn : 8 ≤ n)
    (i : CycleBoundaryColumn n) :
    flagD2 (CycleComplementGraph n) (cycleBoundaryColumn hn i) =
      Finsupp.single (cycleBoundaryPivot hn i) 1 +
        cycleTreeChainMap hn (cycleBoundaryTreeChain hn i) := by
  rcases i with e | v | v | _
  · rw [flagD2_cycleBoundaryColumn_middle]
    rcases e with ⟨e, he⟩
    induction e using Sym2.ind with
    | _ u v =>
        simp [cycleBoundaryPivot, cycleBoundaryTreeChain, cycleTreeChainMap,
          cycleTreePivot, middleEdgeLift] <;>
          ext z <;>
          simp only [Finsupp.add_apply, Finsupp.single_apply,
            Subtype.ext_iff] <;>
          abel
  · rw [flagD2_cycleBoundaryColumn_left]
    simp [cycleBoundaryPivot, cycleBoundaryTreeChain, cycleTreeChainMap,
      cycleTreePivot, leftRootMiddle, leftArmMiddle] <;>
      ext z <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply,
        Subtype.ext_iff] <;>
      abel
  · rw [flagD2_cycleBoundaryColumn_right]
    simp [cycleBoundaryPivot, cycleBoundaryTreeChain, cycleTreeChainMap,
      cycleTreePivot, rightRootMiddle, rightArmMiddle] <;>
      ext z <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply,
        Subtype.ext_iff] <;>
      abel
  · rw [flagD2_cycleBoundaryColumn_cross]
    let hqb : (CycleComplementGraph n).Adj
        (cycleRightRoot n hn) (cycleRight n hn) :=
      cycleComplement_adj_of_gap
        (by simp [cycleRightRoot, cycleRight]; omega)
        (by simp [cycleRightRoot, cycleRight]; omega)
    rw [cycleTreeChainMap_cross_expand hn hqb]
    simp [cycleBoundaryPivot, cycleBoundaryTreeChain, cycleTreeChainMap,
      cycleTreePivot, leftRootMiddle, rightRootMiddle] <;>
      ext z <;>
      simp only [Finsupp.add_apply, Finsupp.single_apply,
        Subtype.ext_iff] <;>
      abel

private lemma cycleTreeChainMap_at_boundaryPivot {n : ℕ} (hn : 8 ≤ n)
    (c : CycleTreeIndex n →₀ F₂) (i : CycleBoundaryColumn n) :
    cycleTreeChainMap hn c (cycleBoundaryPivot hn i) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp [map_add, hc, hd]
  | single t a =>
      rw [cycleTreeChainMap, Finsupp.linearCombination_single,
        Finsupp.smul_apply, Finsupp.single_apply]
      rw [if_neg (Ne.symm (cycleBoundaryPivot_ne_cycleTreePivot hn i t))]
      simp

private theorem cycleBoundaryColumn_delta {n : ℕ} (hn : 8 ≤ n)
    (i j : CycleBoundaryColumn n) :
    flagD2 (CycleComplementGraph n) (cycleBoundaryColumn hn j)
        (cycleBoundaryPivot hn i) = if j = i then 1 else 0 := by
  rw [flagD2_cycleBoundaryColumn_normal, Finsupp.add_apply,
    Finsupp.single_apply, cycleTreeChainMap_at_boundaryPivot]
  rw [if_congr (cycleBoundaryPivot_injective hn).eq_iff rfl rfl]
  simp

/-- For every cycle of length at least eight, the complement's flag complex has
trivial first homology over F₂.  The proof exhibits a full identity minor in
the triangle-boundary matrix rather than assuming an abstract homology value. -/
theorem cycle_complement_h1_zero_of_eight_le (n : ℕ) (hn : 8 ≤ n) :
    flagBeta1F2 (cycleGraph n)ᶜ = 0 := by
  apply flagBeta1_eq_zero_of_boundary_columns
    (CycleComplementGraph n)
    (cycleComplement_connected hn)
    (cycleBoundaryColumn hn)
    (cycleBoundaryPivot hn)
    (cycleBoundaryColumn_delta hn)
  simpa only [Fintype.card_fin] using
    cycleBoundaryColumn_card_lower_for hn
      CategoryTheory.FinCategory.fintypeObj

end CycleComplementColumns

/-- The complement of the seven-cycle, used for the explicit boundary-rank
calculation below. -/
abbrev SevenGraph : SimpleGraph (Fin 7) := (cycleGraph 7)ᶜ

/-- The seven independent triples of the seven-cycle, indexed cyclically. -/
def sevenTriangle (i : Fin 7) : FlagTriangle SevenGraph := by
  refine ⟨{i, i + 2, i + 4}, ?_, ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> decide

/-- The distance-three edge unique to the corresponding independent triple. -/
def sevenWitnessEdge (i : Fin 7) : FlagEdge SevenGraph := by
  refine ⟨s(i, i + 4), ?_⟩
  fin_cases i <;> decide

private theorem sevenTriangle_bijective :
    Function.Bijective sevenTriangle := by
  decide

private theorem sevenWitnessEdge_injective :
    Function.Injective sevenWitnessEdge := by
  decide

noncomputable def sevenTriangleEquiv :
    Fin 7 ≃ FlagTriangle SevenGraph :=
  Equiv.ofBijective sevenTriangle sevenTriangle_bijective

private lemma triangleBoundary_sevenTriangle_witness (i j : Fin 7) :
    triangleBoundary SevenGraph (sevenTriangle j) (sevenWitnessEdge i) =
      if j = i then 1 else 0 := by
  rw [triangleBoundary_apply]
  fin_cases i <;> fin_cases j <;> decide

private lemma triangleBoundary_seven_witness
    (t : FlagTriangle SevenGraph) (i : Fin 7) :
    triangleBoundary SevenGraph t (sevenWitnessEdge i) =
      if t = sevenTriangle i then 1 else 0 := by
  obtain ⟨j, rfl⟩ := sevenTriangle_bijective.2 t
  rw [triangleBoundary_sevenTriangle_witness]
  by_cases hji : j = i
  · subst j
    simp
  · have htri : sevenTriangle j ≠ sevenTriangle i := by
      exact fun h ↦ hji (sevenTriangle_bijective.1 h)
    simp [hji, htri]

private lemma flagD2_seven_witness
    (c : FlagChain2 SevenGraph) (i : Fin 7) :
    flagD2 SevenGraph c (sevenWitnessEdge i) = c (sevenTriangle i) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
      simp only [map_add, Finsupp.add_apply, hc, hd]
  | single t a =>
      rw [flagD2, Finsupp.linearCombination_single, Finsupp.smul_apply,
        triangleBoundary_seven_witness]
      by_cases hti : t = sevenTriangle i
      · subst t
        simp
      · simp [hti]

private theorem flagD2_seven_injective :
    Function.Injective (flagD2 SevenGraph) := by
  intro c d hcd
  ext t
  let i : Fin 7 := (sevenTriangleEquiv.symm t)
  have hval := congrArg (fun z : FlagChain1 SevenGraph ↦ z (sevenWitnessEdge i)) hcd
  change flagD2 SevenGraph c (sevenWitnessEdge i) =
    flagD2 SevenGraph d (sevenWitnessEdge i) at hval
  rw [flagD2_seven_witness, flagD2_seven_witness] at hval
  have ht : sevenTriangle i = t := by
    change sevenTriangle (sevenTriangleEquiv.symm t) = t
    exact sevenTriangleEquiv.apply_symm_apply t
  simpa [ht] using hval

private theorem flagD2Cycle_seven_injective :
    Function.Injective (flagD2Cycle SevenGraph) := by
  intro c d hcd
  apply flagD2_seven_injective
  exact congrArg Subtype.val hcd

/-- At seven vertices the distance-three coordinates show that all seven
triangle boundaries are independent, leaving one first-homology class. -/
theorem cycle_seven_complement_h1_equiv_bool :
    flagBeta1F2 (cycleGraph 7)ᶜ = 1 := by
  classical
  have hconn : SevenGraph.Connected := by decide
  have hchain1 : Module.finrank F₂ (FlagChain1 SevenGraph) = 14 := by
    rw [Module.finrank_finsupp_self]
    decide
  have hrange :
      Module.finrank F₂ (LinearMap.range (flagD1 SevenGraph)) = 6 := by
    rw [range_flagD1_eq_reducedVertices_of_connected SevenGraph hconn,
      finrank_reducedVertexChains hconn.nonempty]
    norm_num
  have hdim := LinearMap.finrank_range_add_finrank_ker (flagD1 SevenGraph)
  have hcycles' : Module.finrank F₂ (FlagCycle SevenGraph) = 8 := by
    rw [hrange, hchain1] at hdim
    change Module.finrank F₂ (LinearMap.ker (flagD1 SevenGraph)) = 8
    omega
  have hchain2 : Module.finrank F₂ (FlagChain2 SevenGraph) = 7 := by
    rw [Module.finrank_finsupp_self]
    decide
  have hboundaries :=
    LinearMap.finrank_range_of_inj flagD2Cycle_seven_injective
  rw [hchain2] at hboundaries
  change Module.finrank F₂ (FlagBoundarySubmodule SevenGraph) = 7 at hboundaries
  unfold flagBeta1F2
  rw [Submodule.finrank_quotient, hcycles', hboundaries]

theorem cycle_complement_reduced_h0
    (n : ℕ) (hn : 3 ≤ n) :
    (n = 3 → Module.finrank F₂ (ReducedComponentCode (cycleGraph n)ᶜ) = 2) ∧
    (n = 4 → Module.finrank F₂ (ReducedComponentCode (cycleGraph n)ᶜ) = 1) ∧
    (5 ≤ n → Module.finrank F₂ (ReducedComponentCode (cycleGraph n)ᶜ) = 0) := by
  constructor
  · intro h3
    subst n
    rw [finrank_reducedComponentCode]
    have hc : Fintype.card ((cycleGraph 3)ᶜ).ConnectedComponent = 3 := by
      decide
    omega
  constructor
  · intro h4
    subst n
    rw [finrank_reducedComponentCode]
    have hc : Fintype.card ((cycleGraph 4)ᶜ).ConnectedComponent = 2 := by
      decide
    omega
  · intro h5
    have hdeg : ∀ v, (cycleGraph n).degree v = 2 := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h5
      rw [Nat.add_comm] at hk
      subst n
      intro v
      simpa [Nat.add_assoc] using
        (cycleGraph_degree_three_le (n := k + 2) (v := v))
    have hconn : (cycleGraph n)ᶜ.Connected :=
      two_regular_complement_connected_of_five_le (cycleGraph n)
        (by simpa using h5) hdeg
    rw [finrank_reducedComponentCode]
    have hc : Fintype.card ((cycleGraph n)ᶜ).ConnectedComponent = 1 := by
      apply Fintype.card_eq_one_iff.mpr
      letI : Subsingleton ((cycleGraph n)ᶜ).ConnectedComponent :=
        hconn.preconnected.subsingleton_connectedComponent
      let c := (cycleGraph n)ᶜ.connectedComponentMk
        (Classical.choice hconn.nonempty)
      exact ⟨c, fun d ↦ Subsingleton.elim d c⟩
    omega

theorem cycle_complement_low_h1 (n : ℕ) (hn : 7 ≤ n) :
    flagBeta1F2 (cycleGraph n)ᶜ ≤ 1 := by
  by_cases h7 : n = 7
  · subst n
    rw [cycle_seven_complement_h1_equiv_bool]
  · have h8 : 8 ≤ n := by omega
    rw [cycle_complement_h1_zero_of_eight_le n h8]
    omega

/-- With canonical edge/face bases the joined graph needs neither a vertex
order nor a separate decidability binder. -/
theorem sum_complement_h1_equiv_tensor_reduced_h0
    (G : SimpleGraph V) [Nonempty V]
    {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) :
    Nonempty
      (FlagH1F2 (G ⊕g H)ᶜ ≃ₗ[F₂]
        TensorProduct F₂ (ReducedComponentCode Gᶜ) (ReducedComponentCode Hᶜ)) := by
  exact ⟨ExtremalFullJoinBridge.joinedFlagH1EquivTensorReduced G H⟩

private lemma cycleGraph_degree_eq_two_of_three_le
    {n : ℕ} (hn : 3 ≤ n) (v : Fin n) :
    (cycleGraph n).degree v = 2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hk
  subst n
  simpa [Nat.add_assoc] using
    (cycleGraph_degree_three_le (n := k) (v := v))

private lemma cycleGraph_neighbor_pair_card_of_three_le
    {n : ℕ} [NeZero n] (hn : 3 ≤ n) (v : Fin n) :
    #{v - 1, v + 1} = 2 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm] at hk
  subst n
  calc
    #{v - 1, v + 1} = (cycleGraph (k + 3)).degree v := by
      simpa [Nat.add_assoc] using
        (cycleGraph_degree_two_le (n := k + 1) (v := v)).symm
    _ = 2 := cycleGraph_degree_three_le (n := k) (v := v)

private lemma cycle_getVert_fin_succ_adj
    (Q : SimpleGraph V) {u : V} {p : Q.Walk u u}
    (hp : p.IsCycle) [NeZero p.length] (i : Fin p.length) :
    Q.Adj (p.getVert i.val) (p.getVert (i + 1).val) := by
  have hadj := p.adj_getVert_succ i.isLt
  convert hadj using 1
  have hone : ((1 : Fin p.length).val) = 1 := by
    change 1 % p.length = 1
    exact Nat.mod_eq_of_lt (by have := hp.three_le_length; omega)
  rw [Fin.val_add_eq_ite, hone]
  split_ifs with hi
  · have hilast : i.val + 1 = p.length := by
      have hiLt := i.isLt
      omega
    simp only [hilast, Nat.sub_self, p.getVert_zero, p.getVert_length]
  · rfl

theorem connected_two_regular_iso_cycle
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hconn : Q.Connected)
    (hdeg : ∀ v, Q.degree v = 2) :
    ∃ ℓ : ℕ, 3 ≤ ℓ ∧ ℓ = Fintype.card V ∧
      Nonempty (Q ≃g cycleGraph ℓ) := by
  classical
  have hcycles : Q.IsCycles := by
    intro v _
    rw [Set.ncard_eq_toFinset_card']
    simpa only [neighborFinset, card_neighborFinset_eq_degree] using hdeg v
  let u : V := Classical.choice hconn.nonempty
  let C : Q.ConnectedComponent := Q.connectedComponentMk u
  have huC : u ∈ C.supp := by
    exact ConnectedComponent.connectedComponentMk_mem
  have hnu : (Q.neighborSet u).Nonempty := by
    rw [← degree_pos_iff_nonempty, hdeg]
    omega
  obtain ⟨p, hp, hpverts⟩ :=
    hcycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp huC hnu
  have hplen : 3 ≤ p.length := hp.three_le_length
  letI : NeZero p.length := ⟨by omega⟩
  have hCsupp : C.supp = Set.univ := by
    ext v
    simp only [ConnectedComponent.mem_supp_iff, Set.mem_univ, iff_true]
    change Q.connectedComponentMk v = Q.connectedComponentMk u
    rw [ConnectedComponent.eq]
    exact hconn v u
  have hpall : p.toSubgraph.verts = Set.univ := hpverts.trans hCsupp
  have hpHam : p.IsHamiltonianCycle := by
    refine ⟨hp, hp.isPath_tail.isHamiltonian_of_mem ?_⟩
    intro v
    rw [p.support_tail_of_not_nil hp.not_nil]
    by_cases hvu : v = u
    · subst v
      exact p.end_mem_tail_support hp.not_nil
    · have hvp : v ∈ p.support := by
        rw [← Walk.mem_verts_toSubgraph, hpall]
        trivial
      rw [← p.cons_tail_support] at hvp
      exact (List.mem_cons.mp hvp).resolve_left hvu
  let f : Fin p.length → V := fun i ↦ p.getVert i.val
  have hfInjective : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    apply hp.getVert_injOn'
    · simp only [Set.mem_setOf_eq]
      have hi := i.isLt
      omega
    · simp only [Set.mem_setOf_eq]
      have hj := j.isLt
      omega
    · change p.getVert i.val = p.getVert j.val at hij
      exact hij
  have hfSurjective : Function.Surjective f := by
    intro v
    have hvp : v ∈ p.support := by
      rw [← Walk.mem_verts_toSubgraph, hpall]
      trivial
    obtain ⟨i, hiv, hilength⟩ := Walk.mem_support_iff_exists_getVert.mp hvp
    by_cases hi : i < p.length
    · exact ⟨⟨i, hi⟩, hiv⟩
    · have hiEq : i = p.length := by omega
      refine ⟨0, ?_⟩
      change p.getVert 0 = v
      simpa [hiEq] using hiv
  let e : Fin p.length ≃ V := Equiv.ofBijective f ⟨hfInjective, hfSurjective⟩
  have he_apply (i : Fin p.length) : e i = p.getVert i.val := rfl
  have honeFin : ((1 : Fin p.length).val) = 1 := by
    change 1 % p.length = 1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucc (i : Fin p.length) : Q.Adj (e i) (e (i + 1)) := by
    simpa only [he_apply] using cycle_getVert_fin_succ_adj Q hp i
  have hpred (i : Fin p.length) : Q.Adj (e i) (e (i - 1)) := by
    have h := (hsucc (i - 1)).symm
    simpa only [sub_add_cancel] using h
  have hpairs (i : Fin p.length) :
      Q.neighborFinset (e i) = {e (i - 1), e (i + 1)} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [mem_insert, mem_singleton] at hv
      rcases hv with rfl | rfl
      · simpa only [mem_neighborFinset] using hpred i
      · simpa only [mem_neighborFinset] using hsucc i
    · rw [card_neighborFinset_eq_degree, hdeg]
      have hcycleCard : #{i - 1, i + 1} = 2 :=
        cycleGraph_neighbor_pair_card_of_three_le hplen i
      have hpairCard : #{e (i - 1), e (i + 1)} = 2 :=
        card_pair_eq_two_iff.mpr fun hij ↦
          (card_pair_eq_two_iff.mp hcycleCard) (e.injective hij)
      omega
  let φ : cycleGraph p.length ≃g Q :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        constructor
        · intro hij
          rw [← mem_neighborFinset, hpairs i] at hij
          simp only [mem_insert, mem_singleton] at hij
          rcases hij with hij | hij
          · have hji : j = i - 1 := e.injective hij
            subst j
            rw [cycleGraph_adj']
            left
            simpa only [sub_sub_cancel] using honeFin
          · have hji : j = i + 1 := e.injective hij
            subst j
            rw [cycleGraph_adj']
            right
            simpa only [add_sub_cancel_left] using honeFin
        · intro hij
          rw [cycleGraph_adj'] at hij
          rcases hij with hij | hij
          · have hfin : i - j = 1 := Fin.ext (by simpa only [honeFin] using hij)
            rw [sub_eq_iff_eq_add'] at hfin
            simpa only [hfin, add_comm] using (hsucc j).symm
          · have hfin : j - i = 1 := Fin.ext (by simpa only [honeFin] using hij)
            rw [sub_eq_iff_eq_add'] at hfin
            simpa only [hfin] using hsucc i }
  exact ⟨p.length, hp.three_le_length, hpHam.length_eq, ⟨φ.symm⟩⟩

theorem connectedComponent_sum_complement_iso
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (C : Q.ConnectedComponent) :
    let S : Set V := C.supp
    Nonempty (Q ≃g (Q.induce S ⊕g Q.induce (Sᶜ : Set V))) := by
  classical
  let S : Set V := C.supp
  let e : (Q.induce S ⊕g Q.induce (Sᶜ : Set V)) ≃g Q :=
    { toEquiv := Equiv.Set.sumCompl S
      map_rel_iff' := by
        rintro (u | u) (v | v)
        · rfl
        · simp only [Equiv.Set.sumCompl_apply_inl,
            Equiv.Set.sumCompl_apply_inr, SimpleGraph.sum]
          constructor
          · intro h
            exact (v.2 ((C.mem_supp_congr_adj h).mp u.2)).elim
          · intro h
            simp at h
        · simp only [Equiv.Set.sumCompl_apply_inl,
            Equiv.Set.sumCompl_apply_inr, SimpleGraph.sum]
          constructor
          · intro h
            exact (u.2 ((C.mem_supp_congr_adj h).mpr v.2)).elim
          · intro h
            simp at h
        · rfl }
  exact ⟨e.symm⟩

theorem two_regular_complement_h1_atMostTwo
    (Q : SimpleGraph V) [DecidableRel Q.Adj]
    (hcard : 7 ≤ Fintype.card V)
    (hdeg : ∀ v, Q.degree v = 2) :
    FlagH1F2AtMostTwo Qᶜ := by
  classical
  unfold FlagH1F2AtMostTwo flagBeta1F2
  by_cases hQconn : Q.Connected
  · obtain ⟨ℓ, hℓ3, hℓcard, ⟨e⟩⟩ :=
      connected_two_regular_iso_cycle Q hQconn hdeg
    let ec : Qᶜ ≃g (cycleGraph ℓ)ᶜ :=
      { e.toEquiv with
        map_rel_iff' :=
          (SimpleGraph.Embedding.complEquiv e.toEmbedding).map_rel_iff }
    obtain ⟨eh⟩ := flagH1F2_congr Qᶜ (cycleGraph ℓ)ᶜ ec
    rw [eh.finrank_eq]
    exact (cycle_complement_low_h1 ℓ (by omega)).trans (by omega)
  · have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
    let v₀ : V := Classical.choice hV
    let C : Q.ConnectedComponent := Q.connectedComponentMk v₀
    let S : Set V := C.supp
    have hv₀S : v₀ ∈ S := by
      change v₀ ∈ C.supp
      exact ConnectedComponent.connectedComponentMk_mem
    have hfar : ∀ v : V, ∃ w : V, ¬Q.Reachable v w := by
      rw [Q.connected_iff_exists_forall_reachable] at hQconn
      push_neg at hQconn
      exact hQconn
    obtain ⟨w₀, hw₀⟩ := hfar v₀
    have hw₀S : w₀ ∈ (Sᶜ : Set V) := by
      rw [Set.mem_compl_iff]
      intro hwS
      exact hw₀ (C.reachable_of_mem_supp hv₀S hwS)
    letI : Nonempty S := ⟨⟨v₀, hv₀S⟩⟩
    letI : Nonempty (Sᶜ : Set V) := ⟨⟨w₀, hw₀S⟩⟩
    let G : SimpleGraph S := Q.induce S
    let H : SimpleGraph (Sᶜ : Set V) := Q.induce (Sᶜ : Set V)
    have hGconn : G.Connected := by
      simpa [G, S] using C.connected_toSimpleGraph
    have hGdeg : ∀ x, G.degree x = 2 := by
      intro x
      calc
        G.degree x = Q.degree (x : V) := by
          apply Q.degree_induce_of_neighborSet_subset
          intro y hy
          exact C.mem_supp_of_adj_mem_supp x.2 hy
        _ = 2 := hdeg x
    have hHdeg : ∀ x, H.degree x = 2 := by
      intro x
      calc
        H.degree x = Q.degree (x : V) := by
          apply Q.degree_induce_of_neighborSet_subset
          intro y hy
          rw [Set.mem_compl_iff]
          intro hyS
          exact x.2 ((C.mem_supp_congr_adj hy).mpr hyS)
        _ = 2 := hdeg x
    have heQ : Nonempty (Q ≃g (G ⊕g H)) := by
      simpa [G, H, S] using connectedComponent_sum_complement_iso Q C
    obtain ⟨eQ⟩ := heQ
    let eQc : Qᶜ ≃g (G ⊕g H)ᶜ :=
      { eQ.toEquiv with
        map_rel_iff' :=
          (SimpleGraph.Embedding.complEquiv eQ.toEmbedding).map_rel_iff }
    obtain ⟨eSplit⟩ := flagH1F2_congr Qᶜ (G ⊕g H)ᶜ eQc
    obtain ⟨eJoin⟩ := sum_complement_h1_equiv_tensor_reduced_h0 G H
    have hRank :
        Module.finrank F₂ (FlagH1F2 Qᶜ) =
          Module.finrank F₂ (ReducedComponentCode Gᶜ) *
            Module.finrank F₂ (ReducedComponentCode Hᶜ) := by
      calc
        Module.finrank F₂ (FlagH1F2 Qᶜ) =
            Module.finrank F₂ (FlagH1F2 (G ⊕g H)ᶜ) := eSplit.finrank_eq
        _ = Module.finrank F₂
              (TensorProduct F₂ (ReducedComponentCode Gᶜ)
                (ReducedComponentCode Hᶜ)) := eJoin.finrank_eq
        _ = Module.finrank F₂ (ReducedComponentCode Gᶜ) *
              Module.finrank F₂ (ReducedComponentCode Hᶜ) :=
          Module.finrank_tensorProduct
    rw [hRank]
    by_cases hHconn : H.Connected
    · obtain ⟨ℓG, hℓG3, hℓGcard, ⟨eG⟩⟩ :=
        connected_two_regular_iso_cycle G hGconn hGdeg
      obtain ⟨ℓH, hℓH3, hℓHcard, ⟨eH⟩⟩ :=
        connected_two_regular_iso_cycle H hHconn hHdeg
      let eGc : Gᶜ ≃g (cycleGraph ℓG)ᶜ :=
        { eG.toEquiv with
          map_rel_iff' :=
            (SimpleGraph.Embedding.complEquiv eG.toEmbedding).map_rel_iff }
      let eHc : Hᶜ ≃g (cycleGraph ℓH)ᶜ :=
        { eH.toEquiv with
          map_rel_iff' :=
            (SimpleGraph.Embedding.complEquiv eH.toEmbedding).map_rel_iff }
      have hGdim := finrank_reducedComponentCode_congr Gᶜ
        (cycleGraph ℓG)ᶜ eGc
      have hHdim := finrank_reducedComponentCode_congr Hᶜ
        (cycleGraph ℓH)ᶜ eHc
      obtain ⟨hG3, hG4, hG5⟩ := cycle_complement_reduced_h0 ℓG hℓG3
      obtain ⟨hH3, hH4, hH5⟩ := cycle_complement_reduced_h0 ℓH hℓH3
      have hcardSplit :
          Fintype.card V = Fintype.card S + Fintype.card (Sᶜ : Set V) := by
        simpa using (Fintype.card_congr (Equiv.Set.sumCompl S)).symm
      have htotal : 7 ≤ ℓG + ℓH := by omega
      by_cases hGlarge : 5 ≤ ℓG
      · rw [hGdim, hG5 hGlarge]
        simp
      by_cases hHlarge : 5 ≤ ℓH
      · rw [hHdim, hH5 hHlarge]
        simp
      have hGsmall : ℓG = 3 ∨ ℓG = 4 := by omega
      have hHsmall : ℓH = 3 ∨ ℓH = 4 := by omega
      rcases hGsmall with hGthree | hGfour <;>
        rcases hHsmall with hHthree | hHfour
      · omega
      · rw [hGdim, hG3 hGthree, hHdim, hH4 hHfour]
      · rw [hGdim, hG4 hGfour, hHdim, hH3 hHthree]
      · rw [hGdim, hG4 hGfour, hHdim, hH4 hHfour]
        norm_num
    · have hHcconn : Hᶜ.Connected :=
        H.connected_or_connected_compl.resolve_left hHconn
      have hHcomponents : Fintype.card Hᶜ.ConnectedComponent = 1 := by
        apply Fintype.card_eq_one_iff.mpr
        letI : Subsingleton Hᶜ.ConnectedComponent :=
          hHcconn.preconnected.subsingleton_connectedComponent
        let c := Hᶜ.connectedComponentMk
          (Classical.choice hHcconn.nonempty)
        exact ⟨c, fun d ↦ Subsingleton.elim d c⟩
      have hHdim :
          Module.finrank F₂ (ReducedComponentCode Hᶜ) = 0 := by
        rw [finrank_reducedComponentCode Hᶜ, hHcomponents]
      rw [hHdim]
      simp

theorem n_edges_complement_h1_atMostTwo
    {n : ℕ} (hn : 7 ≤ n) (Q : SimpleGraph (Fin n))
    [DecidableRel Q.Adj]
    (hQ : #Q.edgeFinset = n) :
    FlagH1F2AtMostTwo Qᶜ := by
  classical
  have hsum : ∑ v : Fin n, Q.degree v = 2 * n := by
    simpa [hQ] using Q.sum_degrees_eq_twice_card_edges
  by_cases hzero : ∃ v, Q.degree v = 0
  · obtain ⟨v, hv⟩ := hzero
    have hviso : Q.IsIsolated v := (Q.degree_eq_zero (v := v)).mp hv
    apply flag_h1_cone_at_most_two Qᶜ v
    intro w hvw
    rw [Q.compl_adj]
    exact ⟨hvw.symm, hviso (w := w)⟩
  by_cases hone : ∃ v, Q.degree v = 1
  · obtain ⟨v, hv⟩ := hone
    obtain ⟨w, hvw, hunique⟩ := Q.degree_eq_one_iff_existsUnique_adj.mp hv
    have hleaf : ∀ x, Q.Adj v x ↔ x = w := by
      intro x
      constructor
      · exact hunique x
      · rintro rfl
        exact hvw
    let U : Set (Fin n) := {x | x ≠ w ∧ ¬Q.Adj w x}
    let J : SimpleGraph U := Q.induce U
    rcases flag_h1_leaf_injects_into_components Q v w hleaf with ⟨e⟩
    have hJE : #J.edgeFinset ≤ Fintype.card U + 1 := by
      have hQ' : #Q.edgeFinset = Fintype.card (Fin n) := by simpa using hQ
      simpa [U, J] using leaf_remainder_edges_le_vertices_add_one Q w hQ'
    have hcomp : Fintype.card (Jᶜ).ConnectedComponent ≤ 3 :=
      complement_components_le_three_of_edges_le_vertices_add_one J hJE
    have hred : Module.finrank F₂ (ReducedComponentCode Jᶜ) ≤ 2 :=
      reducedComponentCode_atMostTwo Jᶜ hcomp
    unfold FlagH1F2AtMostTwo flagBeta1F2
    rw [LinearEquiv.finrank_eq e]
    exact hred
  · have hlower : ∀ v : Fin n, 2 ≤ Q.degree v := by
      intro v
      have hv0 : Q.degree v ≠ 0 := fun h ↦ hzero ⟨v, h⟩
      have hv1 : Q.degree v ≠ 1 := fun h ↦ hone ⟨v, h⟩
      omega
    have hdeg : ∀ v : Fin n, Q.degree v = 2 := by
      have hconst : ∑ _v : Fin n, 2 = ∑ v : Fin n, Q.degree v := by
        simp [hsum, mul_comm]
      have hall :=
        (Finset.sum_eq_sum_iff_of_le (s := univ)
          (fun v _ ↦ hlower v)).mp hconst
      intro v
      exact (hall v (mem_univ v)).symm
    exact two_regular_complement_h1_atMostTwo Q (by simpa using hn) hdeg

theorem universal_flag_beta1_f2_le_two
    {n : ℕ} (hn : 7 ≤ n) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj]
    (hE : #F.edgeFinset = n.choose 2 - n) :
    FlagH1F2AtMostTwo F := by
  let Q : SimpleGraph (Fin n) := Fᶜ
  have hQedges : #Q.edgeFinset = n := by
    have hpartition :
        Q.edgeFinset =
          (⊤ : SimpleGraph (Fin n)).edgeFinset \ F.edgeFinset := by
      ext e
      induction e using Sym2.ind with
      | h u v => simp [Q, SimpleGraph.compl_adj]
    rw [hpartition, card_sdiff_of_subset (edgeFinset_mono le_top)]
    have htop : #(⊤ : SimpleGraph (Fin n)).edgeFinset = n.choose 2 := by
      simpa using (card_edgeFinset_top_eq_card_choose_two (V := Fin n))
    rw [htop, hE]
    have hnchoose : n ≤ n.choose 2 := by
      rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide : 0 < 2)]
      have hpred : n - 1 + 1 = n := by omega
      nlinarith
    have hsplit : n.choose 2 - n + n = n.choose 2 :=
      Nat.sub_add_cancel hnchoose
    omega
  have hbound := n_edges_complement_h1_atMostTwo hn Q hQedges
  simpa [Q] using hbound

end UpperBoundReductions

section PaperLevelBundle

def HasCompleteBipartiteSpanning {V : Type*}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A : Finset V,
    A.Nonempty ∧ A ≠ univ ∧
      ∀ u ∈ A, ∀ v ∈ univ \ A, G.Adj u v

theorem dense_range_nat_strict {n : ℕ} (hn : 7 ≤ n) :
    n ^ 2 / 4 < n.choose 2 - n := by
  have hnchoose : n ≤ n.choose 2 := by
    rw [Nat.choose_two_right, Nat.le_div_iff_mul_le (by decide : 0 < 2)]
    have hpred : n - 1 + 1 = n := by omega
    nlinarith
  have hchooseTwice : n.choose 2 * 2 = n * (n - 1) := by
    rw [Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self n)]
  have hpredThree : n - 3 + 3 = n := by omega
  have hpredOne : n - 1 = (n - 3) + 2 := by omega
  have hproductSplit : n * (n - 1) = n * (n - 3) + 2 * n := by
    rw [hpredOne]
    ring
  have htwiceRemainder : 2 * (n.choose 2 - n) = n * (n - 3) := by
    have hsplit := Nat.sub_add_cancel hnchoose
    omega
  have hfourRemainder :
      4 * (n.choose 2 - n) = 2 * n * (n - 3) := by
    calc
      4 * (n.choose 2 - n) = 2 * (2 * (n.choose 2 - n)) := by ring
      _ = 2 * (n * (n - 3)) := by rw [htwiceRemainder]
      _ = 2 * n * (n - 3) := by ring
  have hfloor : 4 * (n ^ 2 / 4) ≤ n ^ 2 := by
    simpa [mul_comm] using Nat.div_mul_le_self (n ^ 2) 4
  have hcleared : n ^ 2 < 2 * n * (n - 3) := by
    nlinarith
  omega

theorem dense_extremal_flag_counterexample_f2
    {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n ∧
    n ^ 2 / 4 < #(FamilyG n).edgeFinset ∧
    FlagH1F2ExactlyTwo (FamilyG n) ∧
    (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      #F.edgeFinset = n.choose 2 - n → FlagH1F2AtMostTwo F) ∧
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  have hedge : #(FamilyG n).edgeFinset = n.choose 2 - n :=
    ExtremalFlagBetti.family_complement_edge_count hn
  refine ⟨hedge, ?_, family_actual_flag_h1_exactly_two hn, ?_, ?_⟩
  · rw [hedge]
    exact dense_range_nat_strict hn
  · intro F _ hF
    exact universal_flag_beta1_f2_le_two hn F hF
  · simpa only [HasCompleteBipartiteSpanning,
      ExtremalFlagBetti.HasCompleteBipartiteSpanning, FamilyG] using
      ExtremalFlagBetti.family_no_complete_bipartite_spanning hn

end PaperLevelBundle

end


end ExtremalFlagBetti.ActualHomology
