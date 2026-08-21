/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar F₂ flag-homology upgrade: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib

/-!
# Actual F₂ flag homology for the dense extremal family

The definitions below are the ordinary finite simplicial chain complex of a
graph's flag complex in degrees zero, one, and two. Edges are unordered
`Sym2` pairs, triangular faces are three-element clique finsets, and first
homology is `ker d₁ / range d₂` over `ZMod 2`.

The chain-complex identity `d₁ ∘ d₂ = 0` is selected together with three
paper-level results: the family's actual F₂ first Betti number, Proposition
3.1's universal F₂ upper bound, and their dense/no-spanning-biclique bundle.
No arbitrary-field, integral-homology, or finite-census claim is made.
-/

open Finset SimpleGraph

namespace ExtremalFlagBetti.ActualHomology

abbrev F₂ := ZMod 2

noncomputable section

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V)

/-- Unordered edges of `G`. -/
abbrev FlagEdge := {e : Sym2 V // e ∈ G.edgeSet}

/-- Three-vertex clique faces of the flag complex. -/
abbrev FlagTriangle :=
  {s : Finset V // s.card = 3 ∧ G.IsClique s}

abbrev FlagChain0 := V →₀ F₂
abbrev FlagChain1 := FlagEdge G →₀ F₂
abbrev FlagChain2 := FlagTriangle G →₀ F₂

/-- The unoriented F₂ boundary of one edge. -/
def edgeBoundary (e : FlagEdge G) : FlagChain0 (V := V) :=
  Sym2.lift
    ⟨fun u v ↦ Finsupp.single u 1 + Finsupp.single v 1,
      fun u v ↦ by dsimp; rw [add_comm]⟩ e.1

/-- The three unordered edges in a triangular clique. -/
noncomputable def triangleBoundary (t : FlagTriangle G) : FlagChain1 G := by
  classical
  let es : Finset (Sym2 V) :=
    t.1.sym2.filter (fun e ↦ e ∈ G.edgeSet)
  exact es.attach.sum fun e ↦
    Finsupp.single ⟨e.1, (mem_filter.mp e.2).2⟩ 1

def flagD1 : FlagChain1 G →ₗ[F₂] FlagChain0 (V := V) :=
  Finsupp.linearCombination F₂ (edgeBoundary G)

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

/-- Actual first simplicial homology of the flag complex over F₂. -/
abbrev FlagH1F2 := FlagCycle G ⧸ FlagBoundarySubmodule G

noncomputable def flagBeta1F2 : ℕ :=
  Module.finrank F₂ (FlagH1F2 G)

def FlagH1F2AtMostTwo : Prop := flagBeta1F2 G ≤ 2
def FlagH1F2ExactlyTwo : Prop := flagBeta1F2 G = 2

/-- The sparse complement family in Equation (1) of the paper. -/
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

/-- A complete bipartite spanning subgraph with two nonempty sides. -/
def HasCompleteBipartiteSpanning {V : Type u_1}
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A : Finset V,
    A.Nonempty ∧ A ≠ univ ∧
      ∀ u ∈ A, ∀ v ∈ univ \ A, G.Adj u v

end

end ExtremalFlagBetti.ActualHomology

namespace PalomarExtremalFlagBetti

open ExtremalFlagBetti.ActualHomology

/-- The concrete family has actual first flag homology of F₂-dimension two. -/
theorem family_actual_flag_h1_exactly_two {n : ℕ} (hn : 7 ≤ n) :
    FlagH1F2ExactlyTwo (FamilyG n) := by
  sorry

/-- Proposition 3.1 over F₂ for every graph at the extremal edge count. -/
theorem universal_flag_beta1_f2_le_two
    {n : ℕ} (hn : 7 ≤ n) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj]
    (hE : #F.edgeFinset = n.choose 2 - n) :
    FlagH1F2AtMostTwo F := by
  sorry

/-- The paper-level dense extremal counterexample bundle, over F₂. -/
theorem dense_extremal_flag_counterexample_f2
    {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n ∧
    n ^ 2 / 4 < #(FamilyG n).edgeFinset ∧
    FlagH1F2ExactlyTwo (FamilyG n) ∧
    (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      #F.edgeFinset = n.choose 2 - n → FlagH1F2AtMostTwo F) ∧
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  sorry

end PalomarExtremalFlagBetti
