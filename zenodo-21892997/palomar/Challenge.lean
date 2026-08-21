/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Authors: Lennart Rudolph, Sol, Fable
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

/-- Boundary squared is zero for the literal edge/triangle boundary maps. -/
theorem flagD1_flagD2 (c : FlagChain2 G) :
    flagD1 G (flagD2 G c) = 0 := by
  sorry

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
