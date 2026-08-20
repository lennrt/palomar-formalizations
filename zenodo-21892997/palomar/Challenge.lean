/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega

/-!
# Auditable graph core for the extremal flag-Betti counterexample family

This Challenge states only the all-order graph results proved without native
evaluation. It does not state a homology computation or the paper's full
extremal first-Betti theorem.
-/

open Finset
open SimpleGraph

namespace ExtremalFlagBetti

/-- The sparse complement family: a triangle, a two-edge attached path, and leaves. -/
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
  loopless := ⟨by
    intro u
    omega⟩

instance (n : ℕ) : DecidableRel (FamilyH n).Adj := by
  unfold FamilyH
  infer_instance

/-- Direct finite formulation of a complete bipartite spanning subgraph. -/
def HasCompleteBipartiteSpanning {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A : Finset V,
    A.Nonempty ∧ A ≠ univ ∧ ∀ u ∈ A, ∀ v ∈ univ \ A, G.Adj u v

/-- The dense family is the graph complement of `FamilyH`. -/
def FamilyG (n : ℕ) : SimpleGraph (Fin n) := (FamilyH n)ᶜ

instance (n : ℕ) : DecidableRel (FamilyG n).Adj := by
  unfold FamilyG
  infer_instance

end ExtremalFlagBetti

namespace PalomarExtremalFlagBetti

open ExtremalFlagBetti

/-- Uniform leaf certificate whose remainder on vertices `0,1,2` is a triangle. -/
theorem family_leaf_triangle_certificate {n : ℕ} (hn : 7 ≤ n) :
    let leaf : Fin n := ⟨5, by omega⟩
    let hub : Fin n := ⟨4, by omega⟩
    (∀ v, (FamilyH n).Adj leaf v ↔ v = hub) ∧
      (∀ u, u ≠ hub ∧ ¬(FamilyH n).Adj hub u ↔ u.val < 3) ∧
      (∀ u v, u.val < 3 → v.val < 3 → u ≠ v → (FamilyH n).Adj u v) := by
  sorry

/-- Every graph in the dense family lacks a complete bipartite spanning subgraph. -/
theorem family_no_complete_bipartite_spanning {n : ℕ} (hn : 7 ≤ n) :
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  sorry

/-- The dense family has exactly `choose(n,2) - n` edges. -/
theorem family_complement_edge_count {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n := by
  sorry

end PalomarExtremalFlagBetti
