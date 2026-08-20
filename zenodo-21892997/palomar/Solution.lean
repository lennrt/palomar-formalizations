/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ExtremalFlagBetti

/-! Proof-bearing wrappers for the declarations in `Challenge.lean`. -/

open Finset
open SimpleGraph

namespace PalomarExtremalFlagBetti

open ExtremalFlagBetti

theorem family_leaf_triangle_certificate {n : ℕ} (hn : 7 ≤ n) :
    let leaf : Fin n := ⟨5, by omega⟩
    let hub : Fin n := ⟨4, by omega⟩
    (∀ v, (FamilyH n).Adj leaf v ↔ v = hub) ∧
      (∀ u, u ≠ hub ∧ ¬(FamilyH n).Adj hub u ↔ u.val < 3) ∧
      (∀ u v, u.val < 3 → v.val < 3 → u ≠ v → (FamilyH n).Adj u v) := by
  exact ExtremalFlagBetti.family_leaf_triangle_certificate hn

theorem family_no_complete_bipartite_spanning {n : ℕ} (hn : 7 ≤ n) :
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  exact ExtremalFlagBetti.family_no_complete_bipartite_spanning hn

theorem family_complement_edge_count {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n := by
  exact ExtremalFlagBetti.family_complement_edge_count hn

end PalomarExtremalFlagBetti

