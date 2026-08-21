/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar F₂ flag-homology upgrade: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ExtremalFlagBetti.ActualHomology

/-! The imported implementation exposes the selected `d₁ ∘ d₂ = 0`
chain identity. The wrappers below expose the three paper-level results. -/

open Finset SimpleGraph

namespace PalomarExtremalFlagBetti

open ExtremalFlagBetti.ActualHomology

theorem family_actual_flag_h1_exactly_two {n : ℕ} (hn : 7 ≤ n) :
    FlagH1F2ExactlyTwo (FamilyG n) := by
  exact ExtremalFlagBetti.ActualHomology.family_actual_flag_h1_exactly_two hn

theorem universal_flag_beta1_f2_le_two
    {n : ℕ} (hn : 7 ≤ n) (F : SimpleGraph (Fin n))
    [DecidableRel F.Adj]
    (hE : #F.edgeFinset = n.choose 2 - n) :
    FlagH1F2AtMostTwo F := by
  exact ExtremalFlagBetti.ActualHomology.universal_flag_beta1_f2_le_two hn F hE

theorem dense_extremal_flag_counterexample_f2
    {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n ∧
    n ^ 2 / 4 < #(FamilyG n).edgeFinset ∧
    FlagH1F2ExactlyTwo (FamilyG n) ∧
    (∀ (F : SimpleGraph (Fin n)) [DecidableRel F.Adj],
      #F.edgeFinset = n.choose 2 - n → FlagH1F2AtMostTwo F) ∧
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  exact ExtremalFlagBetti.ActualHomology.dense_extremal_flag_counterexample_f2 hn

#print axioms ExtremalFlagBetti.ActualHomology.flagD1_flagD2
#print axioms family_actual_flag_h1_exactly_two
#print axioms universal_flag_beta1_f2_le_two
#print axioms dense_extremal_flag_counterexample_f2

end PalomarExtremalFlagBetti
