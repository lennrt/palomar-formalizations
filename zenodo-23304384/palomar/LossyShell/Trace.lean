module

public import LossyShell.Landing
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The endpoint sensor reads the deletion trace

For a sensor at the end of a path, entry `k` of the lossy report is entry `k` of the
deletion-channel trace of the population (with `0` past the end of the trace), and the trace
is the first `aliveCount ω` entries of the report. So a report together with the horizon
`aliveCount ω` is the same datum as a complete deletion trace.
-/

@[expose] public section

namespace LossyShell

open Finset

lemma aliveRank_eq_sum {n : ℕ} (ω : Pattern n) (i : Fin n) :
    aliveRank ω i = ∑ j, if j ≤ i ∧ ω j = true then 1 else 0 := by
  unfold aliveRank
  rw [card_filter]

lemma aliveRank_cons_zero {n : ℕ} (b : Bool) (ω : Pattern n) :
    aliveRank (Fin.cons b ω : Pattern (n + 1)) 0 = if b = true then 1 else 0 := by
  rw [aliveRank_eq_sum, Fin.sum_univ_succ]
  simp [Fin.succ_ne_zero]

lemma aliveRank_cons_succ {n : ℕ} (b : Bool) (ω : Pattern n) (i : Fin n) :
    aliveRank (Fin.cons b ω : Pattern (n + 1)) i.succ =
      (if b = true then 1 else 0) + aliveRank ω i := by
  rw [aliveRank_eq_sum, Fin.sum_univ_succ, aliveRank_eq_sum]
  simp [Fin.succ_le_succ_iff]

lemma legReport_cons {n : ℕ} (x0 : ℕ) (x : Population n) (b : Bool) (ω : Pattern n) (k : ℕ) :
    legReport (Fin.cons x0 x : Population (n + 1)) (Fin.cons b ω) k =
      (if b = true ∧ k = 0 then x0 else 0) +
        ∑ i, if ω i = true ∧ (if b = true then 1 else 0) + aliveRank ω i = k + 1 then x i
          else 0 := by
  unfold legReport
  rw [Fin.sum_univ_succ]
  congr 1
  · rw [aliveRank_cons_zero]
    cases b <;> by_cases hk : k = 0 <;> simp [hk]
  · apply sum_congr rfl
    intro i _
    rw [aliveRank_cons_succ]
    simp

lemma trace_cons {n : ℕ} (x0 : ℕ) (x : Population n) (b : Bool) (ω : Pattern n) :
    trace (Fin.cons x0 x : Population (n + 1)) (Fin.cons b ω) =
      (if b = true then [x0] else []) ++ trace x ω := by
  unfold trace
  rw [List.finRange_succ]
  cases b <;> simp [List.filter_map, Function.comp_def]

lemma aliveCount_cons {n : ℕ} (b : Bool) (ω : Pattern n) :
    aliveCount (Fin.cons b ω : Pattern (n + 1)) = (if b = true then 1 else 0) + aliveCount ω := by
  unfold aliveCount
  rw [card_filter, card_filter, Fin.sum_univ_succ]
  simp

/-- The endpoint sensor's report is the deletion trace, read entry by entry. -/
theorem legReport_eq_trace_getD {n : ℕ} (x : Population n) (ω : Pattern n) (k : ℕ) :
    legReport x ω k = (trace x ω).getD k 0 := by
  induction n generalizing k with
  | zero =>
    simp [legReport, trace]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail ω, legReport_cons, trace_cons]
    cases hb : ω 0 with
    | false =>
      simp only [Bool.false_eq_true, false_and, ite_eq_right, not_false_eq_true, zero_add,
        List.nil_append]
      rw [← ih]
      rfl
    | true =>
      simp only [ite_true, true_and, List.singleton_append]
      cases k with
      | zero =>
        simp only [ite_true, List.getD_cons_zero]
        simp
        intro i hi hr
        have := aliveRank_pos hi
        omega
      | succ k =>
        simp only [Nat.add_one_ne_zero, ite_false, zero_add, List.getD_cons_succ]
        rw [← ih]
        unfold legReport
        apply sum_congr rfl
        intro i _
        refine if_congr ?_ rfl rfl
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

lemma trace_length {n : ℕ} (x : Population n) (ω : Pattern n) :
    (trace x ω).length = aliveCount ω := by
  induction n with
  | zero => simp [trace, aliveCount]
  | succ n ih =>
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail ω, trace_cons, aliveCount_cons]
    cases ω 0 <;> simp [ih, Nat.add_comm]

/-- The trace is the first `aliveCount ω` entries of the endpoint report. -/
theorem trace_eq_map_legReport {n : ℕ} (x : Population n) (ω : Pattern n) :
    trace x ω = (List.range (aliveCount ω)).map (legReport x ω) := by
  apply List.ext_getElem
  · simp [trace_length]
  · intro k h1 h2
    rw [List.getElem_map, List.getElem_range, legReport_eq_trace_getD, List.getElem_eq_getD 0]

end LossyShell
