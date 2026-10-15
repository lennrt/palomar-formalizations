module

public import ShellSampling.Geometric
public import Mathlib.Tactic

/-! Arithmetic of the depth-dependent union bound and rational survival design.
No probability-tail inequality is postulated or proved in this file. -/
@[expose] public section

namespace ShellResearch
open Finset

/-- Sum of depth-dependent error bounds; no factor of the path length appears. -/
theorem geometric_tail_budget {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (hbudget : r ≤ δ / (δ + 8)) (n : ℕ) (errors : ℕ → ℝ)
    (herr : ∀ k ∈ range n, errors k ≤ 4 * r ^ (k+1)) :
    ∑ k ∈ range n, errors k ≤ δ / 2 := by
  have hd : 0 < δ + 8 := by linarith
  have hb : r * (δ+8) ≤ δ := (le_div_iff₀ hd).mp hbudget
  have hr1 : r < 1 := by
    have : δ / (δ+8) < 1 := (div_lt_one hd).mpr (by linarith)
    exact lt_of_le_of_lt hbudget this
  have hgeom := geom_sum_mul_neg r n
  have hpow : 0 ≤ r^n := pow_nonneg hr n
  have hs : (∑ k ∈ range n, r^(k+1)) * (1-r) ≤ r := by
    simp_rw [pow_succ]
    rw [← sum_mul]
    nlinarith [mul_nonneg hr hpow]
  have he : (∑ k ∈ range n, errors k) ≤ 4 * ∑ k ∈ range n, r^(k+1) := by
    rw [mul_sum]
    exact sum_le_sum herr
  have hmul := mul_le_mul_of_nonneg_right he (show 0 ≤ 1-r by linarith)
  have hfin : (∑ k ∈ range n, errors k) * (1-r) ≤ (δ/2)*(1-r) := by
    nlinarith
  exact (mul_le_mul_iff_left₀ (show 0 < 1-r by linarith)).mp hfin

end ShellResearch
