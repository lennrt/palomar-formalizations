module

public import ShellSampling.LowerBound
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! Geometric inequalities used to sum depth-dependent concentration errors. -/
@[expose] public section

namespace ShellSampling
open Finset

/-- For a decreasing geometric sequence, its average over a shorter prefix is larger. -/
theorem geometric_failure_ratio {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {k n : ℕ} (hkn : k ≤ n) :
    (k:ℝ) * (1-p^n) ≤ (n:ℝ) * (1-p^k) := by
  induction n, hkn using Nat.le_induction with
  | base => exact le_rfl
  | succ n hkn ih =>
    have hs : (k:ℝ) * p^n ≤ ∑ i ∈ range k, p^i := by
      calc (k:ℝ) * p^n = ∑ _i ∈ range k, p^n := by simp
           _ ≤ ∑ i ∈ range k, p^i := by
             apply sum_le_sum
             intro i hi
             exact pow_le_pow_of_le_one hp0 hp1
               (le_trans (Nat.le_of_lt (mem_range.mp hi)) hkn)
    have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hp1)
    rw [geom_sum_mul_neg] at hm
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    nlinarith

/-- A convenient constant valid on the whole designed-survival window. -/
theorem square_times_failure_ge_eighth {t : ℝ}
    (ht0 : (1:ℝ)/2 ≤ t) (ht1 : t ≤ (2:ℝ)/3) :
    (1:ℝ)/8 ≤ t^2*(1-t) := by
  have ht : 0 ≤ t := by linarith
  have hquadratic := mul_nonneg ht (show 0 ≤ (2:ℝ)/3-t by linarith)
  have hfactor : 0 ≤ -4*t^2+2*t+1 := by nlinarith
  have h := mul_nonneg (show 0 ≤ 2*t-1 by linarith) hfactor
  nlinarith

/-- The rational rate places the all-survive probability in a fixed compact interval. -/
theorem designed_power_window (n : ℕ) (hn : 0 < n) :
    (1:ℝ)/2 ≤ (designedRate n)^n ∧ (designedRate n)^n ≤ (2:ℝ)/3 := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnR
  have hden : (0:ℝ) < 2*(n:ℝ)+1 := by positivity
  have hdenne : 2*(n:ℝ)+1 ≠ 0 := ne_of_gt hden
  let p := designedRate n
  have hp : 0 < p := by dsimp [p, designedRate]; positivity
  have hpow : 0 < p^n := pow_pos hp n
  have hlo := one_add_mul_sub_le_pow (show -1 ≤ p by linarith) n
  have hloeval : (1:ℝ)/2 ≤ 1+(n:ℝ)*(p-1) := by
    dsimp [p, designedRate]
    apply (le_of_mul_le_mul_right ?_ hden)
    field_simp
    nlinarith
  have hhi := one_add_mul_sub_le_pow (show -1 ≤ p⁻¹ by have := inv_pos.mpr hp; linarith) n
  have hhieval : 1+(n:ℝ)*(p⁻¹-1) = (3:ℝ)/2 := by
    dsimp [p, designedRate]
    rw [inv_div]
    field_simp
    ring
  rw [hhieval] at hhi
  have hmul := mul_le_mul_of_nonneg_right hhi hpow.le
  rw [inv_pow, inv_mul_cancel₀ (ne_of_gt hpow)] at hmul
  constructor
  · exact le_trans hloeval hlo
  · change p^n ≤ (2:ℝ)/3
    nlinarith

/-- In particular the concentration design factor never exceeds eight. -/
theorem designed_power_factor (n : ℕ) (hn : 0 < n) :
    (1:ℝ)/8 ≤ (designedRate n)^(2*n)*(1-(designedRate n)^n) := by
  obtain ⟨hlo, hhi⟩ := designed_power_window n hn
  have h := square_times_failure_ge_eighth hlo hhi
  simpa only [← pow_mul, Nat.mul_comm n 2] using h

end ShellSampling
