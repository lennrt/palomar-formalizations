/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ArithmeticAndMonotonicity
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

open Set

namespace PalomarSignedCirculant

noncomputable section

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def bandPolynomial (t y : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + (80 - 2 * y) * t ^ 2 +
    (-128 + 16 * y) * t + y ^ 2 - 13 * y + 38

def bandQuartic (t : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + 76 * t ^ 2 - 96 * t + 16

def blochSymbol {R : Type*} [CommRing R] (z zInv : R) :
    Matrix (Fin 8) (Fin 8) R :=
  !![0,  1, 1,  0,  0,  0, -zInv, zInv;
     1,  0, 1, -1,  0,  0,  0,     zInv;
     1,  1, 0,  1,  1,  0,  0,     0;
     0, -1, 1,  0,  1, -1,  0,     0;
     0,  0, 1,  1,  0,  1, -1,     0;
     0,  0, 0, -1,  1,  0,  1,     1;
    -z,  0, 0,  0, -1,  1,  0,     1;
     z,  z, 0,  0,  0,  1,  1,     0]

def bandPolynomialRing {R : Type*} [CommRing R] (t y : R) : R :=
  t ^ 4 - 16 * t ^ 3 + (80 - 2 * y) * t ^ 2 +
    (-128 + 16 * y) * t + y ^ 2 - 13 * y + 38

def determinantCorrection {R : Type*} [CommRing R] (x z zInv : R) : R :=
  -3 * x ^ 6 + x ^ 4 * z * zInv + 28 * x ^ 4 - 4 * x ^ 3 -
    5 * x ^ 2 * z * zInv + 3 * x ^ 2 * z + 3 * x ^ 2 * zInv -
    59 * x ^ 2 - 2 * x * z - 2 * x * zInv + 12 * x +
    4 * z * zInv - 4 * z - 4 * zInv + 17

theorem bloch_symbol_phase_reversal {R : Type*} [CommRing R] (z zInv : R) :
    (blochSymbol z zInv).transpose = blochSymbol zInv z := by
  ext r s
  fin_cases r <;> fin_cases s <;> simp [blochSymbol]

theorem bloch_determinant_with_correction {R : Type*} [CommRing R]
    (x z zInv : R) :
    Matrix.det (Matrix.scalar (Fin 8) x - blochSymbol z zInv) =
      bandPolynomialRing (x ^ 2) (z + zInv) +
        (z * zInv - 1) * determinantCorrection x z zInv := by
  rw [Matrix.det_succ_row_zero]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
    blochSymbol, bandPolynomialRing, determinantCorrection]
  ring

theorem bloch_determinant_identity {R : Type*} [CommRing R]
    (x z zInv : R) (hz : z * zInv = 1) :
    Matrix.det (Matrix.scalar (Fin 8) x - blochSymbol z zInv) =
      bandPolynomialRing (x ^ 2) (z + zInv) := by
  rw [bloch_determinant_with_correction, hz]
  ring

private lemma bandQuartic_eq_source (t : ℝ) :
    bandQuartic t = SignedCirculantArithmetic.Q t := by
  simp [bandQuartic, SignedCirculantArithmetic.Q]

private lemma bandPolynomial_phase_one (t : ℝ) :
    bandPolynomial t 2 = bandQuartic t := by
  simp [bandPolynomial, bandQuartic]
  ring

private def bandPolynomialInT (y : ℝ) : Polynomial ℝ :=
  Polynomial.X ^ 4 - Polynomial.C 16 * Polynomial.X ^ 3 +
    Polynomial.C (80 - 2 * y) * Polynomial.X ^ 2 +
    Polynomial.C (-128 + 16 * y) * Polynomial.X +
    Polynomial.C (y ^ 2 - 13 * y + 38)

private lemma bandPolynomialInT_eval (t y : ℝ) :
    (bandPolynomialInT y).eval t = bandPolynomial t y := by
  simp [bandPolynomialInT, bandPolynomial]
  ring

private lemma bandPolynomialInT_derivative_eval (t y : ℝ) :
    (bandPolynomialInT y).derivative.eval t =
      SignedCirculantArithmetic.partialT t y := by
  simp only [bandPolynomialInT, map_add, map_sub, map_mul, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_pow, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_pow, Nat.cast_ofNat]
  simp [SignedCirculantArithmetic.partialT]
  ring

private lemma bandPolynomial_hasDerivAt (t y : ℝ) :
    HasDerivAt (fun u => bandPolynomial u y)
      (SignedCirculantArithmetic.partialT t y) t := by
  simpa only [bandPolynomialInT_eval, bandPolynomialInT_derivative_eval] using
    (bandPolynomialInT y).hasDerivAt t

private theorem bandPolynomial_strictMonoOn (y : ℝ) (hy : y ≤ 2) :
    StrictMonoOn (fun t => bandPolynomial t y) (Ici (39 / 5)) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos
    (f' := fun t => SignedCirculantArithmetic.partialT t y) (convex_Ici _) ?_ ?_ ?_
  · intro t _
    exact (bandPolynomial_hasDerivAt t y).continuousAt.continuousWithinAt
  · intro t _
    exact (bandPolynomial_hasDerivAt t y).hasDerivWithinAt
  · intro t ht
    have ht' : (39 / 5 : ℝ) ≤ t := by
      rw [interior_Ici] at ht
      exact le_of_lt ht
    exact SignedCirculantArithmetic.partialT_pos ht' hy

private theorem bandPolynomial_at_root_nonneg
    {t₀ y : ℝ} (ht₀ : 39 / 5 ≤ t₀) (hroot : bandQuartic t₀ = 0)
    (hy : y ≤ 2) : 0 ≤ bandPolynomial t₀ y := by
  have hderiv := SignedCirculantArithmetic.partialY_neg ht₀
    (show (2 : ℝ) ≤ 2 by norm_num)
  have hcoefficient : y - 2 * t₀ ^ 2 + 16 * t₀ - 11 < 0 := by
    dsimp [SignedCirculantArithmetic.partialY] at hderiv
    nlinarith
  have hfactor :
      bandPolynomial t₀ y - bandPolynomial t₀ 2 =
        (y - 2) * (y - 2 * t₀ ^ 2 + 16 * t₀ - 11) := by
    simp [bandPolynomial]
    ring
  have hdiff : 0 ≤ bandPolynomial t₀ y - bandPolynomial t₀ 2 := by
    rw [hfactor]
    exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hy) hcoefficient.le
  rw [bandPolynomial_phase_one, hroot] at hdiff
  linarith

private theorem bandPolynomial_at_root_pos_of_phase_lt_two
    {t₀ y : ℝ} (ht₀ : 39 / 5 ≤ t₀) (hroot : bandQuartic t₀ = 0)
    (hy : y < 2) : 0 < bandPolynomial t₀ y := by
  have hderiv := SignedCirculantArithmetic.partialY_neg ht₀
    (show (2 : ℝ) ≤ 2 by norm_num)
  have hcoefficient : y - 2 * t₀ ^ 2 + 16 * t₀ - 11 < 0 := by
    dsimp [SignedCirculantArithmetic.partialY] at hderiv
    nlinarith
  have hfactor :
      bandPolynomial t₀ y - bandPolynomial t₀ 2 =
        (y - 2) * (y - 2 * t₀ ^ 2 + 16 * t₀ - 11) := by
    simp [bandPolynomial]
    ring
  have hdiff : 0 < bandPolynomial t₀ y - bandPolynomial t₀ 2 := by
    rw [hfactor]
    exact mul_pos_of_neg_of_neg (sub_neg.mpr hy) hcoefficient
  rw [bandPolynomial_phase_one, hroot] at hdiff
  linarith

private theorem bandPolynomial_pos_above_root
    {t₀ t y : ℝ} (ht₀ : 39 / 5 ≤ t₀) (hroot : bandQuartic t₀ = 0)
    (htt₀ : t₀ < t) (hy : y ≤ 2) : 0 < bandPolynomial t y := by
  have hroot_nonneg := bandPolynomial_at_root_nonneg ht₀ hroot hy
  have ht : t ∈ Ici (39 / 5 : ℝ) := by
    exact mem_Ici.mpr (le_trans ht₀ (le_of_lt htt₀))
  have hmono := bandPolynomial_strictMonoOn y hy
    (mem_Ici.mpr ht₀) ht htt₀
  exact lt_of_le_of_lt hroot_nonneg hmono

theorem algebraic_band_edge_certificate :
    ∃ t₀ : ℝ,
      39 / 5 < t₀ ∧
      t₀ < 1561 / 200 ∧
      bandQuartic t₀ = 0 ∧
      t₀ < 4 + Real.sqrt (2 + Real.sqrt 2) +
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) ∧
      (∀ y, -2 ≤ y → y ≤ 2 → 0 ≤ bandPolynomial t₀ y) ∧
      (∀ y, -2 ≤ y → y < 2 → 0 < bandPolynomial t₀ y) ∧
      (∀ t y, -2 ≤ y → y ≤ 2 → bandPolynomial t y = 0 → t ≤ t₀) := by
  obtain ⟨t₀, ht₀lower, ht₀upper, hroot⟩ :=
    SignedCirculantArithmetic.exists_q_root_in_separator
  have hroot' : bandQuartic t₀ = 0 := by
    simpa [bandQuartic_eq_source] using hroot
  refine ⟨t₀, ht₀lower, ht₀upper, hroot', ?_, ?_, ?_, ?_⟩
  · exact SignedCirculantArithmetic.certified_bloch_root_below_target_squared ht₀upper
  · intro y _ hy
    exact bandPolynomial_at_root_nonneg (le_of_lt ht₀lower) hroot' hy
  · intro y _ hy
    exact bandPolynomial_at_root_pos_of_phase_lt_two (le_of_lt ht₀lower) hroot' hy
  · intro t y _ hy hzero
    by_contra hle
    have hpos := bandPolynomial_pos_above_root (le_of_lt ht₀lower) hroot'
      (lt_of_not_ge hle) hy
    rw [hzero] at hpos
    exact (lt_irrefl 0 hpos)

end

#print axioms bloch_symbol_phase_reversal
#print axioms bloch_determinant_with_correction
#print axioms bloch_determinant_identity
#print axioms algebraic_band_edge_certificate

end PalomarSignedCirculant
