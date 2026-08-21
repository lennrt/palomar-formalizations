/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Arithmetic and monotonicity checks for the signed-circulant counterexample

This file formalizes the rational separators, the nested-radical lower bound,
and the polynomial derivative inequalities used in the infinite-family proof.
It also checks a concrete algebraic bridge at Bloch phase `z = 1`: the displayed
eight-dimensional block exchanges two explicit four-dimensional lattices, and
the characteristic polynomial of the resulting squared block is exactly `Q`.
It deliberately does **not** claim to formalize the 32 by 32 characteristic
polynomial, Sturm's theorem, the full phase-dependent Bloch determinant, the
direct-integral decomposition, or the spectral theorem. Those parts are proved
in the paper; the algebraic certificates are checked by the exact executable
verifiers, while the Fourier and spectral-theorem steps remain manuscript
arguments.

No `sorry` and no `native_decide` are used.
-/

namespace SignedCirculantArithmetic

noncomputable section

def F (t y : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + (80 - 2 * y) * t ^ 2 +
    (-128 + 16 * y) * t + y ^ 2 - 13 * y + 38

def Q (t : ℝ) : ℝ := t ^ 4 - 16 * t ^ 3 + 76 * t ^ 2 - 96 * t + 16

def partialY (t y : ℝ) : ℝ := 2 * y - 2 * t ^ 2 + 16 * t - 13

def partialT (t y : ℝ) : ℝ :=
  4 * t ^ 3 - 48 * t ^ 2 + 2 * (80 - 2 * y) * t - 128 + 16 * y

example (t : ℝ) : F t 2 = Q t := by
  simp [F, Q]
  ring

example (t : ℝ) : partialT t 2 = 4 * (t - 4) * (t ^ 2 - 8 * t + 6) := by
  simp [partialT]
  ring

theorem q_at_lower : Q (39 / 5 : ℝ) = -179 / 625 := by
  norm_num [Q]

theorem q_at_upper : Q (1561 / 200 : ℝ) = 84332641 / 1600000000 := by
  norm_num [Q]

theorem finite_separator_squared_lt_aux : (1397 / 500 : ℝ) ^ 2 < 976 / 125 := by
  norm_num

theorem bloch_separator_lt_aux : (1561 / 200 : ℝ) < 976 / 125 := by
  norm_num

/-! ## The exact phase-one Bloch bridge

The columns of `plusBasis` and `minusBasis` are the vectors
`e_j + (-1)^j e_(j+4)` and `e_j - (-1)^j e_(j+4)`, respectively.  The
phase-one Bloch matrix exchanges their spans.  Squaring therefore reduces its
eigenvalue equation on either span to the four-dimensional block below.
-/

def blochOne : Matrix (Fin 8) (Fin 8) ℤ :=
  !![0,  1, 1,  0,  0,  0, -1, 1;
     1,  0, 1, -1,  0,  0,  0, 1;
     1,  1, 0,  1,  1,  0,  0, 0;
     0, -1, 1,  0,  1, -1,  0, 0;
     0,  0, 1,  1,  0,  1, -1, 0;
     0,  0, 0, -1,  1,  0,  1, 1;
    -1,  0, 0,  0, -1,  1,  0, 1;
     1,  1, 0,  0,  0,  1,  1, 0]

def plusBasis : Matrix (Fin 8) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
     1, 0, 0, 0;
     0,-1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0,-1]

def minusBasis : Matrix (Fin 8) (Fin 4) ℤ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1;
    -1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0,-1, 0;
     0, 0, 0, 1]

def headProjection : Matrix (Fin 4) (Fin 8) ℤ :=
  !![1, 0, 0, 0, 0, 0, 0, 0;
     0, 1, 0, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0, 0, 0]

def plusToMinus : Matrix (Fin 4) (Fin 4) ℤ :=
  !![0, 1, 0,-1;
     1, 0, 1,-2;
     2, 1, 0, 1;
     1, 0, 1, 0]

def minusToPlus : Matrix (Fin 4) (Fin 4) ℤ :=
  !![ 0, 1, 2, 1;
      1, 0, 1, 0;
      0, 1, 0, 1;
     -1,-2, 1, 0]

def phaseOneSquaredBlock : Matrix (Fin 4) (Fin 4) ℤ :=
  !![6, 2, 2, 0;
     2, 2, 0, 0;
     2, 0, 2,-2;
     0, 0,-2, 6]

def phaseOneSquaredBlockReal : Matrix (Fin 4) (Fin 4) ℝ :=
  phaseOneSquaredBlock.map (Int.castRingHom ℝ)

theorem blochOne_maps_plus :
    blochOne * plusBasis = minusBasis * plusToMinus := by
  decide

theorem plusBasis_has_left_inverse : headProjection * plusBasis = 1 := by
  decide

theorem minusBasis_has_left_inverse : headProjection * minusBasis = 1 := by
  decide

theorem blochOne_maps_minus :
    blochOne * minusBasis = plusBasis * minusToPlus := by
  decide

theorem phaseOneSquaredBlock_eq :
    minusToPlus * plusToMinus = phaseOneSquaredBlock := by
  decide

theorem blochOne_sq_reduction :
    blochOne ^ 2 * plusBasis = plusBasis * phaseOneSquaredBlock := by
  calc
    blochOne ^ 2 * plusBasis = blochOne * (blochOne * plusBasis) := by
      simp [pow_two, Matrix.mul_assoc]
    _ = blochOne * (minusBasis * plusToMinus) := by rw [blochOne_maps_plus]
    _ = (blochOne * minusBasis) * plusToMinus := by rw [Matrix.mul_assoc]
    _ = (plusBasis * minusToPlus) * plusToMinus := by rw [blochOne_maps_minus]
    _ = plusBasis * (minusToPlus * plusToMinus) := by rw [Matrix.mul_assoc]
    _ = plusBasis * phaseOneSquaredBlock := by rw [phaseOneSquaredBlock_eq]

set_option maxHeartbeats 2000000 in
theorem phaseOneSquaredBlock_det (t : ℝ) :
    Matrix.det (Matrix.scalar (Fin 4) t - phaseOneSquaredBlockReal) = Q t := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Fin.succAbove, phaseOneSquaredBlockReal, phaseOneSquaredBlock,
    Matrix.det_fin_three, Q]
  ring

lemma sqrt_two_lower : (1414 / 1000 : ℝ) < Real.sqrt 2 := by
  have hsqrt : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hrational : (1414 / 1000 : ℝ) ^ 2 < 2 := by norm_num
  nlinarith

lemma first_nested_lower :
    (1847 / 1000 : ℝ) < Real.sqrt (2 + Real.sqrt 2) := by
  have hradicand : 0 ≤ 2 + Real.sqrt (2 : ℝ) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (2 + Real.sqrt (2 : ℝ)) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (2 + Real.sqrt (2 : ℝ))) ^ 2 =
      2 + Real.sqrt 2 := Real.sq_sqrt hradicand
  have hrational : (1847 / 1000 : ℝ) ^ 2 < 2 + 1414 / 1000 := by norm_num
  nlinarith [sqrt_two_lower]

lemma second_nested_lower :
    (1961 / 1000 : ℝ) < Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
  have hradicand : 0 ≤ 2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)) := by positivity
  have hsqrt : 0 ≤ Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ))) :=
    Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (2 + Real.sqrt (2 + Real.sqrt (2 : ℝ)))) ^ 2 =
      2 + Real.sqrt (2 + Real.sqrt 2) := Real.sq_sqrt hradicand
  have hrational : (1961 / 1000 : ℝ) ^ 2 < 2 + 1847 / 1000 := by norm_num
  nlinarith [first_nested_lower]

theorem target_squared_lower :
    (976 / 125 : ℝ) <
      4 + Real.sqrt (2 + Real.sqrt 2) +
        Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
  nlinarith [first_nested_lower, second_nested_lower]

theorem certified_bloch_root_below_target_squared
    {t₀ : ℝ} (ht₀ : t₀ < 1561 / 200) :
    t₀ < 4 + Real.sqrt (2 + Real.sqrt 2) +
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
  exact lt_trans ht₀ (lt_trans bloch_separator_lt_aux target_squared_lower)

/-- A narrowly tailored exact root-exclusion certificate for the exceptional
quartic.  Above the upper separator, expand around `1561 / 200`; every
nonconstant Taylor coefficient and the constant term are strictly positive.
Thus `Q` has no real root at or above the separator. -/
theorem q_pos_at_or_above_upper
    {t : ℝ} (ht : 1561 / 200 ≤ t) : 0 < Q t := by
  let u : ℝ := t - 1561 / 200
  have hu : 0 ≤ u := by dsimp [u]; linarith
  have hc1 :
      0 < 4 * (1561 / 200 : ℝ) ^ 3 - 48 * (1561 / 200 : ℝ) ^ 2 +
        152 * (1561 / 200 : ℝ) - 96 := by norm_num
  have hc2 :
      0 < 6 * (1561 / 200 : ℝ) ^ 2 - 48 * (1561 / 200 : ℝ) + 76 := by
    norm_num
  have hc3 : 0 < 4 * (1561 / 200 : ℝ) - 16 := by norm_num
  have hdecomp :
      Q t = Q (1561 / 200) +
        (4 * (1561 / 200 : ℝ) ^ 3 - 48 * (1561 / 200 : ℝ) ^ 2 +
          152 * (1561 / 200 : ℝ) - 96) * u +
        (6 * (1561 / 200 : ℝ) ^ 2 - 48 * (1561 / 200 : ℝ) + 76) * u ^ 2 +
        (4 * (1561 / 200 : ℝ) - 16) * u ^ 3 + u ^ 4 := by
    dsimp [u, Q]
    ring
  rw [hdecomp, q_at_upper]
  positivity

theorem exists_q_root_in_separator :
    ∃ t : ℝ, 39 / 5 < t ∧ t < 1561 / 200 ∧ Q t = 0 := by
  have hbounds : (39 / 5 : ℝ) ≤ 1561 / 200 := by norm_num
  have hzero : (0 : ℝ) ∈ Set.Icc (Q (39 / 5)) (Q (1561 / 200)) := by
    rw [q_at_lower, q_at_upper]
    constructor <;> norm_num
  have hcontinuous : Continuous Q := by
    unfold Q
    fun_prop
  rcases intermediate_value_Icc hbounds hcontinuous.continuousOn hzero with
    ⟨t, ht, hQt⟩
  refine ⟨t, ?_, ?_, ?_⟩
  · by_contra h
    have hle : t ≤ 39 / 5 := le_of_not_gt h
    have : t = 39 / 5 := le_antisymm hle ht.1
    subst t
    rw [q_at_lower] at hQt
    norm_num at hQt
  · by_contra h
    have hle : 1561 / 200 ≤ t := le_of_not_gt h
    have hpos := q_pos_at_or_above_upper hle
    rw [hQt] at hpos
    exact (lt_irrefl 0 hpos)
  · exact hQt

theorem partialY_neg
    {t y : ℝ} (ht : 39 / 5 ≤ t) (hy : y ≤ 2) : partialY t y < 0 := by
  have hsum : 0 ≤ t + 39 / 5 - 8 := by nlinarith
  have hproduct : 0 ≤ (t - 39 / 5) * (t + 39 / 5 - 8) :=
    mul_nonneg (sub_nonneg.mpr ht) hsum
  have hbase : -2 * (39 / 5 : ℝ) ^ 2 + 16 * (39 / 5 : ℝ) - 9 = -147 / 25 := by
    norm_num
  dsimp [partialY]
  nlinarith

theorem partialT_pos
    {t y : ℝ} (ht : 39 / 5 ≤ t) (hy : y ≤ 2) : 0 < partialT t y := by
  have ht4 : 4 < t := by nlinarith
  have hsum : 0 ≤ t + 39 / 5 - 8 := by nlinarith
  have hproduct : 0 ≤ (t - 39 / 5) * (t + 39 / 5 - 8) :=
    mul_nonneg (sub_nonneg.mpr ht) hsum
  have hquadratic_base :
      (39 / 5 : ℝ) ^ 2 - 8 * (39 / 5 : ℝ) + 6 = 111 / 25 := by
    norm_num
  have hquadratic : 0 < t ^ 2 - 8 * t + 6 := by
    nlinarith
  have hfour : (0 : ℝ) < 4 := by norm_num
  have hfactor : 0 < 4 * (t - 4) * (t ^ 2 - 8 * t + 6) :=
    mul_pos (mul_pos hfour (sub_pos.mpr ht4)) hquadratic
  have hcoefficient : 16 - 4 * t ≤ 0 := by nlinarith
  have hyshift : y - 2 ≤ 0 := by nlinarith
  have hcorrection : 0 ≤ (16 - 4 * t) * (y - 2) :=
    mul_nonneg_of_nonpos_of_nonpos hcoefficient hyshift
  calc
    0 < 4 * (t - 4) * (t ^ 2 - 8 * t + 6) +
        (16 - 4 * t) * (y - 2) := by nlinarith
    _ = partialT t y := by
      simp [partialT]
      ring

#print axioms target_squared_lower
#print axioms q_at_lower
#print axioms q_at_upper
#print axioms blochOne_maps_plus
#print axioms blochOne_maps_minus
#print axioms plusBasis_has_left_inverse
#print axioms minusBasis_has_left_inverse
#print axioms blochOne_sq_reduction
#print axioms phaseOneSquaredBlock_det
#print axioms certified_bloch_root_below_target_squared
#print axioms q_pos_at_or_above_upper
#print axioms exists_q_root_in_separator
#print axioms partialY_neg
#print axioms partialT_pos

end

end SignedCirculantArithmetic
