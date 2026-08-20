/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ArithmeticAndMonotonicity

namespace PalomarSignedCirculant

noncomputable section

def quartic (t : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + 76 * t ^ 2 - 96 * t + 16

def phaseOneSquaredBlock : Matrix (Fin 4) (Fin 4) ℤ :=
  !![6, 2, 2, 0;
     2, 2, 0, 0;
     2, 0, 2, -2;
     0, 0, -2, 6]

def phaseOneSquaredBlockReal : Matrix (Fin 4) (Fin 4) ℝ :=
  phaseOneSquaredBlock.map (Int.castRingHom ℝ)

theorem phase_one_characteristic_polynomial (t : ℝ) :
    Matrix.det (Matrix.scalar (Fin 4) t - phaseOneSquaredBlockReal) = quartic t := by
  simpa [phaseOneSquaredBlockReal, phaseOneSquaredBlock,
    SignedCirculantArithmetic.phaseOneSquaredBlockReal,
    SignedCirculantArithmetic.phaseOneSquaredBlock, quartic,
    SignedCirculantArithmetic.Q] using
    SignedCirculantArithmetic.phaseOneSquaredBlock_det t

theorem exists_quartic_root_in_separator :
    ∃ t : ℝ, 39 / 5 < t ∧ t < 1561 / 200 ∧ quartic t = 0 := by
  simpa [quartic, SignedCirculantArithmetic.Q] using
    SignedCirculantArithmetic.exists_q_root_in_separator

theorem quartic_positive_at_or_above_upper
    {t : ℝ} (ht : 1561 / 200 ≤ t) : 0 < quartic t := by
  simpa [quartic, SignedCirculantArithmetic.Q] using
    SignedCirculantArithmetic.q_pos_at_or_above_upper ht

theorem certified_root_below_nested_target
    {t₀ : ℝ} (ht₀ : t₀ < 1561 / 200) :
    t₀ < 4 + Real.sqrt (2 + Real.sqrt 2) +
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
  exact SignedCirculantArithmetic.certified_bloch_root_below_target_squared ht₀

end

#print axioms phase_one_characteristic_polynomial
#print axioms exists_quartic_root_in_separator
#print axioms quartic_positive_at_or_above_upper
#print axioms certified_root_below_nested_target

end PalomarSignedCirculant
