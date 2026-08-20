/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Auditable statements for the signed-circulant arithmetic companion

The definitions make the submitted characteristic-polynomial statement
self-contained.  This is the phase-one algebraic bridge, not the paper's full
spectral theorem.
-/

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

/-- The exact characteristic polynomial of the squared phase-one block. -/
theorem phase_one_characteristic_polynomial (t : ℝ) :
    Matrix.det (Matrix.scalar (Fin 4) t - phaseOneSquaredBlockReal) = quartic t := by
  sorry

/-- The quartic has a real root inside the certified rational separator. -/
theorem exists_quartic_root_in_separator :
    ∃ t : ℝ, 39 / 5 < t ∧ t < 1561 / 200 ∧ quartic t = 0 := by
  sorry

/-- The quartic is strictly positive at and above the upper separator. -/
theorem quartic_positive_at_or_above_upper
    {t : ℝ} (ht : 1561 / 200 ≤ t) : 0 < quartic t := by
  sorry

/-- Any root below the certified separator is below the nested-radical target
used in the band-edge comparison. -/
theorem certified_root_below_nested_target
    {t₀ : ℝ} (ht₀ : t₀ < 1561 / 200) :
    t₀ < 4 + Real.sqrt (2 + Real.sqrt 2) +
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
  sorry

end

end PalomarSignedCirculant
