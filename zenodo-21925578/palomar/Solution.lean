/-
Paper: Exact Spectra of Generalized Cubic Subdivision Matrices
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21925578
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import CubicHalfSpectrum

/-! Proof-bearing wrappers for the declarations in `Challenge.lean`. -/

noncomputable section

namespace PalomarCubicHalfSpectrum

open CubicHalfSpectrum

theorem zero_mode_factorization
    (u q x y z : ℝ) (hu : u ≠ 1) :
    zeroModeChar u q x y z =
      (z - 1) * (z - q ^ 2) * (z - x * y) := by
  exact CubicHalfSpectrum.zero_mode_factorization u q x y z hu

theorem real_root_in_unit_interval
    {T x μ : ℝ}
    (hx : x < 1)
    (hfirst : 0 < 1 - 2 * T + x)
    (hsecond : 0 < 1 + 2 * T + x)
    (hroot : μ ^ 2 - 2 * T * μ + x = 0) :
    -1 < μ ∧ μ < 1 := by
  exact CubicHalfSpectrum.real_root_in_unit_interval hx hfirst hsecond hroot

theorem double_ring_outer_symbol_factorization
    (l omega : ℂ) (homega : omega ≠ 0) :
    l ^ 24 * (l - 1 / 64) *
        det3C
          (l - 1 / 16) (-1 / 16) 0
          (-1 / 64) (l - 3 / 32) (-omega / 64)
          0 (-1 / (16 * omega)) (l - 1 / 16)
      = l ^ 24 * (l - 1 / 64) * (l - 1 / 32) *
          (l - 1 / 16) * (l - 1 / 8) := by
  exact CubicHalfSpectrum.doubleRingOuterSymbol_factorization_complex
    l omega homega

theorem double_ring_line_factorization (z : ℝ) :
    doubleRingLineChar z =
      z ^ 6 * (z - 1) * (z - 1 / 2) * (z - 1 / 4) *
        (z - 1 / 8) ^ 2 := by
  exact CubicHalfSpectrum.double_ring_line_polynomial_reassociation z

end PalomarCubicHalfSpectrum

