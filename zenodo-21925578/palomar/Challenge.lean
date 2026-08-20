/-
Paper: Exact Spectra of Generalized Cubic Subdivision Matrices
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21925578
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic

/-!
# Auditable scalar certificates for generalized-cubic subdivision matrices

These are the exact algebraic statements proved by the Lean companion. They
support, but do not themselves state, the preprint's complete spectral result.
-/

noncomputable section

namespace CubicHalfSpectrum

def det3
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : ℝ) : ℝ :=
  a₀₀ * (a₁₁ * a₂₂ - a₁₂ * a₂₁)
    - a₀₁ * (a₁₀ * a₂₂ - a₁₂ * a₂₀)
    + a₀₂ * (a₁₀ * a₂₁ - a₁₁ * a₂₀)

def det3C
    (a₀₀ a₀₁ a₀₂ a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ : ℂ) : ℂ :=
  a₀₀ * (a₁₁ * a₂₂ - a₁₂ * a₂₁)
    - a₀₁ * (a₁₀ * a₂₂ - a₁₂ * a₂₀)
    + a₀₂ * (a₁₀ * a₂₁ - a₁₁ * a₂₀)

def zeroModeChar (u q x y z : ℝ) : ℝ :=
  let v := u / (u - 1)
  let a := 1 - u * q + (u - 1) * y
  let b := u * (q - y)
  let r := v * (q - x)
  let w := 1 - x - r
  let s₀₀ := x
  let s₀₁ := r
  let s₀₂ := w
  let s₁₀ := (1 - q) * x
  let s₁₁ := (1 - q) * r + q ^ 2
  let s₁₂ := (1 - q) * w + q * (1 - q)
  let s₂₀ := a * x
  let s₂₁ := a * r + b * q
  let s₂₂ := a * w + b * (1 - q) + y
  det3
    (z - s₀₀) (-s₀₁) (-s₀₂)
    (-s₁₀) (z - s₁₁) (-s₁₂)
    (-s₂₀) (-s₂₁) (z - s₂₂)

def initialLineChar (z : ℝ) : ℝ :=
  det3
    (z - 1 / 2) (-1 / 2) 0
    (-1 / 8) (z - 3 / 4) (-1 / 8)
    0 (-1 / 2) (z - 1 / 2)

def doubleRingLineChar (z : ℝ) : ℝ :=
  z ^ 6 * (z - 1 / 8) ^ 2 * initialLineChar z

end CubicHalfSpectrum

namespace PalomarCubicHalfSpectrum

open CubicHalfSpectrum

/-- Exact characteristic-polynomial factorization of the zero Fourier mode. -/
theorem zero_mode_factorization
    (u q x y z : ℝ) (hu : u ≠ 1) :
    zeroModeChar u q x y z =
      (z - 1) * (z - q ^ 2) * (z - x * y) := by
  sorry

/-- The two strict Jury margins place every real quadratic root in `(-1,1)`. -/
theorem real_root_in_unit_interval
    {T x μ : ℝ}
    (hx : x < 1)
    (hfirst : 0 < 1 - 2 * T + x)
    (hsecond : 0 < 1 + 2 * T + x)
    (hroot : μ ^ 2 - 2 * T * μ + x = 0) :
    -1 < μ ∧ μ < 1 := by
  sorry

/-- Exact complex factorization of the nonzero double-ring outer symbol. -/
theorem double_ring_outer_symbol_factorization
    (l omega : ℂ) (homega : omega ≠ 0) :
    l ^ 24 * (l - 1 / 64) *
        det3C
          (l - 1 / 16) (-1 / 16) 0
          (-1 / 64) (l - 3 / 32) (-omega / 64)
          0 (-1 / (16 * omega)) (l - 1 / 16)
      = l ^ 24 * (l - 1 / 64) * (l - 1 / 32) *
          (l - 1 / 16) * (l - 1 / 8) := by
  sorry

/-- Exact factorization of the one-dimensional double-ring characteristic polynomial. -/
theorem double_ring_line_factorization (z : ℝ) :
    doubleRingLineChar z =
      z ^ 6 * (z - 1) * (z - 1 / 2) * (z - 1 / 4) *
        (z - 1 / 8) ^ 2 := by
  sorry

end PalomarCubicHalfSpectrum
