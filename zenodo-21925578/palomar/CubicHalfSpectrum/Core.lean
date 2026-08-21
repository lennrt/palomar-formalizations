/-
Paper: Exact Spectra of Generalized Cubic Subdivision Matrices
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925578
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact scalar certificates for the generalized-cubic half-spectrum theorem

This companion formalizes the polynomial identities and real-root exclusion
lemmas left after the paper's source reconstruction and cyclic Fourier
decomposition. The source-to-matrix map, direct-sum accounting, elementary
trigonometric ordering, and tensor-product interpretation remain in the paper
and executable artifact.
-/

noncomputable section

namespace CubicHalfSpectrum

def det2 (a₀₀ a₀₁ a₁₀ a₁₁ : ℝ) : ℝ :=
  a₀₀ * a₁₁ - a₀₁ * a₁₀

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

def quadratic (T x z : ℝ) : ℝ :=
  z ^ 2 - T * z + x / 4

def modeTrace (x ρ g : ℝ) : ℝ :=
  x + 1 / 4 + ρ * g / 2

def nonzeroModeChar (α β x g z : ℝ) : ℝ :=
  det2
    (z - x)
    (-(β * g))
    (-(α * x / 2))
    (z - (1 / 4 + α * β * g / 2))

theorem nonzero_mode_characteristic
    (α β x g z : ℝ) :
    nonzeroModeChar α β x g z = quadratic (modeTrace x (α * β) g) x z := by
  unfold nonzeroModeChar det2 quadratic modeTrace
  ring

theorem tangent_mode_factorization
    (x h z : ℝ) (hh : h ≠ 0) :
    quadratic (modeTrace x h ((1 / 2 - x) / h)) x z =
      (z - 1 / 2) * (z - x / 2) := by
  unfold quadratic modeTrace
  field_simp [hh]
  ring

theorem jury_margin_identity
    (x ρ h : ℝ) (hh : h ≠ 0) :
    1 - 2 * modeTrace x ρ ((1 / 2 - x) / h) + x =
      (1 / 2 - x) * (1 - ρ / h) := by
  unfold modeTrace
  field_simp [hh]
  ring

theorem discriminant_floor_identity (x : ℝ) :
    (x + 1 / 4) ^ 2 - x = (x - 1 / 4) ^ 2 := by
  ring

theorem root_lt_one_of_first_jury
    {T x μ : ℝ}
    (hx : x < 1)
    (hmargin : 0 < 1 - 2 * T + x)
    (hroot : μ ^ 2 - 2 * T * μ + x = 0) :
    μ < 1 := by
  by_contra hnot
  have hμ : 1 ≤ μ := le_of_not_gt hnot
  have hμpos : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have hμx : 0 < μ - x := by linarith
  have hleft : 0 < μ * (1 - 2 * T + x) := mul_pos hμpos hmargin
  have hid : μ * (1 - 2 * T + x) = -(μ - 1) * (μ - x) := by
    nlinarith [hroot]
  have hnonneg : 0 ≤ (μ - 1) * (μ - x) :=
    mul_nonneg (sub_nonneg.mpr hμ) (le_of_lt hμx)
  nlinarith

theorem neg_one_lt_root_of_second_jury
    {T x μ : ℝ}
    (hx : x < 1)
    (hmargin : 0 < 1 + 2 * T + x)
    (hroot : μ ^ 2 - 2 * T * μ + x = 0) :
    -1 < μ := by
  by_contra hnot
  have hμ : μ ≤ -1 := le_of_not_gt hnot
  have hnμ : 0 < -μ := by linarith
  have hμx : μ + x < 0 := by linarith
  have hleft : 0 < (-μ) * (1 + 2 * T + x) := mul_pos hnμ hmargin
  have hid : (-μ) * (1 + 2 * T + x) = -(μ + 1) * (μ + x) := by
    nlinarith [hroot]
  have hnonneg : 0 ≤ (μ + 1) * (μ + x) :=
    mul_nonneg_of_nonpos_of_nonpos (by linarith) (le_of_lt hμx)
  nlinarith

theorem real_root_in_unit_interval
    {T x μ : ℝ}
    (hx : x < 1)
    (hfirst : 0 < 1 - 2 * T + x)
    (hsecond : 0 < 1 + 2 * T + x)
    (hroot : μ ^ 2 - 2 * T * μ + x = 0) :
    -1 < μ ∧ μ < 1 := by
  exact ⟨neg_one_lt_root_of_second_jury hx hsecond hroot,
    root_lt_one_of_first_jury hx hfirst hroot⟩

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

theorem zero_mode_factorization
    (u q x y z : ℝ) (hu : u ≠ 1) :
    zeroModeChar u q x y z =
      (z - 1) * (z - q ^ 2) * (z - x * y) := by
  have hu' : u - 1 ≠ 0 := sub_ne_zero.mpr hu
  unfold zeroModeChar det3
  dsimp
  field_simp [hu']
  ring

/-! The paper's revised outer proof is phase-free: each nontrivial support
component has the same fixed real `3 x 3` block. -/

def doubleRingOuterCoreChar (l : ℝ) : ℝ :=
  det3
    (l - 1 / 16) (-1 / 16) 0
    (-1 / 64) (l - 3 / 32) (-1 / 64)
    0 (-1 / 16) (l - 1 / 16)

theorem doubleRingOuterCore_factorization_real (l : ℝ) :
    doubleRingOuterCoreChar l =
      (l - 1 / 8) * (l - 1 / 16) * (l - 1 / 32) := by
  unfold doubleRingOuterCoreChar det3
  ring

/-! The older Fourier-symbol route is retained as a supplemental certificate.
Its phase is complex, and the determinant agrees with the phase-free block. -/

theorem doubleRingOuterCore_factorization_complex
    (l omega : ℂ) (homega : omega ≠ 0) :
    det3C
        (l - 1 / 16) (-1 / 16) 0
        (-1 / 64) (l - 3 / 32) (-omega / 64)
        0 (-1 / (16 * omega)) (l - 1 / 16)
      = (l - 1 / 8) * (l - 1 / 16) * (l - 1 / 32) := by
  unfold det3C
  field_simp [homega]
  ring

theorem doubleRingOuterSymbol_factorization_complex
    (l omega : ℂ) (homega : omega ≠ 0) :
    l ^ 24 * (l - 1 / 64) *
        det3C
          (l - 1 / 16) (-1 / 16) 0
          (-1 / 64) (l - 3 / 32) (-omega / 64)
          0 (-1 / (16 * omega)) (l - 1 / 16)
      = l ^ 24 * (l - 1 / 64) * (l - 1 / 32) *
          (l - 1 / 16) * (l - 1 / 8) := by
  rw [doubleRingOuterCore_factorization_complex l omega homega]
  ring

def initialLineChar (z : ℝ) : ℝ :=
  det3
    (z - 1 / 2) (-1 / 2) 0
    (-1 / 8) (z - 3 / 4) (-1 / 8)
    0 (-1 / 2) (z - 1 / 2)

theorem initial_line_factorization (z : ℝ) :
    initialLineChar z =
      (z - 1) * (z - 1 / 2) * (z - 1 / 4) := by
  unfold initialLineChar det3
  ring

/-! The 11-state one-dimensional double-ring factor has six zero singleton
blocks. Its five-state nonzero core splits off two `1/8` boundary factors and
leaves the same three-state determinant as the initial factor. -/

def doubleRingLineChar (z : ℝ) : ℝ :=
  z ^ 6 * (z - 1 / 8) ^ 2 * initialLineChar z

theorem double_ring_line_polynomial_reassociation (z : ℝ) :
    doubleRingLineChar z =
      z ^ 6 * (z - 1) * (z - 1 / 2) * (z - 1 / 4) *
        (z - 1 / 8) ^ 2 := by
  unfold doubleRingLineChar
  rw [initial_line_factorization]
  ring

end CubicHalfSpectrum
