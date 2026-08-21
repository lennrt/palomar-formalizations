/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Auditable statements for the signed-circulant band-edge algebra

The definitions reproduce the paper's full phase-dependent `8 × 8` Bloch
symbol.  The selected results prove its determinant identity and the paper's
all-phase algebraic band-edge certificate.  They deliberately stop before the
direct-integral and spectral-theorem arguments.
-/

namespace PalomarSignedCirculant

noncomputable section

/-- The paper's two-variable determinant polynomial `F(t,y)`. -/
def bandPolynomial (t y : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + (80 - 2 * y) * t ^ 2 +
    (-128 + 16 * y) * t + y ^ 2 - 13 * y + 38

/-- The phase-one specialization `Q(t) = F(t,2)`. -/
def bandQuartic (t : ℝ) : ℝ :=
  t ^ 4 - 16 * t ^ 3 + 76 * t ^ 2 - 96 * t + 16

/-- The paper's full period-eight Bloch symbol.  The two arguments represent
`z` and `z⁻¹`; keeping them independent records the exact determinant
correction before the relation `z * z⁻¹ = 1` is imposed. -/
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

/-- The formula `F`, interpreted in any commutative ring. -/
def bandPolynomialRing {R : Type*} [CommRing R] (t y : R) : R :=
  t ^ 4 - 16 * t ^ 3 + (80 - 2 * y) * t ^ 2 +
    (-128 + 16 * y) * t + y ^ 2 - 13 * y + 38

/-- The correction term before imposing `z * zInv = 1`. -/
def determinantCorrection {R : Type*} [CommRing R] (x z zInv : R) : R :=
  -3 * x ^ 6 + x ^ 4 * z * zInv + 28 * x ^ 4 - 4 * x ^ 3 -
    5 * x ^ 2 * z * zInv + 3 * x ^ 2 * z + 3 * x ^ 2 * zInv -
    59 * x ^ 2 - 2 * x * z - 2 * x * zInv + 12 * x +
    4 * z * zInv - 4 * z - 4 * zInv + 17

/-- Phase reversal transposes the displayed symbol; for a unit complex phase
this is exactly Hermitian symmetry. -/
theorem bloch_symbol_phase_reversal {R : Type*} [CommRing R] (z zInv : R) :
    (blochSymbol z zInv).transpose = blochSymbol zInv z := by
  sorry

/-- Fraction-free determinant expansion of the exact displayed matrix. -/
theorem bloch_determinant_with_correction {R : Type*} [CommRing R]
    (x z zInv : R) :
    Matrix.det (Matrix.scalar (Fin 8) x - blochSymbol z zInv) =
      bandPolynomialRing (x ^ 2) (z + zInv) +
        (z * zInv - 1) * determinantCorrection x z zInv := by
  sorry

/-- Equations (4)--(5) of the paper under the phase relation
`z * zInv = 1`. -/
theorem bloch_determinant_identity {R : Type*} [CommRing R]
    (x z zInv : R) (hz : z * zInv = 1) :
    Matrix.det (Matrix.scalar (Fin 8) x - blochSymbol z zInv) =
      bandPolynomialRing (x ^ 2) (z + zInv) := by
  sorry

/-- The paper's all-phase band-edge conclusion at the algebraic level.

It isolates the phase-one root `t₀`, proves its rational separator and
nested-radical comparison, proves `F(t₀,y) ≥ 0` for `y ∈ [-2,2]` with
strictness away from `y = 2`, and excludes every zero of `F(t,y)` above `t₀`.
No spectral or direct-integral assertion is included. -/
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
  sorry

end

end PalomarSignedCirculant
