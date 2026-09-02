/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Formalization: Lennart Rudolph, with the automated assistants Sol (OpenAI
Codex) and Fable (Anthropic Claude)
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Auditable statements for the periodic signing of `C_n(1,2)`

Nine results are selected, in two layers.

The disproof layer defines the paper's period-8 triangle-flux signing of
`C_n(1,2)` as an explicit signed adjacency matrix over `ZMod n`, and proves:
it is a symmetric `±1` signing of mathlib's `SimpleGraph.circulantGraph
{1, 2}`; the Rayleigh bound `|vᵀAv| ≤ (1397/500)‖v‖²` for every real vector,
from exact rational sum-of-squares window certificates uniform in `n`; the
eigenvalue bound `|μ| ≤ 1397/500` for every real eigenpair; the comparison
`1397/500 < ρ₋(n)` for `n ≥ 32` against the conjectured minimum; and their
bundle, an explicit signing of `C_n(1,2)` whose real eigenvalues lie strictly
below `ρ₋(n)` for every `n ≡ 0 (mod 8)` with `n ≥ 32`.

The algebra layer reproduces the paper's full phase-dependent `8 × 8` Bloch
symbol and proves four results about it: phase reversal transposes the
displayed symbol; a fraction-free determinant expansion exhibits the exact
correction divisible by `z*zInv - 1`; the determinant identity
`det(xI-B(z)) = F(x²,z+z⁻¹)` holds under `z*zInv = 1`; and an all-phase
algebraic band-edge certificate locates the phase-one root and excludes every
zero above it.

The eigenvalue statements quantify over real eigenpairs; the spectral theorem
is not imported and no spectral-radius or complex-spectrum claim is selected.
The direct-integral argument, the exact radius `√t₀`, Sturm's theorem, and the
period-at-most-16 classification are likewise outside this selection.
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

/-! ## The period-eight signing family and Suvagiya's Conjecture 3

Suvagiya (arXiv:2607.18334, Conjecture 3) asserts that for every even `n ≥ 8`
the minimum spectral radius over all `±1` signings of the circulant graph
`C_n(1,2)` equals `ρ₋(n) = 2 √(cos²(π/n) + cos²(2π/n))`.  The definitions and
statements below package the paper's refutation of that conjecture on the
arithmetic progression `n ≡ 0 (mod 8)`, `n ≥ 32`. -/

/-- The period-8 triangle-flux word (+1,−1,+1,−1,−1,+1,−1,+1): −1 exactly at
residues 1, 3, 4, 6. -/
def fluxWord (i : ZMod 8) : ℤ :=
  if i.val = 1 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then -1 else 1

/-- The step-2 sign at vertex `i` of `C_n(1,2)`, read through the reduction
`ZMod n → ZMod 8`. -/
def stepTwoSign (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) : ℤ :=
  fluxWord (ZMod.castHom hdvd (ZMod 8) i)

/-- The signed adjacency matrix of `C_n(1,2)`: every step-1 edge positive,
the step-2 edge starting at `i` signed by `stepTwoSign`. -/
def signedAdjacency (n : ℕ) (hdvd : 8 ∣ n) : Matrix (ZMod n) (ZMod n) ℝ :=
  fun i j =>
    (if j = i + 1 ∨ i = j + 1 then 1 else 0) +
    (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) else 0) +
    (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) else 0)

/-- `A` is a ±1 signing of the circulant graph `C_n(1,2)`. -/
def IsCirculantSigning (n : ℕ) (A : Matrix (ZMod n) (ZMod n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  (∀ i j, (SimpleGraph.circulantGraph {(1 : ZMod n), 2}).Adj i j →
    A i j = 1 ∨ A i j = -1) ∧
  (∀ i j, ¬ (SimpleGraph.circulantGraph {(1 : ZMod n), 2}).Adj i j → A i j = 0)

/-- Suvagiya's twisted-class spectral radius `ρ₋(n)`. -/
noncomputable def rhoMinus (n : ℕ) : ℝ :=
  2 * Real.sqrt (Real.cos (Real.pi / n) ^ 2 + Real.cos (2 * Real.pi / n) ^ 2)

/-- The displayed matrix really is a `±1` signing of `C_n(1,2)`: it is
symmetric, its entries on edges of `C_n(1,2)` are `±1`, and it vanishes off
those edges. -/
theorem signedAdjacency_isCirculantSigning (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) :
    IsCirculantSigning n (signedAdjacency n hdvd) := by
  sorry

/-- The exact rational sum-of-squares window certificate: the Rayleigh
numerator of the signing is bounded by `1397/500` times the squared norm,
uniformly in `n`. -/
theorem rayleigh_band_bound (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) (v : ZMod n → ℝ) :
    |∑ i, ∑ j, v i * signedAdjacency n hdvd i j * v j| ≤ 1397 / 500 * ∑ i, v i ^ 2 := by
  sorry

/-- Consequently every eigenvalue of the signing has absolute value at most
`1397/500`. -/
theorem eigenvalue_band_bound (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) (μ : ℝ) (v : ZMod n → ℝ)
    (hv : v ≠ 0) (hev : (signedAdjacency n hdvd).mulVec v = μ • v) :
    |μ| ≤ 1397 / 500 := by
  sorry

/-- The rational separator `1397/500` lies strictly below the conjectured
minimum `ρ₋(n)` for every `n ≥ 32`. -/
theorem separator_lt_twisted_value (n : ℕ) (hn : 32 ≤ n) :
    (1397 / 500 : ℝ) < rhoMinus n := by
  sorry

/-- The refutation.  For every `n ≡ 0 (mod 8)` with `n ≥ 32` there is a `±1`
signing of `C_n(1,2)` all of whose eigenvalues are strictly smaller in absolute
value than Suvagiya's conjectured minimum `ρ₋(n)`. -/
theorem periodic_signing_beats_twisted_class (n : ℕ) [NeZero n] (hdvd : 8 ∣ n)
    (hn : 32 ≤ n) :
    ∃ A : Matrix (ZMod n) (ZMod n) ℝ, IsCirculantSigning n A ∧
      ∀ (μ : ℝ) (v : ZMod n → ℝ), v ≠ 0 → A.mulVec v = μ • v → |μ| < rhoMinus n := by
  sorry

end

end PalomarSignedCirculant
