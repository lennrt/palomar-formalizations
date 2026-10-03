module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Tactic

@[expose] public section

/-!
# Residual syndromes for rectangular incidence packings

A left annihilator of an incidence matrix gives conservation laws for every
residual. For a disjoint 0/1 packing, the residual is the indicator of the
uncovered rows, so its syndrome is a sum of matrix columns. Excluding all
supports below a given size yields a packing bound with a certified defect.
No square-matrix, field, singleton-defect, or invertibility assumption is used.
-/

namespace ShellObservability

section Rectangular

variable {L R C K : Type*} [Fintype R] [Fintype C] [Semiring K]

/-- Left annihilators constrain arbitrary residuals in a rectangular linear
system. This is the algebraic conservation law behind defect certificates. -/
theorem residual_syndrome (W : Matrix L R K) (A : Matrix R C K)
    (c : C → K) (d b : R → K)
    (hWA : W * A = 0) (hresidual : A.mulVec c + d = b) :
    W.mulVec d = W.mulVec b := by
  rw [← hresidual, Matrix.mulVec_add, Matrix.mulVec_mulVec, hWA, Matrix.zero_mulVec]
  simp

end Rectangular

section Indicators

variable {L R K : Type*} [Fintype R] [DecidableEq R] [Semiring K]

/-- A finite set, represented as a literal zero-one vector. -/
def supportIndicator (D : Finset R) : R → K := fun r => if r ∈ D then 1 else 0

/-- Sum the columns of `W` indexed by a residual support. -/
def supportSyndrome (W : Matrix L R K) (D : Finset R) : L → K :=
  fun l => ∑ r ∈ D, W l r

/-- Matrix multiplication of an indicator is exactly a column-subset sum. -/
theorem indicator_syndrome (W : Matrix L R K) (D : Finset R) :
    W.mulVec (supportIndicator D) = supportSyndrome W D := by
  funext l
  simp [Matrix.mulVec, dotProduct, supportIndicator, supportSyndrome, mul_ite]

/-- A residual indicator must realize the target syndrome as a column-subset sum. -/
theorem support_syndrome_of_residual {C : Type*} [Fintype C]
    (W : Matrix L R K) (A : Matrix R C K) (c : C → K) (b : R → K) (D : Finset R)
    (hWA : W * A = 0) (hresidual : A.mulVec c + supportIndicator D = b) :
    supportSyndrome W D = W.mulVec b := by
  rw [← indicator_syndrome]
  exact residual_syndrome W A c (supportIndicator D) b hWA hresidual

end Indicators

section Packings

variable {L R C K : Type*} [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C] [Semiring K]
variable (incidence : R → C → Prop) [DecidableRel incidence]

/-- The literal zero-one incidence matrix, over any chosen semiring. -/
def incidenceMatrix : Matrix R C K := fun r c => if incidence r c then 1 else 0

/-- Number of selected columns covering a row, counted in the natural numbers. -/
def rowCoverage (selected : Finset C) (r : R) : ℕ :=
  ∑ c ∈ selected, if incidence r c then 1 else 0

/-- Selected columns form a packing when no row is covered twice. -/
def IsIncidencePacking (selected : Finset C) : Prop :=
  ∀ r, rowCoverage incidence selected r ≤ 1

/-- The exact uncovered-row support of a selected packing. -/
def uncoveredRows (selected : Finset C) : Finset R :=
  Finset.univ.filter (fun r => rowCoverage incidence selected r = 0)

omit [Fintype R] [DecidableEq R] in
/-- Algebraic incidence multiplication agrees with natural-number row coverage. -/
theorem incidence_mul_indicator (selected : Finset C) :
    (incidenceMatrix (K := K) incidence).mulVec (supportIndicator selected) =
      fun r => (rowCoverage incidence selected r : K) := by
  funext r
  simp [Matrix.mulVec, dotProduct, incidenceMatrix, supportIndicator, rowCoverage,
    mul_ite]

/-- A genuine 0/1 packing leaves exactly the indicator of its uncovered rows. -/
theorem packing_residual_identity (selected : Finset C)
    (hpacking : IsIncidencePacking incidence selected) :
    (incidenceMatrix (K := K) incidence).mulVec (supportIndicator selected) +
      supportIndicator (uncoveredRows incidence selected) = 1 := by
  rw [incidence_mul_indicator]
  funext r
  have hr := hpacking r
  have hc : rowCoverage incidence selected r = 0 ∨ rowCoverage incidence selected r = 1 := by omega
  rcases hc with hc | hc <;> simp [supportIndicator, uncoveredRows, hc]

/-- Multi-defect syndrome theorem: every uncovered support, of any size,
has the fixed target syndrome `W * 1`. -/
theorem packing_defect_syndrome (W : Matrix L R K) (selected : Finset C)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected) :
    supportSyndrome W (uncoveredRows incidence selected) = W.mulVec 1 :=
  support_syndrome_of_residual W (incidenceMatrix (K := K) incidence) (supportIndicator selected) 1
    (uncoveredRows incidence selected) hWA (packing_residual_identity incidence selected hpacking)

/-- A support-size obstruction rules out that exact number of uncovered rows. -/
theorem no_packing_with_defect_card (W : Matrix L R K) (selected : Finset C) (t : ℕ)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected)
    (hexclude : ∀ D : Finset R, D.card = t → supportSyndrome W D ≠ W.mulVec 1) :
    (uncoveredRows incidence selected).card ≠ t := by
  intro ht
  exact hexclude _ ht (packing_defect_syndrome incidence W selected hWA hpacking)

/-- Excluding all supports below `ell` forces at least `ell` uncovered rows. -/
theorem packing_defect_lower_bound (W : Matrix L R K) (selected : Finset C) (ell : ℕ)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected)
    (hexclude : ∀ D : Finset R, D.card < ell → supportSyndrome W D ≠ W.mulVec 1) :
    ell ≤ (uncoveredRows incidence selected).card := by
  by_contra hn
  have ht : (uncoveredRows incidence selected).card < ell := by omega
  exact hexclude _ ht (packing_defect_syndrome incidence W selected hWA hpacking)

omit [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- Double count all row-column incidences of the selected columns. -/
theorem total_rowCoverage (selected : Finset C) :
    (∑ r, rowCoverage incidence selected r) =
      ∑ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card := by
  unfold rowCoverage
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  simp

omit [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- Every row is either covered exactly once or is uncovered. -/
theorem packing_coverage_plus_defect (selected : Finset C)
    (hpacking : IsIncidencePacking incidence selected) :
    (∑ r, rowCoverage incidence selected r) + (uncoveredRows incidence selected).card =
      Fintype.card R := by
  have hD : (uncoveredRows incidence selected).card =
      ∑ r, if rowCoverage incidence selected r = 0 then 1 else 0 := by
    simp [uncoveredRows]
  rw [hD, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _r : R, 1 := by
      apply Finset.sum_congr rfl
      intro r _
      have hr := hpacking r
      split_ifs <;> omega
    _ = _ := by simp

omit [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- For regular columns, the packing cardinality determines the exact defect. -/
theorem regular_packing_count (selected : Finset C) (k : ℕ)
    (hregular : ∀ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card = k)
    (hpacking : IsIncidencePacking incidence selected) :
    k * selected.card + (uncoveredRows incidence selected).card = Fintype.card R := by
  have htotal := packing_coverage_plus_defect incidence selected hpacking
  rw [total_rowCoverage] at htotal
  have hsum : (∑ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card) =
      k * selected.card := by
    rw [Finset.sum_congr rfl hregular]
    simp [Nat.mul_comm]
  rwa [hsum] at htotal

omit [Fintype C] [DecidableEq R] [DecidableEq C] in
/-- The exact defect cardinality as a natural-number residual. -/
theorem regular_packing_defect_card (selected : Finset C) (k : ℕ)
    (hregular : ∀ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card = k)
    (hpacking : IsIncidencePacking incidence selected) :
    (uncoveredRows incidence selected).card = Fintype.card R - k * selected.card := by
  have hcount := regular_packing_count incidence selected k hregular hpacking
  omega

/-- A reusable packing bound from a rectangular left-annihilator certificate
and a multi-defect support-syndrome exclusion. -/
theorem syndrome_packing_bound (W : Matrix L R K) (selected : Finset C) (k ell : ℕ)
    (hregular : ∀ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card = k)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected)
    (hexclude : ∀ D : Finset R, D.card < ell → supportSyndrome W D ≠ W.mulVec 1) :
    k * selected.card + ell ≤ Fintype.card R := by
  have hcount := regular_packing_count incidence selected k hregular hpacking
  have hdefect := packing_defect_lower_bound incidence W selected ell hWA hpacking hexclude
  omega

/-- Exact-defect exclusion also rules out a proposed packing cardinality. -/
theorem syndrome_excludes_packing_card (W : Matrix L R K) (selected : Finset C) (k t : ℕ)
    (hregular : ∀ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card = k)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected)
    (hexclude : ∀ D : Finset R, D.card = t → supportSyndrome W D ≠ W.mulVec 1) :
    k * selected.card + t ≠ Fintype.card R := by
  intro ht
  have hcount := regular_packing_count incidence selected k hregular hpacking
  have hdefect : (uncoveredRows incidence selected).card = t := by omega
  exact no_packing_with_defect_card incidence W selected t hWA hpacking hexclude hdefect

end Packings

end ShellObservability
