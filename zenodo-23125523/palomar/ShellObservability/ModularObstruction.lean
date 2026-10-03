module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Modular obstruction to open-neighborhood packings with a single defect. -/
namespace ShellObservability
open Matrix

/-- A full-support left null vector with zero sum excludes a single missing row.
This is a reusable certificate; no exhaustive subset enumeration is assumed. -/
theorem no_single_defect {V F : Type*} [Fintype V] [DecidableEq V] [Field F]
    (A : Matrix V V F) (w : V → F)
    (hker : vecMul w A = 0) (hsum : ∑ v, w v = 0)
    (hfull : ∀ v, w v ≠ 0) (c : V → F) (r : V) :
    A.mulVec c ≠ fun v => if v = r then 0 else 1 := by
  intro he
  have hz : dotProduct w (A.mulVec c) = 0 := by
    rw [dotProduct_mulVec, hker]
    simp
  rw [he] at hz
  have hid (v : V) : w v * (if v = r then (0:F) else 1) =
      w v - if v = r then w v else 0 := by split_ifs <;> simp
  simp only [dotProduct, hid, Finset.sum_sub_distrib] at hz
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true] at hz
  rw [hsum] at hz
  exact hfull r (by simpa using hz)

/-- A zero-one load with total one below the number of rows has exactly one
zero row. This is the counting bridge from packing to the modular certificate. -/
theorem single_defect_of_total {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℕ) (hle : ∀ v, f v ≤ 1)
    (hsum : (∑ v, f v) + 1 = Fintype.card V) :
    ∃ r, ∀ v, f v = if v = r then 0 else 1 := by
  classical
  let D := Finset.univ.filter (fun v => f v = 0)
  have hcount : D.card + (∑ v, f v) = Fintype.card V := by
    calc
      _ = ∑ v, ((if f v = 0 then 1 else 0) + f v) := by
        simp [D, Finset.sum_add_distrib]
      _ = ∑ _v : V, 1 := by
        apply Finset.sum_congr rfl
        intro v _
        have := hle v
        split_ifs <;> omega
      _ = _ := by simp
  have hD : D.card = 1 := by omega
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hD
  refine ⟨r, ?_⟩
  intro v
  by_cases hvr : v = r
  · subst v
    have hm : r ∈ D := by simp [hr]
    have hf : f r = 0 := (Finset.mem_filter.mp hm).2
    simp [hf]
  · have hn : v ∉ D := by simp [hr, hvr]
    have hf : f v ≠ 0 := by simpa [D] using hn
    have := hle v
    simp only [hvr, if_false]
    omega

end ShellObservability
