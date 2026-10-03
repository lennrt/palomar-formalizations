module

public import ShellTomography.Foundations
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# Paired distance fibers and antisymmetric trades

A distance shell in a cycle has at most two vertices, exchanged by reflection
about the sensor. This module separates the general finite-fiber argument from
the arithmetic verification of the cycle distance fibers.
-/

namespace ShellObservability

open ShellTomography

section PairedFibers

variable {V R : Type*} [Fintype V] [DecidableEq V] [DecidableEq R]

/-- Every nonempty measurement fiber is a point together with its reflected point.
A fixed point is permitted and gives a singleton fiber. -/
def PairedFibers (δ : V → R) (f : V → V) : Prop :=
  ∀ v w, δ w = δ v ↔ w = v ∨ w = f v

/-- Signed occupancy in a fiber of a single measurement. -/
def fiberSum (δ : V → R) (z : V → ℤ) (r : R) : ℤ :=
  ∑ w, if δ w = r then z w else 0

omit [DecidableEq V] in
theorem fiberSum_eq_shellZ (δ : V → R) (z : V → ℤ) (r : R) :
    fiberSum δ z r = shellZ (fun (_ : Unit) v => δ v) z () r := rfl

/-- The signed sum in a paired fiber, including the singleton case. -/
theorem paired_fiber_sum (δ : V → R) (f : V → V) (hf : PairedFibers δ f)
    (z : V → ℤ) (v : V) :
    fiberSum δ z (δ v) = if f v = v then z v else z v + z (f v) := by
  classical
  unfold fiberSum
  by_cases hfix : f v = v
  · simp only [hfix, ↓reduceIte]
    simp_rw [hf v, hfix, or_self]
    simp
  · simp only [hfix, ↓reduceIte]
    have heq (w : V) :
        (if δ w = δ v then z w else 0) =
          (if w = v then z w else 0) + (if w = f v then z w else 0) := by
      simp only [hf v]
      by_cases hw : w = v
      · subst w
        simp [Ne.symm hfix]
      · by_cases hfw : w = f v <;> simp [hw, hfw, hfix]
    simp_rw [heq]
    rw [Finset.sum_add_distrib]
    simp

/-- Vanishing shell sums are equivalent to sign reversal across each paired fiber.
This conclusion is derived from the measurement fibers, not postulated. -/
theorem paired_fibers_zero_iff_antisymmetric (δ : V → R) (f : V → V)
    (hf : PairedFibers δ f) (z : V → ℤ) :
    (∀ r, fiberSum δ z r = 0) ↔ ∀ v, z (f v) = -z v := by
  constructor
  · intro hz v
    have hv := hz (δ v)
    rw [paired_fiber_sum δ f hf z v] at hv
    split_ifs at hv with hfix
    · simp [hfix, hv]
    · omega
  · intro hz r
    by_cases hr : ∃ v, δ v = r
    · obtain ⟨v, rfl⟩ := hr
      rw [paired_fiber_sum δ f hf z v]
      split_ifs with hfix
      · have hv := hz v
        rw [hfix] at hv
        omega
      · rw [hz v]
        omega
    · unfold fiberSum
      apply Finset.sum_eq_zero
      intro v _
      have hv : δ v ≠ r := fun h => hr ⟨v, h⟩
      simp [hv]

/-- Sensor families with paired measurement fibers have precisely the common
antisymmetric trades. -/
theorem invisible_iff_antisymmetric {S : Type*} (δ : S → V → R)
    (f : S → V → V) (hf : ∀ s, PairedFibers (δ s) (f s)) (z : V → ℤ) :
    Invisible δ z ↔ ∀ s v, z (f s v) = -z v := by
  constructor
  · intro hz s
    exact (paired_fibers_zero_iff_antisymmetric (δ s) (f s) (hf s) z).mp (hz s)
  · intro hz s
    exact (paired_fibers_zero_iff_antisymmetric (δ s) (f s) (hf s) z).mpr (hz s)

end PairedFibers

end ShellObservability

namespace ShellObservability

open ShellTomography

section CyclicDistance

variable {n : ℕ} [NeZero n]

/-- Shortest cyclic displacement; the two terms are the clockwise and
counterclockwise lengths. -/
def cyclicNorm (a : ZMod n) : ℕ := min a.val (-a).val

/-- Cyclic distance on the residue classes modulo `n`. -/
def cyclicDistance (s v : ZMod n) : ℕ := cyclicNorm (v - s)

/-- Reflection in a sensor, in additive coordinates on the cycle. -/
def reflection (s v : ZMod n) : ZMod n := 2 * s - v

omit [NeZero n] in
@[simp] theorem cyclicNorm_neg (a : ZMod n) : cyclicNorm (-a) = cyclicNorm a := by
  simp [cyclicNorm, min_comm]

/-- Equal cyclic lengths have exactly the two possible orientations. -/
theorem cyclicNorm_eq_iff (a b : ZMod n) :
    cyclicNorm a = cyclicNorm b ↔ a = b ∨ a = -b := by
  constructor
  · intro h
    unfold cyclicNorm at h
    simp only [min_def] at h
    split_ifs at h with ha hb hb
    · exact Or.inl ((ZMod.val_injective n) h)
    · exact Or.inr ((ZMod.val_injective n) h)
    · right
      have he := (ZMod.val_injective n) h
      exact neg_eq_iff_eq_neg.mp he
    · left
      have he := (ZMod.val_injective n) h
      exact neg_injective he
  · rintro (rfl | rfl)
    · rfl
    · exact cyclicNorm_neg b

/-- The cyclic distance fibers are precisely the reflection pairs. -/
theorem cyclicDistance_pairedFibers (s : ZMod n) :
    PairedFibers (cyclicDistance s) (reflection s) := by
  intro v w
  unfold cyclicDistance
  rw [cyclicNorm_eq_iff]
  constructor
  · rintro (h | h)
    · left
      exact sub_left_inj.mp h
    · right
      unfold reflection
      linear_combination h
  · rintro (rfl | h)
    · exact Or.inl rfl
    · right
      rw [h]
      unfold reflection
      ring

/-- Exact shell-kernel description for any family of labelled cycle sensors. -/
theorem cycle_invisible_iff_antisymmetric {S : Type*} (sensors : S → ZMod n)
    (z : ZMod n → ℤ) :
    Invisible (fun s v => cyclicDistance (sensors s) v) z ↔
      ∀ s v, z (2 * sensors s - v) = -z v :=
  invisible_iff_antisymmetric _ _ (fun s => cyclicDistance_pairedFibers (sensors s)) z

end CyclicDistance

end ShellObservability
