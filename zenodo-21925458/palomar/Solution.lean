/-
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Nat.Dist
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000

namespace PalomarMSET25

abbrev CylinderVertex (m : ℕ) := Fin m × Fin (6 * m)

def cycleDistance {N : ℕ} (a b : Fin N) : ℕ :=
  min (Nat.dist a.val b.val) (N - Nat.dist a.val b.val)

def cylinderDistance {m : ℕ} (u v : CylinderVertex m) : ℕ :=
  Nat.dist u.1.val v.1.val + cycleDistance u.2 v.2

def displayedEvenCylinderLandmarks (m : ℕ) (hm : 1 ≤ m) :
    Multiset (CylinderVertex m) :=
  {(⟨0, hm⟩, ⟨0, by omega⟩),
    (⟨0, hm⟩, ⟨2 * m, by omega⟩),
    (⟨m - 1, by omega⟩, ⟨0, by omega⟩)}

def multisetCode {m : ℕ} (W : Multiset (CylinderVertex m))
    (v : CylinderVertex m) : Multiset ℕ :=
  W.map (cylinderDistance v)

def IsMultisetResolving {m : ℕ} (W : Multiset (CylinderVertex m)) : Prop :=
  Function.Injective (multisetCode W)

/-- The four affine pieces of the paper's cycle distance-pair locus. -/
def CyclePairLocus (m j a b : ℕ) : Prop :=
  (j ≤ 2 * m ∧ a = j ∧ b = 2 * m - j) ∨
  (2 * m ≤ j ∧ j ≤ 3 * m ∧ a = j ∧ b = j - 2 * m) ∨
  (3 * m ≤ j ∧ j ≤ 5 * m ∧ a = 6 * m - j ∧ b = j - 2 * m) ∨
  (5 * m ≤ j ∧ a = 6 * m - j ∧ b = 8 * m - j)

/-- Equation (5) / Lemma 1: the distances from `j` to columns `0` and `2m`. -/
theorem cycle_distance_pair_locus (m : ℕ) (j : Fin (6 * m)) :
    let a := cycleDistance j ⟨0, by have := j.isLt; omega⟩
    let b := cycleDistance j ⟨2 * m, by have := j.isLt; omega⟩
    CyclePairLocus m j.val a b := by
  dsimp
  unfold CyclePairLocus
  by_cases h2 : j.val ≤ 2 * m
  · left
    have hdist0 : Nat.dist j.val 0 = j.val := Nat.dist_zero_right _
    have hdist2 : Nat.dist j.val (2 * m) = 2 * m - j.val :=
      Nat.dist_eq_sub_of_le h2
    have hmin0 : min j.val (6 * m - j.val) = j.val :=
      min_eq_left (by omega)
    have hmin2 :
        min (2 * m - j.val) (6 * m - (2 * m - j.val)) = 2 * m - j.val :=
      min_eq_left (by omega)
    simp only [cycleDistance, hdist0, hdist2, hmin0, hmin2]
    exact ⟨h2, by simp, by simp⟩
  by_cases h3 : j.val ≤ 3 * m
  · right; left
    have h2' : 2 * m ≤ j.val := by omega
    have hdist0 : Nat.dist j.val 0 = j.val := Nat.dist_zero_right _
    have hdist2 : Nat.dist j.val (2 * m) = j.val - 2 * m :=
      Nat.dist_eq_sub_of_le_right h2'
    have hmin0 : min j.val (6 * m - j.val) = j.val :=
      min_eq_left (by omega)
    have hmin2 :
        min (j.val - 2 * m) (6 * m - (j.val - 2 * m)) = j.val - 2 * m :=
      min_eq_left (by omega)
    simp only [cycleDistance, hdist0, hdist2, hmin0, hmin2]
    exact ⟨h2', h3, by simp, by simp⟩
  by_cases h5 : j.val ≤ 5 * m
  · right; right; left
    have h3' : 3 * m ≤ j.val := by omega
    have h2' : 2 * m ≤ j.val := by omega
    have hdist0 : Nat.dist j.val 0 = j.val := Nat.dist_zero_right _
    have hdist2 : Nat.dist j.val (2 * m) = j.val - 2 * m :=
      Nat.dist_eq_sub_of_le_right h2'
    have hmin0 : min j.val (6 * m - j.val) = 6 * m - j.val :=
      min_eq_right (by omega)
    have hmin2 :
        min (j.val - 2 * m) (6 * m - (j.val - 2 * m)) = j.val - 2 * m :=
      min_eq_left (by omega)
    simp only [cycleDistance, hdist0, hdist2, hmin0, hmin2]
    exact ⟨h3', h5, by simp, by simp⟩
  · right; right; right
    have h5' : 5 * m ≤ j.val := by omega
    have h2' : 2 * m ≤ j.val := by omega
    have hdist0 : Nat.dist j.val 0 = j.val := Nat.dist_zero_right _
    have hdist2 : Nat.dist j.val (2 * m) = j.val - 2 * m :=
      Nat.dist_eq_sub_of_le_right h2'
    have hmin0 : min j.val (6 * m - j.val) = 6 * m - j.val :=
      min_eq_right (by omega)
    have hmin2 :
        min (j.val - 2 * m) (6 * m - (j.val - 2 * m)) =
          8 * m - j.val := by
      rw [min_eq_right]
      · omega
      · omega
    simp only [cycleDistance, hdist0, hdist2, hmin0, hmin2]
    exact ⟨h5', by simp, by simp⟩

private lemma cyclePairLocus_injective
    (m : ℕ)
    {j₁ j₂ a₁ b₁ a₂ b₂ : ℕ}
    (hj₁ : j₁ < 6 * m) (hj₂ : j₂ < 6 * m)
    (hc₁ : CyclePairLocus m j₁ a₁ b₁)
    (hc₂ : CyclePairLocus m j₂ a₂ b₂)
    (ha : a₁ = a₂) (hb : b₁ = b₂) :
    j₁ = j₂ := by
  unfold CyclePairLocus at hc₁ hc₂
  rcases hc₁ with h₁ | h₁ | h₁ | h₁
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;> omega

/-- The injectivity conclusion of Lemma 1: the two cycle distances determine the column. -/
theorem cycle_distance_pair_injective (m : ℕ) (j₁ j₂ : Fin (6 * m))
    (h₀ : cycleDistance j₁ ⟨0, by have := j₁.isLt; omega⟩ =
      cycleDistance j₂ ⟨0, by have := j₂.isLt; omega⟩)
    (h₂m : cycleDistance j₁ ⟨2 * m, by have := j₁.isLt; omega⟩ =
      cycleDistance j₂ ⟨2 * m, by have := j₂.isLt; omega⟩) :
    j₁ = j₂ := by
  apply Fin.ext
  apply cyclePairLocus_injective m j₁.isLt j₂.isLt
  · exact cycle_distance_pair_locus m j₁
  · exact cycle_distance_pair_locus m j₂
  · exact h₀
  · exact h₂m

private lemma cyclePairLocus_swap_forces_equal
    (m : ℕ)
    {i₁ i₂ j₁ j₂ a₁ b₁ a₂ b₂ : ℕ}
    (hi₁ : i₁ < m) (hi₂ : i₂ < m)
    (hj₁ : j₁ < 6 * m) (hj₂ : j₂ < 6 * m)
    (hc₁ : CyclePairLocus m j₁ a₁ b₁)
    (hc₂ : CyclePairLocus m j₂ a₂ b₂)
    (hswap₁ : i₁ + a₁ = i₂ + b₂)
    (hswap₂ : i₁ + b₁ = i₂ + a₂)
    (hz : (m - 1 - i₁) + a₁ = (m - 1 - i₂) + a₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hsum₁ : a₁ + b₁ = 2 * a₂ := by omega
  have hsum₂ : a₂ + b₂ = 2 * a₁ := by omega
  have hshift : i₂ + a₁ = i₁ + a₂ := by omega
  clear hswap₁ hswap₂ hz
  unfold CyclePairLocus at hc₁ hc₂
  rcases hc₁ with h₁ | h₁ | h₁ | h₁
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;>
      constructor <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;>
      constructor <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;>
      constructor <;> omega
  · rcases hc₂ with h₂ | h₂ | h₂ | h₂ <;>
      constructor <;> omega

private lemma pair_multiset_eq_cases {a b c d : ℕ}
    (h : ({a, b} : Multiset ℕ) = {c, d}) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  change a ::ₘ b ::ₘ 0 = c ::ₘ d ::ₘ 0 at h
  rw [Multiset.cons_eq_cons] at h
  rcases h with ⟨hac, htail⟩ | ⟨_, cs, hleft, hright⟩
  · left
    exact ⟨hac, Multiset.singleton_inj.mp htail⟩
  · have hcard : cs.card = 0 := by
      have := congrArg Multiset.card hleft
      simp only [Multiset.card_cons, Multiset.card_zero] at this
      omega
    have hcs : cs = 0 := Multiset.card_eq_zero.mp hcard
    subst cs
    right
    constructor
    · simpa using hright.symm
    · simpa using hleft

private lemma parity_separates_third
    {x₁ y₁ z₁ x₂ y₂ z₂ : ℕ}
    (hxy₁ : x₁ % 2 = y₁ % 2) (hxz₁ : x₁ % 2 ≠ z₁ % 2)
    (hxy₂ : x₂ % 2 = y₂ % 2) (hxz₂ : x₂ % 2 ≠ z₂ % 2)
    (h : ({x₁, y₁, z₁} : Multiset ℕ) = {x₂, y₂, z₂}) :
    z₁ = z₂ ∧ ({x₁, y₁} : Multiset ℕ) = {x₂, y₂} := by
  have hp : x₁ % 2 = x₂ % 2 := by
    by_contra hne
    have hx₁lt : x₁ % 2 < 2 := Nat.mod_lt _ (by omega)
    have hx₂lt : x₂ % 2 < 2 := Nat.mod_lt _ (by omega)
    have hz₂lt : z₂ % 2 < 2 := Nat.mod_lt _ (by omega)
    have hz₂eq : z₂ % 2 = x₁ % 2 := by omega
    have hy₂ne : y₂ % 2 ≠ x₁ % 2 := by omega
    have hy₁z₁ : y₁ % 2 ≠ z₁ % 2 := by omega
    have hleft :
        (({x₁, y₁, z₁} : Multiset ℕ).map (fun n => n % 2)).count (x₁ % 2) = 2 := by
      simp [hxy₁, hy₁z₁]
    have hright :
        (({x₂, y₂, z₂} : Multiset ℕ).map (fun n => n % 2)).count (x₁ % 2) = 1 := by
      simp [hne, hy₂ne, hz₂eq]
    have hmapped := congrArg (Multiset.map (fun n : ℕ => n % 2)) h
    have hcount := congrArg (Multiset.count (x₁ % 2)) hmapped
    rw [hleft, hright] at hcount
    omega
  have hy₁ : y₁ % 2 = x₁ % 2 := hxy₁.symm
  have hz₁ : z₁ % 2 ≠ x₁ % 2 := by omega
  have hx₂ : x₂ % 2 = x₁ % 2 := hp.symm
  have hy₂ : y₂ % 2 = x₁ % 2 := by omega
  have hzmem : z₁ ∈ ({x₂, y₂, z₂} : Multiset ℕ) := by
    rw [← h]
    simp
  have hzmem' : z₁ = x₂ ∨ z₁ = y₂ ∨ z₁ = z₂ := by
    simpa using hzmem
  have hz : z₁ = z₂ := by
    rcases hzmem' with hz₁x₂ | hz₁y₂ | hz₁z₂
    · have := congrArg (fun n : ℕ => n % 2) hz₁x₂
      omega
    · have := congrArg (fun n : ℕ => n % 2) hz₁y₂
      omega
    · exact hz₁z₂
  have rotate (a b c : ℕ) :
      ({a, b, c} : Multiset ℕ) = c ::ₘ ({a, b} : Multiset ℕ) := by
    change a ::ₘ b ::ₘ c ::ₘ 0 = c ::ₘ a ::ₘ b ::ₘ 0
    calc
      a ::ₘ b ::ₘ c ::ₘ 0 = a ::ₘ c ::ₘ b ::ₘ 0 :=
        congrArg (fun s => a ::ₘ s) (Multiset.cons_swap b c 0)
      _ = c ::ₘ a ::ₘ b ::ₘ 0 := Multiset.cons_swap a c (b ::ₘ 0)
  constructor
  · exact hz
  · apply (Multiset.cons_inj_right z₁).mp
    calc
      z₁ ::ₘ ({x₁, y₁} : Multiset ℕ) = {x₁, y₁, z₁} := (rotate x₁ y₁ z₁).symm
      _ = {x₂, y₂, z₂} := h
      _ = z₁ ::ₘ ({x₂, y₂} : Multiset ℕ) := by simpa [hz] using rotate x₂ y₂ z₂

theorem even_cylinder_three_landmarks_resolve
    (m : ℕ) (hm : 2 ≤ m) (heven : 2 ∣ m) :
    IsMultisetResolving (displayedEvenCylinderLandmarks m (by omega)) := by
  intro v₁ v₂ hcode
  rcases heven with ⟨k, hk⟩
  subst m
  let a₁ := cycleDistance v₁.2 ⟨0, by have := v₁.2.isLt; omega⟩
  let b₁ := cycleDistance v₁.2 ⟨2 * (2 * k), by have := v₁.2.isLt; omega⟩
  let a₂ := cycleDistance v₂.2 ⟨0, by have := v₂.2.isLt; omega⟩
  let b₂ := cycleDistance v₂.2 ⟨2 * (2 * k), by have := v₂.2.isLt; omega⟩
  have hrow₁ : Nat.dist v₁.1.val (2 * k - 1) = 2 * k - 1 - v₁.1.val :=
    Nat.dist_eq_sub_of_le (by have := v₁.1.isLt; omega)
  have hrow₂ : Nat.dist v₂.1.val (2 * k - 1) = 2 * k - 1 - v₂.1.val :=
    Nat.dist_eq_sub_of_le (by have := v₂.1.isLt; omega)
  have hcode' :
      ({v₁.1.val + a₁, v₁.1.val + b₁,
          (2 * k - 1 - v₁.1.val) + a₁} : Multiset ℕ) =
        {v₂.1.val + a₂, v₂.1.val + b₂,
          (2 * k - 1 - v₂.1.val) + a₂} := by
    simpa [IsMultisetResolving, multisetCode, displayedEvenCylinderLandmarks,
      cylinderDistance, Nat.dist_zero_right, hrow₁, hrow₂,
      a₁, b₁, a₂, b₂] using hcode
  have hc₁ := cycle_distance_pair_locus (2 * k) v₁.2
  have hc₂ := cycle_distance_pair_locus (2 * k) v₂.2
  have hc₁_cases := hc₁
  have hc₂_cases := hc₂
  unfold CyclePairLocus at hc₁_cases hc₂_cases
  have hab₁ : a₁ % 2 = b₁ % 2 := by
    rcases hc₁_cases with h | h | h | h <;> simp only [a₁, b₁] <;> omega
  have hab₂ : a₂ % 2 = b₂ % 2 := by
    rcases hc₂_cases with h | h | h | h <;> simp only [a₂, b₂] <;> omega
  have hxy₁ : (v₁.1.val + a₁) % 2 = (v₁.1.val + b₁) % 2 := by
    omega
  have hxy₂ : (v₂.1.val + a₂) % 2 = (v₂.1.val + b₂) % 2 := by
    omega
  have hxz₁ :
      (v₁.1.val + a₁) % 2 ≠
        ((2 * k - 1 - v₁.1.val) + a₁) % 2 := by
    have hi := v₁.1.isLt
    omega
  have hxz₂ :
      (v₂.1.val + a₂) % 2 ≠
        ((2 * k - 1 - v₂.1.val) + a₂) % 2 := by
    have hi := v₂.1.isLt
    omega
  obtain ⟨hz, hpair⟩ :=
    parity_separates_third hxy₁ hxz₁ hxy₂ hxz₂ hcode'
  rcases pair_multiset_eq_cases hpair with hs | hs
  · rcases hs with ⟨hx, hy⟩
    have hi₁ := v₁.1.isLt
    have hi₂ := v₂.1.isLt
    have hi : v₁.1.val = v₂.1.val := by omega
    have ha : a₁ = a₂ := by omega
    have hb : b₁ = b₂ := by omega
    have hj : v₁.2.val = v₂.2.val :=
      cyclePairLocus_injective (2 * k)
        v₁.2.isLt v₂.2.isLt hc₁ hc₂ ha hb
    apply Prod.ext
    · apply Fin.ext
      exact hi
    · apply Fin.ext
      exact hj
  · rcases hs with ⟨hx, hy⟩
    have hij :=
      cyclePairLocus_swap_forces_equal (2 * k)
        v₁.1.isLt v₂.1.isLt v₁.2.isLt v₂.2.isLt hc₁ hc₂ hx hy hz
    apply Prod.ext
    · apply Fin.ext
      exact hij.1
    · apply Fin.ext
      exact hij.2

end PalomarMSET25
