module

public import LossyShell.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Order.Interval.Finset.Fin

/-!
# Ranks of surviving relays and landing probabilities

`landProb p i k` is the probability that the relay at true distance `i + 1` survives and is
heard at hop distance `k + 1`; `pairProb p i j k l` is the joint version for two relays.
The recovery theorem uses only five elementary facts about these numbers:

* a relay is never heard further out than its true distance (`landProb_eq_zero_of_lt`);
* it is heard at its true distance exactly when every relay up to it survives
  (`landProb_self`);
* two different surviving relays are never heard at the same distance (`pairProb_diag`);
* one relay is heard at one distance (`pairProb_same`);
* if the relay at true distance `m + 1` is heard at distance `m + 1`, every earlier relay is
  heard at its own true distance (`pairProb_top`).
-/

@[expose] public section

namespace LossyShell

open Finset

variable {n : ℕ}

/-! ### Ranks -/

lemma aliveRank_filter_subset (ω : Pattern n) (i : Fin n) :
    (univ.filter fun j : Fin n => j ≤ i ∧ ω j = true) ⊆ Iic i := by
  intro j hj
  simp only [mem_filter, mem_univ, true_and] at hj
  simpa using hj.1

lemma aliveRank_le (ω : Pattern n) (i : Fin n) : aliveRank ω i ≤ i.val + 1 := by
  unfold aliveRank
  calc _ ≤ (Iic i).card := card_le_card (aliveRank_filter_subset ω i)
    _ = i.val + 1 := by simp

lemma aliveRank_eq_succ_iff (ω : Pattern n) (i : Fin n) :
    aliveRank ω i = i.val + 1 ↔ ∀ j, j ≤ i → ω j = true := by
  constructor
  · intro h j hj
    have hsub := aliveRank_filter_subset ω i
    have hcard : (Iic i).card ≤ (univ.filter fun j : Fin n => j ≤ i ∧ ω j = true).card := by
      rw [Fin.card_Iic]
      exact h.ge
    have heq := eq_of_subset_of_card_le hsub hcard
    have : j ∈ (univ.filter fun j : Fin n => j ≤ i ∧ ω j = true) := by
      rw [heq]; simpa using hj
    simp only [mem_filter, mem_univ, true_and] at this
    exact this.2
  · intro h
    unfold aliveRank
    have : (univ.filter fun j : Fin n => j ≤ i ∧ ω j = true) = Iic i := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_Iic]
      exact ⟨fun hj => hj.1, fun hj => ⟨hj, h j hj⟩⟩
    rw [this]
    simp

lemma aliveRank_pos {ω : Pattern n} {i : Fin n} (hi : ω i = true) : 1 ≤ aliveRank ω i := by
  unfold aliveRank
  apply card_pos.mpr
  exact ⟨i, by simp [hi]⟩

lemma aliveRank_lt_of_lt {ω : Pattern n} {i j : Fin n} (hij : i < j) (hj : ω j = true) :
    aliveRank ω i < aliveRank ω j := by
  unfold aliveRank
  apply card_lt_card
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [mem_filter, mem_univ, true_and] at ht ⊢
    exact ⟨le_trans ht.1 hij.le, ht.2⟩
  · intro hsub
    have : j ∈ (univ.filter fun t : Fin n => t ≤ i ∧ ω t = true) :=
      hsub (by simp [hj])
    simp only [mem_filter, mem_univ, true_and] at this
    exact absurd this.1 (not_le.mpr hij)

lemma aliveRank_all_true (i : Fin n) : aliveRank (fun _ : Fin n => true) i = i.val + 1 :=
  (aliveRank_eq_succ_iff _ i).mpr fun _ _ => rfl

/-! ### Weights -/

variable {K : Type*} [CommRing K]

/-- Sums over failure patterns of coordinatewise products factor. -/
lemma sum_pattern_prod (f : Fin n → Bool → K) :
    ∑ ω : Pattern n, ∏ i, f i (ω i) = ∏ i, (f i true + f i false) := by
  rw [← Fintype.prod_sum]
  simp

lemma sum_patternWeight (p : K) : ∑ ω : Pattern n, patternWeight p ω = 1 := by
  unfold patternWeight
  rw [sum_pattern_prod (fun _ b => if b = true then p else 1 - p)]
  simp

/-- The probability that every relay up to and including `i` survives. -/
lemma sum_weight_prefix_alive (p : K) (i : Fin n) :
    (∑ ω : Pattern n, if (∀ j, j ≤ i → ω j = true) then patternWeight p ω else 0) =
      p ^ (i.val + 1) := by
  have hrewrite : ∀ ω : Pattern n,
      (if (∀ j, j ≤ i → ω j = true) then patternWeight p ω else 0) =
        ∏ j, (if (j ≤ i → ω j = true) then (if ω j = true then p else 1 - p) else 0) := by
    intro ω
    rw [Fintype.prod_ite_zero]
    split_ifs <;> rfl
  simp_rw [hrewrite]
  rw [sum_pattern_prod
    (fun j b => if (j ≤ i → b = true) then (if b = true then p else 1 - p) else 0)]
  calc _ = ∏ j : Fin n, (if j ≤ i then p else 1) := by
        apply prod_congr rfl
        intro j _
        by_cases hj : j ≤ i <;> simp [hj]
    _ = p ^ (i.val + 1) := by
        rw [Finset.prod_ite, prod_const, prod_const_one, mul_one]
        congr 1
        have : (univ.filter fun j : Fin n => j ≤ i) = Iic i := by
          ext j; simp
        rw [this]
        simp

/-! ### Landing probabilities -/

/-- The probability that the relay at true distance `i + 1` survives and is heard at hop
distance `k + 1`. -/
def landProb (p : K) (i : Fin n) (k : ℕ) : K :=
  ∑ ω : Pattern n, if ω i = true ∧ aliveRank ω i = k + 1 then patternWeight p ω else 0

/-- The probability that the relays at true distances `i + 1` and `j + 1` are heard at hop
distances `k + 1` and `l + 1` respectively. -/
def pairProb (p : K) (i j : Fin n) (k l : ℕ) : K :=
  ∑ ω : Pattern n,
    if (ω i = true ∧ aliveRank ω i = k + 1) ∧ (ω j = true ∧ aliveRank ω j = l + 1) then
      patternWeight p ω else 0

lemma landProb_eq_zero_of_lt (p : K) {i : Fin n} {k : ℕ} (h : i.val < k) :
    landProb p i k = 0 := by
  unfold landProb
  apply sum_eq_zero
  intro ω _
  rw [ite_eq_right]
  rintro ⟨_, hr⟩
  have := aliveRank_le ω i
  omega

lemma landProb_self (p : K) (i : Fin n) : landProb p i i.val = p ^ (i.val + 1) := by
  rw [← sum_weight_prefix_alive p i]
  unfold landProb
  apply sum_congr rfl
  intro ω _
  refine if_congr ?_ rfl rfl
  rw [aliveRank_eq_succ_iff]
  exact ⟨fun h => h.2, fun h => ⟨h i le_rfl, h⟩⟩

lemma pairProb_eq_zero_of_lt (p : K) (i : Fin n) {j : Fin n} (k : ℕ) {l : ℕ}
    (h : j.val < l) : pairProb p i j k l = 0 := by
  unfold pairProb
  apply sum_eq_zero
  intro ω _
  rw [ite_eq_right]
  rintro ⟨_, _, hr⟩
  have := aliveRank_le ω j
  omega

lemma pairProb_diag (p : K) {i j : Fin n} (hij : i ≠ j) (k : ℕ) : pairProb p i j k k = 0 := by
  unfold pairProb
  apply sum_eq_zero
  intro ω _
  rw [ite_eq_right]
  rintro ⟨⟨hi, hri⟩, ⟨hj, hrj⟩⟩
  rcases lt_or_gt_of_ne hij with h | h
  · have := aliveRank_lt_of_lt h hj; omega
  · have := aliveRank_lt_of_lt h hi; omega

lemma pairProb_same (p : K) (i : Fin n) (k l : ℕ) :
    pairProb p i i k l = if k = l then landProb p i k else 0 := by
  unfold pairProb landProb
  split_ifs with hkl
  · subst hkl
    apply sum_congr rfl
    intro ω _
    simp only [and_self]
  · apply sum_eq_zero
    intro ω _
    rw [ite_eq_right]
    rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    omega

lemma pairProb_top (p : K) {i m : Fin n} (him : i < m) (k : ℕ) :
    pairProb p i m k m.val = if k = i.val then p ^ (m.val + 1) else 0 := by
  rw [← sum_weight_prefix_alive p m]
  unfold pairProb
  split_ifs with hk
  · subst hk
    apply sum_congr rfl
    intro ω _
    refine if_congr ?_ rfl rfl
    rw [aliveRank_eq_succ_iff ω m]
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · intro h
      have hi : ∀ j, j ≤ i → ω j = true := fun j hj => h j (le_trans hj him.le)
      exact ⟨⟨hi i le_rfl, (aliveRank_eq_succ_iff ω i).mpr hi⟩, h m le_rfl, h⟩
  · apply sum_eq_zero
    intro ω _
    rw [ite_eq_right]
    rintro ⟨⟨_, hri⟩, _, hrm⟩
    rw [aliveRank_eq_succ_iff ω m] at hrm
    have hi : ∀ j, j ≤ i → ω j = true := fun j hj => hrm j (le_trans hj him.le)
    rw [(aliveRank_eq_succ_iff ω i).mpr hi] at hri
    exact hk (by omega)

end LossyShell
