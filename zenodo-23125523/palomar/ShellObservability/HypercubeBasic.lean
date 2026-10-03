module

public import Mathlib

@[expose] public section

namespace ShellObservability.Hypercube

abbrev Cube (n : ℕ) := Fin n → Bool

def weight {n : ℕ} (x : Cube n) : ℕ := ∑ i, if x i then 1 else 0

def evenPrefix (n j : ℕ) : Cube n := fun i => decide (i.val < 2 * j)

lemma hamming_eq_sum {n : ℕ} (x y : Cube n) :
    hammingDist x y = ∑ i, if x i ≠ y i then 1 else 0 := by
  simp only [hammingDist, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma weight_eq_card {n : ℕ} (x : Cube n) :
    weight x = (Finset.univ.filter (fun i => x i = true)).card := by
  simp only [weight, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma hamming_weight_identity {n : ℕ} (x y : Cube n) :
    hammingDist x y + 2 * (∑ i, if x i && y i then 1 else 0) = weight x + weight y := by
  rw [hamming_eq_sum, weight, weight, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  cases x i <;> cases y i <;> simp

lemma hamming_weight_parity {n : ℕ} (x y : Cube n) :
    hammingDist x y % 2 = (weight x + weight y) % 2 := by
  have h := hamming_weight_identity x y
  omega

end ShellObservability.Hypercube
