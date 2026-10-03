module

public import Mathlib

@[expose] public section

/-!
Tensor identities for signed shell reports and raw distance moments.

The distance functions are explicit inputs. On a Cartesian graph product the
required product distance is the sum of factor distances. This module verifies
the algebra after that standard metric bridge; it does not assert a new
Cartesian-distance theorem or the unformalized Hamming-capacity theorem.
-/

open scoped BigOperators

namespace ShellObservability.TensorMoments

variable {A B : Type*} [Fintype A] [Fintype B]

noncomputable def profile (distance : A → ℕ) (weight : A → ℤ) : Polynomial ℤ :=
  ∑ a, Polynomial.C (weight a) * Polynomial.X ^ distance a

def moment (distance : A → ℕ) (weight : A → ℤ) (k : ℕ) : ℤ :=
  ∑ a, weight a * (distance a : ℤ) ^ k

def tensor (a : A → ℤ) (b : B → ℤ) : A × B → ℤ :=
  fun p => a p.1 * b p.2

theorem profile_tensor (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) :
    profile (fun p : A × B => da p.1 + db p.2) (tensor a b) =
      profile da a * profile db b := by
  simp only [profile, tensor, Fintype.sum_prod_type, map_mul, pow_add,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

theorem profile_tensor_ne_zero_iff (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) :
    profile (fun p : A × B => da p.1 + db p.2) (tensor a b) ≠ 0 ↔
      profile da a ≠ 0 ∧ profile db b ≠ 0 := by
  rw [profile_tensor, mul_ne_zero_iff]

theorem moment_tensor (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) (k : ℕ) :
    moment (fun p : A × B => da p.1 + db p.2) (tensor a b) k =
      ∑ i ∈ Finset.range (k + 1),
        (k.choose i : ℤ) * moment da a i * moment db b (k - i) := by
  simp only [moment, tensor, Fintype.sum_prod_type, Nat.cast_add, add_pow]
  simp_rw [Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext x
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  ring

/-- Orders of moment vanishing add under Cartesian tensor products. -/
theorem moment_tensor_eq_zero_of_lt (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) (p q k : ℕ)
    (ha : ∀ i < p, moment da a i = 0)
    (hb : ∀ i < q, moment db b i = 0) (hk : k < p + q) :
    moment (fun v : A × B => da v.1 + db v.2) (tensor a b) k = 0 := by
  rw [moment_tensor]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hip : i < p
  · simp [ha i hip]
  · have hiq : k - i < q := by
      have hik : i ≤ k := by simpa using (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
      omega
    simp [hb (k - i) hiq]

/-- The first potentially surviving tensor moment has one binomial term. -/
theorem moment_tensor_leading (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) (p q : ℕ)
    (ha : ∀ i < p, moment da a i = 0)
    (hb : ∀ i < q, moment db b i = 0) :
    moment (fun v : A × B => da v.1 + db v.2) (tensor a b) (p + q) =
      ((p + q).choose p : ℤ) * moment da a p * moment db b q := by
  rw [moment_tensor, Finset.sum_eq_single p]
  · simp
  · intro i hi hne
    by_cases hip : i < p
    · simp [ha i hip]
    · have hiq : p + q - i < q := by
        have hik : i ≤ p + q := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        omega
      simp [hb (p + q - i) hiq]
  · intro hp
    exact (hp (Finset.mem_range.mpr (by omega))).elim

theorem moment_tensor_leading_ne_zero (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) (p q : ℕ)
    (ha : ∀ i < p, moment da a i = 0)
    (hb : ∀ i < q, moment db b i = 0)
    (hap : moment da a p ≠ 0) (hbq : moment db b q ≠ 0) :
    moment (fun v : A × B => da v.1 + db v.2) (tensor a b) (p + q) ≠ 0 := by
  rw [moment_tensor_leading da db a b p q ha hb]
  have hc : ((p + q).choose p : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : p ≤ p + q)))
  exact mul_ne_zero (mul_ne_zero hc hap) hbq

end ShellObservability.TensorMoments
