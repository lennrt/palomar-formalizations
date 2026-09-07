import ShellTomography.UniformNecessity

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

theorem coeff_sum {α : Type*} (s : Finset α) (f : α → LP) (e : ℤ) :
    (∑ a ∈ s, f a : LP) e = ∑ a ∈ s, f a e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,coeff_zero]
  | @insert a s ha ih => simp only [Finset.sum_insert ha,coeff_add,ih]

def rows {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n) : LP :=
  ∑ j : Fin n, C (z (i,j)) * T (j.val : ℤ)

theorem rows_coeff {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n) (e : ℤ) :
    rows z i e = ∑ j : Fin n, if e = (j.val : ℤ) then z (i,j) else 0 := by
  unfold rows
  erw [coeff_sum]
  simp_rw [coeff_monomial]

theorem rows_coeff_at {n : ℕ} (z : SignedConfiguration (Grid n)) (i j : Fin n) :
    rows z i (j.val : ℤ) = z (i,j) := by
  rw [rows_coeff]
  simp only [Int.natCast_inj,← Fin.ext_iff]
  simp

theorem rows_supported {m : ℕ} (z : SignedConfiguration (Grid (m+1))) (i : Fin (m+1)) :
    Supported m (rows z i) := by
  intro e he
  rw [rows_coeff]
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg (by have := j.isLt; omega)]

theorem rows_injective {n : ℕ} : Function.Injective (rows (n := n)) := by
  intro z w h
  funext v
  have hh := congrArg (fun F : Fin n → LP => F v.1 (v.2.val : ℤ)) h
  simpa only [rows_coeff_at] using hh

theorem natAbsDiff_cast (i j : ℕ) : (natAbsDiff i j : ℤ) = |(i : ℤ)-j| := by
  unfold natAbsDiff
  by_cases h : i ≤ j
  · rw [abs_of_nonpos (by omega)]
    omega
  · rw [abs_of_nonneg (by omega)]
    omega

def leftDistance {n : ℕ} (i : ℕ) (v : Grid n) : ℕ := natAbsDiff i v.1.val + v.2.val
def rightDistance {m : ℕ} (i : ℕ) (v : Grid (m+1)) : ℕ :=
  natAbsDiff i v.1.val + (m-v.2.val)

theorem response_rows_coeff {n : ℕ} (z : SignedConfiguration (Grid n)) (i e : ℤ) :
    rowResponse (rows z) i e =
      ∑ a : Fin n, ∑ b : Fin n, if e = |i-(a.val : ℤ)| + b.val then z (a,b) else 0 := by
  unfold rowResponse
  erw [coeff_sum]
  simp_rw [coeff_shift,rows_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply propext
  omega

theorem reverse_rows_coeff {n : ℕ} (z : SignedConfiguration (Grid n)) (i e : ℤ) :
    reverseResponse (rows z) i e =
      ∑ a : Fin n, ∑ b : Fin n, if e = (b.val : ℤ)-|i-(a.val : ℤ)| then z (a,b) else 0 := by
  unfold reverseResponse
  erw [coeff_sum]
  simp_rw [coeff_shift,rows_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply propext
  omega

theorem left_coeff_shell {n : ℕ} (z : SignedConfiguration (Grid n)) (i : ℕ) (e : ℤ) :
    rowResponse (rows z) i e =
      if e < 0 then 0 else shellZ (fun (_ : Unit) v => leftDistance i v) z () e.toNat := by
  rw [response_rows_coeff]
  by_cases he : e < 0
  · rw [if_pos he]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (by have := abs_nonneg ((i : ℤ)-a.val); omega)]
  · rw [if_neg he]
    unfold shellZ leftDistance
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply propext
    dsimp only
    have h := natAbsDiff_cast i a.val
    have h' : (e.toNat : ℤ)=e := Int.toNat_of_nonneg (by omega)
    omega

theorem right_coeff_shell {m : ℕ} (z : SignedConfiguration (Grid (m+1))) (i : ℕ) (e : ℤ) :
    reverseResponse (rows z) i e = if (m : ℤ) < e then 0 else
      shellZ (fun (_ : Unit) v => rightDistance i v) z () ((m : ℤ)-e).toNat := by
  rw [reverse_rows_coeff]
  by_cases he : (m : ℤ) < e
  · rw [if_pos he]
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [if_neg (by have := abs_nonneg ((i : ℤ)-a.val); have := b.isLt; omega)]
  · rw [if_neg he]
    unfold shellZ rightDistance
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    apply propext
    dsimp only
    have h := natAbsDiff_cast i a.val
    have h' : (((m : ℤ)-e).toNat : ℤ)=(m : ℤ)-e := Int.toNat_of_nonneg (by omega)
    have := b.isLt
    omega

theorem alt_distance_formula {m : ℕ} (hm : 2 ≤ m) (k : AltSensor (m+1))
    (v : Grid (m+1)) :
    altDistance (by omega) k v = if Even (k.val+1) then rightDistance (k.val+1) v
      else leftDistance (k.val+1) v := by
  have hv := v.2.isLt
  by_cases he : Even (k.val+1)
  · have ho : ¬Odd (k.val+1) := Nat.not_odd_iff_even.mpr he
    simp [altDistance,altSensorVertex,manhattan,rightDistance,leftDistance,natAbsDiff,he,ho]
    omega
  · have ho : Odd (k.val+1) := Nat.not_even_iff_odd.mp he
    simp [altDistance,altSensorVertex,manhattan,rightDistance,leftDistance,natAbsDiff,he,ho]

theorem invisible_rows_alternating {m : ℕ} (hm : 2 ≤ m)
    (z : SignedConfiguration (Grid (m+1)))
    (hz : Invisible (altDistance (by omega)) z) : Alternating (rows z) := by
  intro i hi him
  let k : AltSensor (m+1) := ⟨i.val-1,by omega⟩
  have hk : k.val+1=i.val := by dsimp [k]; omega
  by_cases he : Even i.val
  · rw [if_pos he]
    apply LaurentPolynomial.ext
    intro e
    erw [right_coeff_shell,coeff_zero]
    split
    · rfl
    · rename_i hh
      have h := hz k ((m : ℤ)-e).toNat
      simpa only [shellZ,alt_distance_formula hm,hk,if_pos he] using h
  · rw [if_neg he]
    apply LaurentPolynomial.ext
    intro e
    erw [left_coeff_shell,coeff_zero]
    split
    · rfl
    · rename_i hh
      have h := hz k e.toNat
      simpa only [shellZ,alt_distance_formula hm,hk,if_neg he] using h

theorem rows_alternating_invisible {m : ℕ} (hm : 2 ≤ m)
    (z : SignedConfiguration (Grid (m+1)))
    (hz : Alternating (rows z)) : Invisible (altDistance (by omega)) z := by
  intro k r
  let i : Fin (m+1) := ⟨k.val+1,by have := k.isLt; omega⟩
  have hi : 0 < i.val := by dsimp [i]; omega
  have him : i.val < m := by dsimp [i]; have := k.isLt; omega
  have h := hz i hi him
  by_cases he : Even (k.val+1)
  · change (if Even (k.val+1) then _ else _) = 0 at h
    rw [if_pos he] at h
    have hc := congrArg (fun f : LP => f ((m : ℤ)-r)) h
    change reverseResponse (rows z) (k.val+1 : ℕ) ((m : ℤ)-r) = (0 : LP) ((m : ℤ)-r) at hc
    erw [right_coeff_shell,coeff_zero] at hc
    rw [if_neg (by omega)] at hc
    have e : ((m : ℤ)-((m : ℤ)-r)).toNat=r := by omega
    rw [e] at hc
    simpa only [shellZ,alt_distance_formula hm,if_pos he] using hc
  · change (if Even (k.val+1) then _ else _) = 0 at h
    rw [if_neg he] at h
    have hc := congrArg (fun f : LP => f (r : ℤ)) h
    change rowResponse (rows z) (k.val+1 : ℕ) (r : ℤ) = (0 : LP) (r : ℤ) at hc
    erw [left_coeff_shell,coeff_zero] at hc
    rw [if_neg (by omega)] at hc
    simpa only [Int.toNat_natCast,shellZ,alt_distance_formula hm,if_neg he] using hc

end ShellTomography.Uniform
