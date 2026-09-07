import ShellTomography.UniformGridBridge
import Mathlib.Order.Interval.Finset.Fin

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

def rowNorm {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n) : ℕ :=
  ∑ j, (z (i,j)).natAbs
def totalNorm {n : ℕ} (z : SignedConfiguration (Grid n)) : ℕ := ∑ i, rowNorm z i

theorem entry_norm_le {n : ℕ} (z : SignedConfiguration (Grid n)) (i j : Fin n) :
    (z (i,j)).natAbs ≤ rowNorm z i := by
  unfold rowNorm
  exact Finset.single_le_sum (f := fun j => (z (i,j)).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

theorem rowNorm_zero_iff {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n) :
    rowNorm z i=0 ↔ rows z i=0 := by
  constructor
  · intro h
    have hz (j : Fin n) : z (i,j)=0 := by
      have hj := entry_norm_le z i j
      rw [h] at hj
      exact Int.natAbs_eq_zero.mp (by omega)
    simp [rows,hz]
  · intro h
    have hz (j : Fin n) : z (i,j)=0 := by
      have hh := congrArg (fun f : LP => f (j.val : ℤ)) h
      simpa only [rows_coeff_at,coeff_zero] using hh
    simp [rowNorm,hz]

theorem natAbs_positive_identity (a : ℤ) : (a.natAbs : ℤ)=2*(a.toNat : ℤ)-a := by omega

theorem rowNorm_even {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n)
    (he : Even (∑ j, z (i,j))) : Even (rowNorm z i) := by
  obtain ⟨k,hk⟩ := he
  have h : (rowNorm z i : ℤ) = 2*(∑ j : Fin n, (z (i,j)).toNat : ℕ) - ∑ j, z (i,j) := by
    simp only [rowNorm,Nat.cast_sum]
    simp_rw [natAbs_positive_identity]
    rw [Finset.sum_sub_distrib,Finset.mul_sum]
  have hint : Even (rowNorm z i : ℤ) := by
    refine ⟨(∑ j : Fin n, (z (i,j)).toNat : ℕ)-k,?_⟩
    rw [h,hk]
    ring
  exact_mod_cast hint

theorem rowNorm_ge_two {n : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n)
    (hz : rows z i ≠ 0) (he : Even (∑ j, z (i,j))) : 2 ≤ rowNorm z i := by
  have hne : rowNorm z i ≠ 0 := fun h => hz ((rowNorm_zero_iff z i).mp h)
  have h := rowNorm_even z i he
  rw [Nat.even_iff] at h
  omega

theorem totalNorm_mass {n : ℕ} (z : SignedConfiguration (Grid n))
    (hb : mass (positive z)=mass (negative z)) : totalNorm z=2*mass (positive z) := by
  have hp : totalNorm z=mass (positive z)+mass (negative z) := by
    unfold totalNorm rowNorm mass positive negative
    rw [Fintype.sum_prod_type,Fintype.sum_prod_type,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    omega
  omega

def interiorSet {m : ℕ} (hm : 5 ≤ m) : Finset (Fin (m+1)) :=
  Finset.Icc ⟨2,by omega⟩ ⟨m-2,by omega⟩

theorem mem_interiorSet {m : ℕ} (hm : 5 ≤ m) (i : Fin (m+1)) :
    i ∈ interiorSet hm ↔ 2 ≤ i.val ∧ i.val+2 ≤ m := by
  simp only [interiorSet,Finset.mem_Icc,Fin.le_iff_val_le_val]
  omega

theorem card_interiorSet {m : ℕ} (hm : 5 ≤ m) : (interiorSet hm).card=m-3 := by
  rw [interiorSet,Fin.card_Icc]
  dsimp only
  omega

def boundarySet {m : ℕ} (hm : 5 ≤ m) : Finset (Fin (m+1)) :=
  {0,⟨1,by omega⟩,⟨m-1,by omega⟩,Fin.last m}

def boundaryNorm {m : ℕ} (hm : 5 ≤ m) (z : SignedConfiguration (Grid (m+1))) : ℕ :=
  rowNorm z 0 + rowNorm z ⟨1,by omega⟩ + rowNorm z ⟨m-1,by omega⟩ + rowNorm z (Fin.last m)

theorem totalNorm_partition {m : ℕ} (hm : 5 ≤ m) (z : SignedConfiguration (Grid (m+1))) :
    totalNorm z=boundaryNorm hm z + ∑ i ∈ interiorSet hm, rowNorm z i := by
  classical
  have hd : Disjoint (boundarySet hm) (interiorSet hm) := by
    rw [Finset.disjoint_left]
    intro i hi hj
    rw [mem_interiorSet] at hj
    simp only [boundarySet,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,Fin.val_zero,Fin.val_last] at hi
    try dsimp only at hi
    omega
  have hu : boundarySet hm ∪ interiorSet hm=Finset.univ := by
    ext i
    simp only [Finset.mem_union,Finset.mem_univ,iff_true,mem_interiorSet,
      boundarySet,Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,Fin.val_zero,Fin.val_last]
    try dsimp only
    have := i.isLt
    omega
  have hb : (∑ i ∈ boundarySet hm, rowNorm z i)=boundaryNorm hm z := by
    unfold boundarySet boundaryNorm
    rw [Finset.sum_insert,Finset.sum_insert,Finset.sum_insert,Finset.sum_singleton]
    · omega
    all_goals
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or,Fin.ext_iff,Fin.val_zero,Fin.val_last]
      omega
  unfold totalNorm
  rw [← hu,Finset.sum_union hd,hb]

theorem sum_norm_lower {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℕ)
    (h : ∀ i ∈ s, 2 ≤ f i) : 2*s.card ≤ ∑ i ∈ s, f i := by
  have hh := Finset.sum_le_sum h
  simpa [mul_comm] using hh

theorem sum_norm_lower_one_exception {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℕ)
    (h : ∀ i ∈ s, f i=0 ∨ 2 ≤ f i)
    (hu : ∀ i ∈ s, ∀ j ∈ s, f i=0 → f j=0 → i=j) :
    2*(s.card-1) ≤ ∑ i ∈ s, f i := by
  classical
  by_cases he : ∃ i ∈ s, f i=0
  · obtain ⟨i,hi,hi₀⟩ := he
    have hb : ∀ j ∈ s.erase i, 2 ≤ f j := by
      intro j hj
      have hj' := Finset.mem_erase.mp hj
      rcases h j hj'.2 with hz | hz
      · exact False.elim (hj'.1 (hu j hj'.2 i hi hz hi₀))
      · exact hz
    have hl := sum_norm_lower (s.erase i) f hb
    rw [Finset.card_erase_of_mem hi] at hl
    exact hl.trans (Finset.sum_le_sum_of_subset (Finset.erase_subset i s))
  · have hh : ∀ i ∈ s, 2 ≤ f i := by
      intro i hi
      rcases h i hi with hz | hz
      · exact False.elim (he ⟨i,hi,hz⟩)
      · exact hz
    have hl := sum_norm_lower s f hh
    omega

end ShellTomography.Uniform
