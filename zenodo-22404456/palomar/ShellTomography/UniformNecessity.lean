import ShellTomography.UniformSupport

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial
local notation "q" => (T 1 : LP)

macro "laurent_ring" : tactic => `(tactic|
  (simp only [mul_add,add_mul,mul_sub,sub_mul,mul_neg,neg_mul,
    one_mul,mul_one,← mul_assoc,← T_add,T_pow]
   <;> ring_nf <;> norm_num <;> ring_nf))

theorem seedA_of_even {m : ℕ} (hm : 3 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    seedA (by omega) F = T (-(m : ℤ)) * F (Fin.last m) := by
  have h := last_row hm F hF
  rw [if_pos he] at h
  rw [h]
  laurent_ring

theorem odd_first_identity {m : ℕ} (hm : 3 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    firstRow (by omega) F = oddFirst m (F 0) (F (Fin.last m)) := by
  rw [first_row,seedA_of_even hm he F hF]
  unfold oddFirst
  laurent_ring

theorem odd_penultimate_identity {m : ℕ} (hm : 3 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨m-1,by omega⟩ = oddFirst m (F (Fin.last m)) (F 0) := by
  rw [penultimate_row hm F hF,if_pos he,seedA_of_even hm he F hF]
  unfold oddFirst
  laurent_ring

theorem odd_second_identity {m : ℕ} (hm : 4 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨2,by omega⟩ = oddSecond m (F 0) (F (Fin.last m)) := by
  rw [interior_rows (by omega) F hF 2 (by omega) (by omega),seedA_of_even (by omega) he F hF]
  norm_num only [show Even 2 by decide,ite_true,Nat.cast_ofNat,one_mul]
  unfold oddSecond
  laurent_ring

theorem odd_prepenultimate_identity {m : ℕ} (hm : 4 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨m-2,by omega⟩ = oddSecond m (F (Fin.last m)) (F 0) := by
  rw [interior_rows (by omega) F hF (m-2) (by omega) (by omega),
    seedA_of_even (by omega) he F hF]
  have he' : Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
  simp only [if_pos he',one_mul,Nat.cast_sub (show 2 ≤ m by omega),Nat.cast_ofNat]
  unfold oddSecond
  laurent_ring

theorem odd_boundary_two_support {m : ℕ} (hm : 6 ≤ m) (he : Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) (hs : ∀ i, Supported m (F i)) :
    (∀ e : ℤ, e ≠ (m : ℤ)-2 → e ≠ (m : ℤ)-1 → F 0 e = 0) ∧
    (∀ e : ℤ, e ≠ (m : ℤ)-2 → e ≠ (m : ℤ)-1 → F (Fin.last m) e = 0) := by
  apply odd_two_support hm (F 0) (F (Fin.last m)) (hs 0) (hs (Fin.last m))
  · rw [← odd_first_identity (by omega) he F hF]
    exact hs ⟨1,by omega⟩
  · rw [← odd_penultimate_identity (by omega) he F hF]
    exact hs ⟨m-1,by omega⟩
  · rw [← odd_second_identity (by omega) he F hF]
    exact hs ⟨2,by omega⟩
  · rw [← odd_prepenultimate_identity (by omega) he F hF]
    exact hs ⟨m-2,by omega⟩

def seedJ {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) : LP :=
  -firstRow hm F - (q+T (-1))*F 0

theorem seedA_J {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) :
    seedA hm F = T (-3) * seedJ hm F := rfl

theorem even_first_identity {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) :
    firstRow hm F = evenFirst (F 0) (seedJ hm F) := by
  unfold evenFirst seedJ
  ring

theorem even_last_identity {m : ℕ} (hm : 3 ≤ m) (he : ¬Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F (Fin.last m) = evenLast m (F 0) := by
  simpa only [if_neg he,evenLast] using last_row hm F hF

theorem even_penultimate_identity {m : ℕ} (hm : 3 ≤ m) (he : ¬Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨m-1,by omega⟩ = evenPenultimate m (F 0) (seedJ (by omega) F) := by
  rw [penultimate_row hm F hF,if_neg he,seedA_J]
  unfold evenPenultimate
  laurent_ring

theorem even_second_identity {m : ℕ} (hm : 4 ≤ m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨2,by omega⟩ = evenSecond (F 0) (seedJ (by omega) F) := by
  rw [interior_rows (by omega) F hF 2 (by omega) (by omega),seedA_J]
  norm_num only [show Even 2 by decide,ite_true,Nat.cast_ofNat,one_mul]
  unfold evenSecond
  laurent_ring

theorem even_prepenultimate_identity {m : ℕ} (hm : 4 ≤ m) (he : ¬Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) :
    F ⟨m-2,by omega⟩ = evenPrePenultimate m (F 0) (seedJ (by omega) F) := by
  rw [interior_rows (by omega) F hF (m-2) (by omega) (by omega),seedA_J]
  have he' : ¬Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
  simp only [if_neg he',Nat.cast_sub (show 2 ≤ m by omega),Nat.cast_ofNat]
  unfold evenPrePenultimate
  laurent_ring

theorem even_boundary_four_support {m : ℕ} (hm : 5 ≤ m) (he : ¬Even m)
    (F : Fin (m+1) → LP) (hF : Alternating F) (hs : ∀ i, Supported m (F i)) :
    (∀ e : ℤ, e ≠ (m : ℤ)-1 → F 0 e = 0) ∧
    (∀ e : ℤ, e ≠ 1 → e ≠ 2 → e ≠ 3 → seedJ (by omega) F e = 0) := by
  apply even_boundary_support hm (F 0) (seedJ (by omega) F) (hs 0)
  · rw [← even_first_identity]
    exact hs ⟨1,by omega⟩
  · rw [← even_last_identity (by omega) he F hF]
    exact hs (Fin.last m)
  · rw [← even_penultimate_identity (by omega) he F hF]
    exact hs ⟨m-1,by omega⟩
  · rw [← even_second_identity (by omega) F hF]
    exact hs ⟨2,by omega⟩
  · rw [← even_prepenultimate_identity (by omega) he F hF]
    exact hs ⟨m-2,by omega⟩

end ShellTomography.Uniform
