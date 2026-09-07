import ShellTomography.UniformInverse

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial
local notation "q" => (T 1 : LP)
local notation "D" => (1-T 2 : LP)

def rowFormula (m : ℕ) (A B : LP) (i : ℕ) : LP :=
  if i=0 then B
  else if i=1 then -T 3*A - (q+T (-1))*B
  else if i=m-1 then
    if Even m then -(T ((m : ℤ)-1)+T ((m : ℤ)+1))*A - T (3-(m : ℤ))*B
    else T ((m : ℤ)-1)*A + (T (1-(m : ℤ))+T (3-(m : ℤ)))*B
  else if i=m then if Even m then T (m : ℤ)*A else -T (2-(m : ℤ))*B
  else (if Even i then (1 : LP) else -1)*(1+T 2)*(T (i : ℤ)*A+T (-(i : ℤ))*B)

def plannedResponse (m : ℕ) (A B : LP) (i : ℕ) : LP :=
  if i=0 then D*B
  else if i=m then D*(T (m : ℤ)*A)
  else if Even i then D*(T (i : ℤ)*A+T (-(i : ℤ))*B) else 0

theorem tri_planned {m : ℕ} (hm : 5 ≤ m) (A B : LP) :
    tridiagonal (by omega) (fun i : Fin (m+1) => plannedResponse m A B i.val) =
      fun i => D*rowFormula m A B i.val := by
  funext ⟨i,hi⟩
  by_cases h₀ : i=0
  · subst i
    norm_num only [tridiagonal,plannedResponse,rowFormula,Nat.even_iff,Fin.val_mk,ite_true,ite_false,dite_true,dite_false,mul_zero,zero_mul,add_zero,zero_add,sub_zero,zero_sub,Nat.cast_one,Nat.cast_ofNat,show m ≠ 0 by omega,show 1 ≠ m by omega]
  by_cases h₁ : i=1
  · subst i
    norm_num only [tridiagonal,plannedResponse,rowFormula,Nat.even_iff,Fin.val_mk,ite_true,ite_false,dite_true,dite_false,mul_zero,zero_mul,add_zero,zero_add,sub_zero,zero_sub,Nat.cast_one,Nat.cast_ofNat,show 1 ≠ m by omega,show 2 ≠ m by omega]
    laurent_ring
  by_cases hp : i=m-1
  · subst i
    have hn₀ : m-1 ≠ 0 := by omega
    have hn₁ : m-1 ≠ 1 := by omega
    have hn₂ : m-1 ≠ m := by omega
    have he₁ : m-1-1=m-2 := by omega
    have he₂ : m-1+1=m := by omega
    simp only [tridiagonal,hn₀,hn₂,dite_false,he₁,he₂,
      rowFormula,hn₁,ite_false,ite_true]
    by_cases he : Even m
    · have hep : ¬Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
      have heq : Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
      simp only [plannedResponse,hn₀,hn₂,show m-2 ≠ 0 by omega,show m-2 ≠ m by omega,
        show m ≠ 0 by omega,he,hep,heq,eq_self_iff_true,ite_true,ite_false,
        Nat.cast_sub (show 2 ≤ m by omega),Nat.cast_ofNat,mul_zero,zero_sub]
      laurent_ring
    · have hep : Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
      have heq : ¬Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
      simp only [plannedResponse,hn₀,hn₂,show m-2 ≠ 0 by omega,show m-2 ≠ m by omega,
        show m ≠ 0 by omega,he,hep,heq,eq_self_iff_true,ite_true,ite_false,
        Nat.cast_sub (show 1 ≤ m by omega),Nat.cast_one,zero_add]
      laurent_ring
  by_cases hl : i=m
  · subst i
    have hn₀ : m ≠ 0 := by omega
    have hn₁ : m ≠ 1 := by omega
    have hn₂ : m ≠ m-1 := by omega
    simp only [tridiagonal,hn₀,dite_false,eq_self_iff_true,dite_true,rowFormula,hn₁,hn₂,ite_false,ite_true]
    by_cases he : Even m
    · have hep : ¬Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
      simp [plannedResponse,hn₀,show m-1 ≠ 0 by omega,Ne.symm hn₂,he,hep]
    · have hep : Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
      simp only [plannedResponse,hn₀,show m-1 ≠ 0 by omega,Ne.symm hn₂,he,hep,
        eq_self_iff_true,ite_true,ite_false,Nat.cast_sub (show 1 ≤ m by omega),Nat.cast_one]
      laurent_ring
  have him : i+2 ≤ m := by omega
  have hig : 2 ≤ i := by omega
  simp only [tridiagonal,h₀,hl,dite_false,rowFormula,h₁,hp,ite_false]
  by_cases he : Even i
  · have hem : ¬Even (i-1) := by rw [Nat.even_iff] at he ⊢; omega
    have hep : ¬Even (i+1) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [plannedResponse,h₀,hl,show i-1 ≠ 0 by omega,show i+1 ≠ 0 by omega,
      show i-1 ≠ m by omega,show i+1 ≠ m by omega,he,hem,hep,eq_self_iff_true,ite_true,ite_false,
      add_zero,mul_zero,sub_zero,one_mul]
    ring
  · have hem : Even (i-1) := by rw [Nat.even_iff] at he ⊢; omega
    have hep : Even (i+1) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [plannedResponse,h₀,hl,show i-1 ≠ 0 by omega,show i+1 ≠ 0 by omega,
      show i-1 ≠ m by omega,show i+1 ≠ m by omega,he,hem,hep,eq_self_iff_true,ite_true,ite_false,
      Nat.cast_sub (show 1 ≤ i by omega),Nat.cast_add,Nat.cast_one,mul_zero,zero_sub]
    laurent_ring

theorem rowFormula_response {m : ℕ} (hm : 5 ≤ m) (A B : LP) :
    (fun i : Fin (m+1) => rowResponse (fun j : Fin (m+1) => rowFormula m A B j.val) i.val) =
      fun i => plannedResponse m A B i.val := by
  apply tridiagonal_injective (by omega)
  rw [tridiagonal_response,tri_planned hm]

theorem rowFormula_alternating {m : ℕ} (hm : 5 ≤ m) (A B : LP) :
    Alternating (fun i : Fin (m+1) => rowFormula m A B i.val) := by
  let F : Fin (m+1) → LP := fun i => rowFormula m A B i.val
  have hL (i : Fin (m+1)) : rowResponse F i.val = plannedResponse m A B i.val :=
    congrFun (rowFormula_response hm A B) i
  have hv : upperMoment F=D*B := by
    have h := hL 0
    change rowResponse F 0 = plannedResponse m A B 0 at h
    simpa only [response_zero,plannedResponse,if_pos rfl] using h
  have hu : lowerMoment F=D*A := by
    apply mul_left_cancel₀ (isUnit_T (R := ℤ) (m : ℤ)).ne_zero
    have h := hL (Fin.last m)
    simp only [Fin.val_last,response_last,plannedResponse,show m ≠ 0 by omega,
      ite_false,eq_self_iff_true,ite_true] at h
    rw [h]
    ring
  intro i hi him
  have h := hL i
  simp only [plannedResponse,show i.val ≠ 0 by omega,show i.val ≠ m by omega,ite_false] at h
  by_cases he : Even i.val
  · rw [if_pos he]
    rw [if_pos he] at h
    have hp := response_pair F i.val
    rw [h,hu,hv] at hp
    linear_combination hp
  · rw [if_neg he]
    simpa only [if_neg he] using h

theorem rowFormula_necessary {m : ℕ} (hm : 5 ≤ m) (F : Fin (m+1) → LP)
    (hF : Alternating F) :
    F = fun i => rowFormula m (seedA (by omega) F) (F 0) i.val := by
  funext ⟨i,hi⟩
  by_cases h₀ : i=0
  · subst i
    simp [rowFormula]
  by_cases h₁ : i=1
  · subst i
    simpa only [rowFormula,show (1 : ℕ) ≠ 0 by omega,ite_false,eq_self_iff_true,ite_true]
      using first_row (by omega) F
  by_cases hp : i=m-1
  · subst i
    simpa only [rowFormula,show m-1 ≠ 0 by omega,show m-1 ≠ 1 by omega,
      ite_false,eq_self_iff_true,ite_true] using penultimate_row (by omega) F hF
  by_cases hl : i=m
  · subst i
    simpa only [rowFormula,show m ≠ 0 by omega,show m ≠ 1 by omega,
      show m ≠ m-1 by omega,ite_false,eq_self_iff_true,ite_true] using last_row (by omega) F hF
  simpa only [rowFormula,h₀,h₁,hp,hl,ite_false] using
    interior_rows (by omega) F hF i (by omega) (by omega)

end ShellTomography.Uniform
