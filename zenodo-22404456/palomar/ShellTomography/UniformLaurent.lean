import ShellTomography.KernelDefinitions
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors

/-! Uniform row-response identities for alternating boundary sensing. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial
abbrev LP := LaurentPolynomial ℤ
local notation "q" => (T 1 : LP)
local notation "D" => (1 - T 2 : LP)

theorem D_ne_zero : D ≠ 0 := by
  intro h
  have he := congrArg (fun f : LP => f 0) ((T_zero (R := ℤ)).trans (sub_eq_zero.mp h))
  change (T (0 : ℤ) : LP) 0 = (T (2 : ℤ) : LP) 0 at he
  erw [T_apply,T_apply] at he
  norm_num at he

theorem green_scalar (i j : ℤ) :
    (1 + T 2 : LP) * T |i - j| - q * (T |i - 1 - j| + T |i + 1 - j|) =
      if i = j then D else 0 := by
  rcases lt_trichotomy i j with h | h | h
  · have h₀ : i - j ≤ 0 := by omega
    have h₁ : i - 1 - j ≤ 0 := by omega
    have h₂ : i + 1 - j ≤ 0 := by omega
    rw [if_neg (by omega), abs_of_nonpos h₀, abs_of_nonpos h₁, abs_of_nonpos h₂]
    simp only [add_mul, one_mul, mul_add, ← T_add]
    have e₁ : 2 + -(i-j) = 1 + -(i-1-j) := by omega
    have e₂ : 1 + -(i+1-j) = -(i-j) := by omega
    rw [e₁,e₂]
    ring
  · subst j
    norm_num [← T_add]
    ring_nf
    simp only [T_pow]
    norm_num
    ring
  · have h₀ : 0 ≤ i - j := by omega
    have h₁ : 0 ≤ i - 1 - j := by omega
    have h₂ : 0 ≤ i + 1 - j := by omega
    rw [if_neg (by omega), abs_of_nonneg h₀, abs_of_nonneg h₁, abs_of_nonneg h₂]
    simp only [add_mul, one_mul, mul_add, ← T_add]
    have e₁ : 2 + (i-j) = 1 + (i+1-j) := by omega
    have e₂ : 1 + (i-1-j) = i-j := by omega
    rw [e₁,e₂]
    ring

def rowResponse {n : ℕ} (F : Fin n → LP) (i : ℤ) : LP :=
  ∑ j, T |i - (j.val : ℤ)| * F j

def reverseResponse {n : ℕ} (F : Fin n → LP) (i : ℤ) : LP :=
  ∑ j, T (-|i - (j.val : ℤ)|) * F j

def lowerMoment {n : ℕ} (F : Fin n → LP) : LP := ∑ j, T (-(j.val : ℤ)) * F j
def upperMoment {n : ℕ} (F : Fin n → LP) : LP := ∑ j, T (j.val : ℤ) * F j

theorem green_row {n : ℕ} (F : Fin n → LP) (i : Fin n) :
    (1 + T 2 : LP) * rowResponse F i.val -
      q * (rowResponse F (i.val - 1) + rowResponse F (i.val + 1)) = D * F i := by
  classical
  calc
    _ = ∑ j : Fin n, ((1 + T 2 : LP) * T |(i.val : ℤ) - j.val| -
        q * (T |(i.val : ℤ) - 1 - j.val| + T |(i.val : ℤ) + 1 - j.val|)) * F j := by
      simp only [rowResponse, Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = D * F i := by
      simp_rw [green_scalar]
      simp only [Int.natCast_inj, ← Fin.ext_iff]
      simp

theorem response_pair {n : ℕ} (F : Fin n → LP) (i : ℤ) :
    rowResponse F i + reverseResponse F i =
      T i * lowerMoment F + T (-i) * upperMoment F := by
  classical
  simp only [rowResponse, reverseResponse, lowerMoment, upperMoment,
    Finset.mul_sum, ← Finset.sum_add_distrib, ← mul_assoc, ← T_add]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : 0 ≤ i - (j.val : ℤ)
  · rw [abs_of_nonneg h]
    have e₁ : i + -(j.val : ℤ) = i - j.val := by omega
    have e₂ : -i + (j.val : ℤ) = -(i - j.val) := by omega
    rw [e₁,e₂]
  · rw [abs_of_neg (by omega)]
    have e₁ : i + -(j.val : ℤ) = i - j.val := by omega
    have e₂ : -i + (j.val : ℤ) = -(i - j.val) := by omega
    rw [e₁,e₂,neg_neg,add_comm]

theorem response_zero {n : ℕ} (F : Fin n → LP) : rowResponse F 0 = upperMoment F := by
  simp [rowResponse, upperMoment]

theorem response_last {m : ℕ} (F : Fin (m+1) → LP) :
    rowResponse F m = T (m : ℤ) * lowerMoment F := by
  simp only [rowResponse, lowerMoment, Finset.mul_sum, ← mul_assoc, ← T_add]
  apply Finset.sum_congr rfl
  intro j _
  rw [abs_of_nonneg (by have := j.isLt; omega)]
  rfl

theorem green_end_scalar (j : ℤ) (hj : 0 ≤ j) :
    (T j : LP) - q * T |1 - j| = if j = 0 then D else 0 := by
  by_cases h : j = 0
  · subst j
    norm_num [← T_add]
  · rw [if_neg h, abs_of_nonpos (by omega), ← T_add]
    have e : 1 + -(1-j) = j := by omega
    rw [e,sub_self]

theorem green_first {m : ℕ} (F : Fin (m+1) → LP) :
    rowResponse F 0 - q * rowResponse F 1 = D * F 0 := by
  classical
  rw [response_zero]
  simp only [upperMoment, rowResponse, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin (m+1), ((T (j.val : ℤ) : LP) - q * T |1 - (j.val : ℤ)|) * F j := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = D * F 0 := by
      simp_rw [green_end_scalar _ (Nat.cast_nonneg _)]
      simp

theorem green_last {m : ℕ} (F : Fin (m+1) → LP) :
    rowResponse F m - q * rowResponse F ((m : ℤ)-1) = D * F (Fin.last m) := by
  classical
  simp only [rowResponse, Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ j : Fin (m+1), ((T ((m : ℤ) - j.val) : LP) -
        q * T |1 - ((m : ℤ) - j.val)|) * F j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [abs_of_nonneg (by have := j.isLt; omega)]
      have e : (m : ℤ)-1-j.val = -(1-((m : ℤ)-j.val)) := by omega
      rw [e,abs_neg]
      ring
    _ = D * F (Fin.last m) := by
      have step (j : Fin (m+1)) : (T ((m : ℤ)-j.val) : LP) -
          q * T |1-((m : ℤ)-j.val)| = if j = Fin.last m then D else 0 := by
        rw [green_end_scalar _ (by have := j.isLt; omega)]
        congr 1
        simp [sub_eq_zero, Fin.ext_iff, eq_comm]
      simp_rw [step]
      simp

/-- Alternating vanishing conditions on the interior boundary rows. -/
def Alternating {m : ℕ} (F : Fin (m+1) → LP) : Prop :=
  ∀ i : Fin (m+1), 0 < i.val → i.val < m →
    (if Even i.val then reverseResponse F i.val else rowResponse F i.val) = 0

theorem alternating_response {m : ℕ} (F : Fin (m+1) → LP) (hF : Alternating F)
    (i : Fin (m+1)) (hi : 0 < i.val) (him : i.val < m) :
    rowResponse F i.val = if Even i.val then
      T (i.val : ℤ) * lowerMoment F + T (-(i.val : ℤ)) * upperMoment F else 0 := by
  have h := hF i hi him
  by_cases he : Even i.val
  · simp only [he, if_pos] at h ⊢
    simpa [h] using response_pair F i.val
  · simpa [he] using h

theorem moment_upper {m : ℕ} (hm : 2 ≤ m) (F : Fin (m+1) → LP)
    (hF : Alternating F) : upperMoment F = D * F 0 := by
  have h₁ := alternating_response F hF ⟨1,by omega⟩ (by simp) (by simpa)
  norm_num at h₁
  simpa [h₁,response_zero] using green_first F

theorem solve_lower_moment (U B C : LP)
    (h : -q * (D * B + (T 2 * U + T (-2) * (D * B))) = D * C) :
    U = D * (T (-3) * (-C - (q + T (-1)) * B)) := by
  have hh := congrArg (fun f : LP => T (-3) * f) h
  simp only [mul_add, mul_sub, add_mul, sub_mul, mul_neg, neg_mul,
    ← mul_assoc, ← T_add, T_zero, mul_one, one_mul] at hh ⊢
  norm_num at hh ⊢
  linear_combination -hh

def firstRow {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) : LP := F ⟨1,by omega⟩
def seedA {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) : LP :=
  T (-3) * (-firstRow hm F - (q + T (-1)) * F 0)

theorem moment_lower {m : ℕ} (hm : 3 ≤ m) (F : Fin (m+1) → LP)
    (hF : Alternating F) : lowerMoment F = D * seedA (by omega) F := by
  have h₁ := alternating_response F hF ⟨1,by omega⟩ (by simp) (by change 1 < m; omega)
  have h₂ := alternating_response F hF ⟨2,by omega⟩ (by simp) (by change 2 < m; omega)
  norm_num at h₁ h₂
  have hg := green_row F ⟨1,by omega⟩
  norm_num at hg
  rw [h₁,h₂,response_zero,moment_upper (by omega) F hF] at hg
  simp only [mul_zero,zero_sub] at hg
  apply solve_lower_moment
  convert hg using 1 <;> ring

theorem neighbor_sum (i : ℤ) (U V : LP) :
    q * ((T (i-1) * U + T (-(i-1)) * V) +
      (T (i+1) * U + T (-(i+1)) * V)) =
    (1 + T 2 : LP) * (T i * U + T (-i) * V) := by
  simp only [mul_add,add_mul,one_mul,← mul_assoc,← T_add]
  have e₁ : 1+(i-1)=i := by omega
  have e₂ : 1+-(i-1)=2+-i := by omega
  have e₃ : 1+(i+1)=2+i := by omega
  have e₄ : 1+-(i+1)=-i := by omega
  rw [e₁,e₂,e₃,e₄]
  ring

theorem interior_scaled {m : ℕ} (F : Fin (m+1) → LP) (hF : Alternating F)
    (i : ℕ) (hi : 2 ≤ i) (him : i+2 ≤ m) :
    D * F ⟨i,by omega⟩ =
      (if Even i then (1 : LP) else -1) * (1+T 2) *
        (T (i : ℤ) * lowerMoment F + T (-(i : ℤ)) * upperMoment F) := by
  have h₀ := alternating_response F hF ⟨i,by omega⟩ (by change 0 < i; omega)
    (by change i < m; omega)
  have hm1 := alternating_response F hF ⟨i-1,by omega⟩ (by change 0 < i-1; omega)
    (by change i-1 < m; omega)
  have hp1 := alternating_response F hF ⟨i+1,by omega⟩ (by change 0 < i+1; omega)
    (by change i+1 < m; omega)
  have hg := green_row F ⟨i,by omega⟩
  simp only [Fin.val_mk, Nat.cast_sub (show 1 ≤ i by omega), Nat.cast_add,
    Nat.cast_one] at h₀ hm1 hp1 hg
  by_cases he : Even i
  · have hem : ¬Even (i-1) := by rw [Nat.even_iff] at he ⊢; omega
    have hep : ¬Even (i+1) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [he,hem,hep,ite_true,ite_false] at h₀ hm1 hp1 ⊢
    rw [h₀,hm1,hp1] at hg
    convert hg.symm using 1 <;> ring
  · have hem : Even (i-1) := by rw [Nat.even_iff] at he ⊢; omega
    have hep : Even (i+1) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [he,hem,hep,ite_true,ite_false] at h₀ hm1 hp1 ⊢
    rw [h₀,hm1,hp1] at hg
    rw [neighbor_sum] at hg
    convert hg.symm using 1 <;> ring

theorem interior_rows {m : ℕ} (hm : 3 ≤ m) (F : Fin (m+1) → LP) (hF : Alternating F)
    (i : ℕ) (hi : 2 ≤ i) (him : i+2 ≤ m) :
    F ⟨i,by omega⟩ = (if Even i then (1 : LP) else -1) * (1+T 2) *
      (T (i : ℤ) * seedA (by omega) F + T (-(i : ℤ)) * F 0) := by
  apply mul_left_cancel₀ D_ne_zero
  have h := interior_scaled F hF i hi him
  rw [moment_lower hm F hF, moment_upper (by omega) F hF] at h
  rw [h]
  ring

theorem last_scaled {m : ℕ} (hm : 2 ≤ m) (F : Fin (m+1) → LP) (hF : Alternating F) :
    D * F (Fin.last m) = if Even m then T (m : ℤ) * lowerMoment F
      else -T (2-(m : ℤ)) * upperMoment F := by
  have hr := alternating_response F hF ⟨m-1,by omega⟩ (by change 0 < m-1; omega)
    (by change m-1 < m; omega)
  simp only [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one] at hr
  have hg := green_last F
  rw [response_last, hr] at hg
  by_cases he : Even m
  · have he' : ¬Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
    simpa [he,he'] using hg.symm
  · have he' : Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [he,he',ite_true,ite_false] at hg ⊢
    rw [← hg]
    simp only [mul_add,← mul_assoc,← T_add]
    have e₁ : 1+((m : ℤ)-1)=(m : ℤ) := by omega
    have e₂ : 1+-((m : ℤ)-1)=2-(m : ℤ) := by omega
    rw [e₁,e₂]
    ring

theorem last_row {m : ℕ} (hm : 3 ≤ m) (F : Fin (m+1) → LP) (hF : Alternating F) :
    F (Fin.last m) = if Even m then T (m : ℤ) * seedA (by omega) F
      else -T (2-(m : ℤ)) * F 0 := by
  apply mul_left_cancel₀ D_ne_zero
  have h := last_scaled (by omega) F hF
  rw [moment_lower hm F hF, moment_upper (by omega) F hF] at h
  rw [h]
  split <;> ring

theorem penultimate_scaled {m : ℕ} (hm : 3 ≤ m) (F : Fin (m+1) → LP)
    (hF : Alternating F) :
    D * F ⟨m-1,by omega⟩ = if Even m then
      -(T ((m : ℤ)-1) + T ((m : ℤ)+1)) * lowerMoment F - T (3-(m : ℤ)) * upperMoment F
    else T ((m : ℤ)-1) * lowerMoment F +
      (T (1-(m : ℤ)) + T (3-(m : ℤ))) * upperMoment F := by
  have hr := alternating_response F hF ⟨m-1,by omega⟩ (by change 0 < m-1; omega)
    (by change m-1 < m; omega)
  have hs := alternating_response F hF ⟨m-2,by omega⟩ (by change 0 < m-2; omega)
    (by change m-2 < m; omega)
  have hg := green_row F ⟨m-1,by omega⟩
  simp only [Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_sub (show 2 ≤ m by omega),
    Nat.cast_one, Nat.cast_ofNat] at hr hs hg
  have e₁ : (m : ℤ)-1-1=(m : ℤ)-2 := by omega
  have e₂ : (m : ℤ)-1+1=(m : ℤ) := by omega
  rw [e₁,e₂,hr,hs,response_last] at hg
  by_cases he : Even m
  · have he' : ¬Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
    have he'' : Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [he,he',he'',ite_true,ite_false] at hg ⊢
    rw [← hg]
    simp only [mul_zero,zero_sub,mul_add,neg_mul,← mul_assoc,← T_add]
    have e₃ : 1+((m : ℤ)-2)=(m : ℤ)-1 := by omega
    have e₄ : 1+-((m : ℤ)-2)=3-(m : ℤ) := by omega
    have e₅ : 1+(m : ℤ)=(m : ℤ)+1 := by omega
    rw [e₃,e₄,e₅]
    ring
  · have he' : Even (m-1) := by rw [Nat.even_iff] at he ⊢; omega
    have he'' : ¬Even (m-2) := by rw [Nat.even_iff] at he ⊢; omega
    simp only [he,he',he'',ite_true,ite_false] at hg ⊢
    rw [← hg]
    simp only [zero_add,mul_add,add_mul,one_mul,← mul_assoc,← T_add]
    have e₃ : 2+((m : ℤ)-1)=(m : ℤ)+1 := by omega
    have e₄ : 2+-((m : ℤ)-1)=3-(m : ℤ) := by omega
    have e₅ : 1+(m : ℤ)=(m : ℤ)+1 := by omega
    have e₆ : -((m : ℤ)-1)=1-(m : ℤ) := by omega
    rw [e₃,e₄,e₅,e₆]
    ring

theorem penultimate_row {m : ℕ} (hm : 3 ≤ m) (F : Fin (m+1) → LP)
    (hF : Alternating F) :
    F ⟨m-1,by omega⟩ = if Even m then
      -(T ((m : ℤ)-1) + T ((m : ℤ)+1)) * seedA (by omega) F - T (3-(m : ℤ)) * F 0
    else T ((m : ℤ)-1) * seedA (by omega) F +
      (T (1-(m : ℤ)) + T (3-(m : ℤ))) * F 0 := by
  apply mul_left_cancel₀ D_ne_zero
  have h := penultimate_scaled hm F hF
  rw [moment_lower hm F hF, moment_upper (by omega) F hF] at h
  rw [h]
  split <;> ring

theorem first_row {m : ℕ} (hm : 1 ≤ m) (F : Fin (m+1) → LP) :
    firstRow hm F = -T 3 * seedA hm F - (q + T (-1)) * F 0 := by
  unfold seedA
  simp only [mul_sub,mul_neg,neg_mul,mul_add,← mul_assoc,← T_add]
  norm_num
  ring

theorem coeff_add (f g : LP) (e : ℤ) : (f+g) e = f e + g e := rfl
theorem coeff_sub (f g : LP) (e : ℤ) : (f-g) e = f e - g e := rfl
theorem coeff_neg (f : LP) (e : ℤ) : (-f) e = -f e := rfl
theorem coeff_zero (e : ℤ) : (0 : LP) e = 0 := rfl
theorem coeff_shift (k e : ℤ) (f : LP) : (T k * f : LP) e = f (e-k) := by
  unfold T
  rw [AddMonoidAlgebra.single_mul_apply,one_mul]
  congr 1
  omega

def Supported (m : ℕ) (f : LP) : Prop := ∀ e : ℤ, e < 0 ∨ (m : ℤ) < e → f e = 0

end ShellTomography.Uniform
