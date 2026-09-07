import ShellTomography.UniformLaurent

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial
local notation "q" => (T 1 : LP)

def oddFirst (m : ℕ) (B C : LP) : LP :=
  -T (3-(m : ℤ)) * C - (q+T (-1)) * B
def oddSecond (m : ℕ) (B C : LP) : LP :=
  (1+T 2) * (T (2-(m : ℤ)) * C + T (-2) * B)

theorem oddFirst_coeff (m : ℕ) (B C : LP) (e : ℤ) :
    oddFirst m B C e = -C (e-3+m) - B (e-1) - B (e+1) := by
  unfold oddFirst
  simp only [neg_mul,add_mul,coeff_sub,coeff_neg,coeff_add,coeff_shift]
  ring_nf

theorem oddSecond_coeff (m : ℕ) (B C : LP) (e : ℤ) :
    oddSecond m B C e = C (e-2+m) + B (e+2) + C (e-4+m) + B e := by
  unfold oddSecond
  simp only [add_mul,one_mul,mul_add,coeff_add,coeff_shift]
  ring_nf

theorem odd_top_zero {m : ℕ} (hm : 6 ≤ m) (B C : LP)
    (hB : Supported m B) (hC : Supported m C) (hR : Supported m (oddFirst m B C)) :
    B (m : ℤ) = 0 := by
  have hr := hR (m+1) (Or.inr (by omega))
  rw [oddFirst_coeff] at hr
  have hc := hC ((m : ℤ)+1-3+m) (Or.inr (by omega))
  have hb := hB ((m : ℤ)+1+1) (Or.inr (by omega))
  have e : (m : ℤ)+1-1=(m : ℤ) := by omega
  rw [hc,hb,e] at hr
  omega

theorem odd_low_zero {m : ℕ} (hm : 6 ≤ m) (B C : LP)
    (hB : Supported m B) (hR : Supported m (oddFirst m B C))
    (j : ℤ) (hj : j ≤ (m : ℤ)-5) : C j = 0 := by
  have hr := hR (j+3-m) (Or.inl (by omega))
  rw [oddFirst_coeff] at hr
  have hb₁ := hB (j+3-m-1) (Or.inl (by omega))
  have hb₂ := hB (j+3-m+1) (Or.inl (by omega))
  have e : j+3-m-3+m=j := by omega
  rw [hb₁,hb₂,e] at hr
  omega

theorem odd_middle_zero {m : ℕ} (hm : 6 ≤ m) (B C : LP)
    (hB : Supported m B) (hb₀ : B 0 = 0)
    (hR : Supported m (oddFirst m B C)) : C ((m : ℤ)-4) = 0 := by
  have hr := hR (-1) (Or.inl (by omega))
  rw [oddFirst_coeff] at hr
  have hb := hB (-2) (Or.inl (by omega))
  have e : (-1 : ℤ)-3+m=(m : ℤ)-4 := by omega
  rw [e] at hr
  norm_num only at hr
  omega

theorem odd_last_low_zero {m : ℕ} (B C : LP)
    (hb₁ : B 1 = 0) (hbm : B (-1) = 0) (hc : C ((m : ℤ)-5) = 0)
    (hR : Supported m (oddSecond m B C)) : C ((m : ℤ)-3) = 0 := by
  have hr := hR (-1) (Or.inl (by omega))
  rw [oddSecond_coeff] at hr
  have e₁ : (-1 : ℤ)-2+m=(m : ℤ)-3 := by omega
  have e₂ : (-1 : ℤ)-4+m=(m : ℤ)-5 := by omega
  rw [e₁,e₂] at hr
  norm_num only at hr
  omega

theorem odd_two_support {m : ℕ} (hm : 6 ≤ m) (B C : LP)
    (hB : Supported m B) (hC : Supported m C)
    (hR : Supported m (oddFirst m B C)) (hS : Supported m (oddFirst m C B))
    (hP : Supported m (oddSecond m B C)) (hQ : Supported m (oddSecond m C B)) :
    (∀ e : ℤ, e ≠ (m : ℤ)-2 → e ≠ (m : ℤ)-1 → B e = 0) ∧
    (∀ e : ℤ, e ≠ (m : ℤ)-2 → e ≠ (m : ℤ)-1 → C e = 0) := by
  have bl := odd_low_zero hm C B hC hS
  have cl := odd_low_zero hm B C hB hR
  have bmid := odd_middle_zero hm C B hC (cl 0 (by omega)) hS
  have cmid := odd_middle_zero hm B C hB (bl 0 (by omega)) hR
  have bnext := odd_last_low_zero C B (cl 1 (by omega)) (hC (-1) (Or.inl (by omega)))
    (bl ((m : ℤ)-5) (by omega)) hQ
  have cnext := odd_last_low_zero B C (bl 1 (by omega)) (hB (-1) (Or.inl (by omega)))
    (cl ((m : ℤ)-5) (by omega)) hP
  have bt := odd_top_zero hm B C hB hC hR
  have ct := odd_top_zero hm C B hC hB hS
  constructor
  · intro e he₂ he₁
    by_cases he : (m : ℤ) < e
    · exact hB e (Or.inr he)
    by_cases hl : e ≤ (m : ℤ)-5
    · exact bl e hl
    have : e = (m : ℤ)-4 ∨ e = (m : ℤ)-3 ∨ e = (m : ℤ) := by omega
    rcases this with rfl | rfl | rfl <;> assumption
  · intro e he₂ he₁
    by_cases he : (m : ℤ) < e
    · exact hC e (Or.inr he)
    by_cases hl : e ≤ (m : ℤ)-5
    · exact cl e hl
    have : e = (m : ℤ)-4 ∨ e = (m : ℤ)-3 ∨ e = (m : ℤ) := by omega
    rcases this with rfl | rfl | rfl <;> assumption

theorem coeff_monomial (a e k : ℤ) : (C a * T k : LP) e = if e = k then a else 0 := by
  rw [mul_comm,coeff_shift,C_apply]
  simp [sub_eq_zero]

theorem two_coefficients (f : LP) (j k : ℤ) (hjk : j ≠ k)
    (h : ∀ e : ℤ, e ≠ j → e ≠ k → f e = 0) :
    f = C (f j) * T j + C (f k) * T k := by
  apply LaurentPolynomial.ext
  intro e
  erw [coeff_add,coeff_monomial,coeff_monomial]
  by_cases hj : e = j
  · subst e
    simp [hjk]
  by_cases hk : e = k
  · subst e
    simp [Ne.symm hjk]
  simp [hj,hk,h e hj hk]

def evenFirst (B J : LP) : LP := -J - (q + T (-1)) * B
def evenLast (m : ℕ) (B : LP) : LP := -T (2-(m : ℤ)) * B
def evenPenultimate (m : ℕ) (B J : LP) : LP :=
  T ((m : ℤ)-4) * J + (T (1-(m : ℤ))+T (3-(m : ℤ))) * B
def evenSecond (B J : LP) : LP := (1+T 2) * (T (-1)*J + T (-2)*B)
def evenPrePenultimate (m : ℕ) (B J : LP) : LP :=
  -(1+T 2) * (T ((m : ℤ)-5)*J + T (2-(m : ℤ))*B)

theorem evenFirst_coeff (B J : LP) (e : ℤ) :
    evenFirst B J e = -J e - B (e-1) - B (e+1) := by
  simp only [evenFirst,add_mul,coeff_sub,coeff_neg,coeff_add,coeff_shift]
  ring_nf

theorem evenLast_coeff (m : ℕ) (B : LP) (e : ℤ) :
    evenLast m B e = -B (e-2+m) := by
  simp only [evenLast,neg_mul,coeff_neg,coeff_shift]
  ring_nf

theorem evenPenultimate_coeff (m : ℕ) (B J : LP) (e : ℤ) :
    evenPenultimate m B J e = J (e-m+4) + B (e-1+m) + B (e-3+m) := by
  simp only [evenPenultimate,add_mul,coeff_add,coeff_shift]
  ring_nf

theorem evenSecond_coeff (B J : LP) (e : ℤ) :
    evenSecond B J e = J (e+1) + B (e+2) + J (e-1) + B e := by
  simp only [evenSecond,add_mul,one_mul,mul_add,coeff_add,coeff_shift]
  ring_nf

theorem evenPrePenultimate_coeff (m : ℕ) (B J : LP) (e : ℤ) :
    evenPrePenultimate m B J e =
      -(J (e-m+5) + B (e-2+m) + J (e-m+3) + B (e-4+m)) := by
  simp only [evenPrePenultimate,neg_mul,add_mul,one_mul,mul_add,coeff_neg,coeff_add,coeff_shift]
  ring_nf

theorem even_boundary_support {m : ℕ} (hm : 5 ≤ m) (B J : LP)
    (hB : Supported m B) (hF₁ : Supported m (evenFirst B J))
    (hFm : Supported m (evenLast m B))
    (hFp : Supported m (evenPenultimate m B J))
    (hF₂ : Supported m (evenSecond B J))
    (hFq : Supported m (evenPrePenultimate m B J)) :
    (∀ e : ℤ, e ≠ (m : ℤ)-1 → B e = 0) ∧
    (∀ e : ℤ, e ≠ 1 → e ≠ 2 → e ≠ 3 → J e = 0) := by
  have bl (e : ℤ) (he : e < (m : ℤ)-2) : B e = 0 := by
    have h := hFm (e+2-m) (Or.inl (by omega))
    rw [evenLast_coeff] at h
    have hh : e+2-m-2+m=e := by omega
    rw [hh] at h
    omega
  have jl (e : ℤ) (he : e < 0) : J e = 0 := by
    have h := hF₁ e (Or.inl he)
    rw [evenFirst_coeff, bl (e-1) (by omega),bl (e+1) (by omega)] at h
    omega
  have ju (e : ℤ) (he : 4 < e) : J e = 0 := by
    have h := hFp (e+m-4) (Or.inr (by omega))
    rw [evenPenultimate_coeff] at h
    have hh : e+m-4-m+4=e := by omega
    rw [hh, hB (e+m-4-1+m) (Or.inr (by omega)),
      hB (e+m-4-3+m) (Or.inr (by omega))] at h
    omega
  have bm₂ : B ((m : ℤ)-2) = 0 := by
    have h := hFp (-1) (Or.inl (by omega))
    rw [evenPenultimate_coeff, jl (-1-m+4) (by omega),bl (-1-3+m) (by omega)] at h
    have hh : (-1 : ℤ)-1+m=(m : ℤ)-2 := by omega
    rw [hh] at h
    omega
  have bm : B (m : ℤ) = 0 := by
    have h := hF₁ (m+1) (Or.inr (by omega))
    rw [evenFirst_coeff,ju (m+1) (by omega),hB (m+1+1) (Or.inr (by omega))] at h
    have hh : (m : ℤ)+1-1=(m : ℤ) := by omega
    rw [hh] at h
    omega
  have bs (e : ℤ) (he : e ≠ (m : ℤ)-1) : B e = 0 := by
    by_cases hu : (m : ℤ) < e
    · exact hB e (Or.inr hu)
    by_cases hl : e < (m : ℤ)-2
    · exact bl e hl
    have : e = (m : ℤ)-2 ∨ e = (m : ℤ) := by omega
    rcases this with rfl | rfl <;> assumption
  have j₀ : J 0 = 0 := by
    have h := hF₂ (-1) (Or.inl (by omega))
    rw [evenSecond_coeff] at h
    norm_num only at h
    rw [bs 1 (by omega),bs (-1) (by omega),jl (-2) (by omega)] at h
    omega
  have j₄ : J 4 = 0 := by
    have h := hFq (m+1) (Or.inr (by omega))
    rw [evenPrePenultimate_coeff] at h
    have hh₁ : (m : ℤ)+1-m+5=6 := by omega
    have hh₂ : (m : ℤ)+1-m+3=4 := by omega
    rw [hh₁,hh₂,ju 6 (by omega),bs (m+1-2+m) (by omega),bs (m+1-4+m) (by omega)] at h
    omega
  refine ⟨bs,?_⟩
  intro e he₁ he₂ he₃
  by_cases hl : e < 0
  · exact jl e hl
  by_cases hu : 4 < e
  · exact ju e hu
  have : e = 0 ∨ e = 4 := by omega
  rcases this with rfl | rfl <;> assumption

end ShellTomography.Uniform
