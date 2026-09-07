import ShellTomography.UniformGridBridge

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

def parameterA (n : ℕ) (p : Params4) : LP :=
  if Odd n then C p.c*T (-2) + C p.d*T (-1)
  else C p.a*T (-2) + C p.b*T (-1) + C p.c
def parameterB (n : ℕ) (p : Params4) : LP :=
  if Odd n then -C p.a*T ((n : ℤ)-3) - C p.b*T ((n : ℤ)-2)
  else -C p.d*T ((n : ℤ)-2)

theorem one_coefficient (f : LP) (j : ℤ) (h : ∀ e : ℤ, e ≠ j → f e = 0) :
    f=C (f j)*T j := by
  apply LaurentPolynomial.ext
  intro e
  erw [coeff_monomial]
  by_cases he : e=j
  · subst e; rw [if_pos rfl]
  · rw [if_neg he,h e he]

theorem three_coefficients (f : LP)
    (h : ∀ e : ℤ, e ≠ 1 → e ≠ 2 → e ≠ 3 → f e = 0) :
    f=C (f 1)*T 1 + C (f 2)*T 2 + C (f 3)*T 3 := by
  apply LaurentPolynomial.ext
  intro e
  erw [coeff_add,coeff_add,coeff_monomial,coeff_monomial,coeff_monomial]
  by_cases he₁ : e=1
  · subst e; norm_num
  by_cases he₂ : e=2
  · subst e; norm_num
  by_cases he₃ : e=3
  · subst e; norm_num
  rw [if_neg he₁,if_neg he₂,if_neg he₃,h e he₁ he₂ he₃]
  rfl

theorem exists_parameters {m : ℕ} (hm : 5 ≤ m)
    (F : Fin (m+1) → LP) (hF : Alternating F) (hs : ∀ i, Supported m (F i)) :
    ∃ p : Params4, seedA (by omega) F = parameterA (m+1) p ∧ F 0=parameterB (m+1) p := by
  by_cases he : Even m
  · have hmo : Odd (m+1) := by rw [Nat.odd_add_one,Nat.not_odd_iff_even]; exact he
    have hm6 : 6 ≤ m := by rw [Nat.even_iff] at he; omega
    have hh := odd_boundary_two_support hm6 he F hF hs
    have hB := two_coefficients (F 0) ((m : ℤ)-2) ((m : ℤ)-1) (by omega) hh.1
    have hC := two_coefficients (F (Fin.last m)) ((m : ℤ)-2) ((m : ℤ)-1) (by omega) hh.2
    let p : Params4 := ⟨-F 0 ((m : ℤ)-2),-F 0 ((m : ℤ)-1),
      F (Fin.last m) ((m : ℤ)-2),F (Fin.last m) ((m : ℤ)-1)⟩
    refine ⟨p,?_,?_⟩
    · rw [seedA_of_even (by omega) he F hF,hC]
      simp only [parameterA,if_pos hmo,p]
      laurent_ring
    · simp only [parameterB,if_pos hmo,p,map_neg,neg_neg,Nat.cast_add,Nat.cast_one]
      convert hB using 1 <;> ring_nf
  · have hmo : ¬Odd (m+1) := by simpa [Nat.odd_add_one] using he
    have hh := even_boundary_four_support hm he F hF hs
    have hB := one_coefficient (F 0) ((m : ℤ)-1) hh.1
    have hJ := three_coefficients (seedJ (by omega) F) hh.2
    let p : Params4 := ⟨seedJ (by omega) F 1,seedJ (by omega) F 2,seedJ (by omega) F 3,
      -F 0 ((m : ℤ)-1)⟩
    refine ⟨p,?_,?_⟩
    · rw [seedA_J,hJ]
      simp only [parameterA,if_neg hmo,p]
      laurent_ring
    · simp only [parameterB,if_neg hmo,p,map_neg,neg_neg,Nat.cast_add,Nat.cast_one]
      convert hB using 1 <;> ring_nf

end ShellTomography.Uniform
