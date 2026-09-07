import ShellTomography.UniformLift
import ShellTomography.UniformSufficiency
import ShellTomography.UniformNorm

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

theorem sum_monoCoeff {n : ℕ} (e : ℕ) (he : e < n) :
    (∑ j : Fin n, monoCoeff e j.val)=1 := by
  have h (j : Fin n) : e=j.val ↔ (⟨e,he⟩ : Fin n)=j := by simp [Fin.ext_iff]
  simp only [monoCoeff,h]
  simp

theorem sum_pairCoeff {n : ℕ} (e : ℕ) (he : e+2 < n) :
    (∑ j : Fin n, pairCoeff e j.val)=2 := by
  simp only [pairCoeff,Finset.sum_add_distrib,sum_monoCoeff (n := n) e (by omega),sum_monoCoeff (n := n) (e+2) he]
  norm_num

theorem interior_signed_sum_even {m : ℕ} (hm : 5 ≤ m) (p : Params4)
    (i : Fin (m+1)) (hi : 2 ≤ i.val) (him : i.val+2 ≤ m) :
    Even (∑ j : Fin (m+1), alternatingKernelVector (m+1) p (i,j)) := by
  by_cases ho : Odd (m+1)
  · simp only [alternatingKernelVector,if_pos ho,oddKernelEntry,Nat.add_sub_cancel,
      show i.val ≠ 0 by omega,show i.val ≠ 1 by omega,show i.val ≠ m-1 by omega,
      show i.val ≠ m by omega,ite_false,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp (disch := omega) only [sum_pairCoeff]
    refine ⟨paritySign i.val*(p.c+p.d-p.a-p.b),?_⟩
    ring
  · simp only [alternatingKernelVector,if_neg ho,evenKernelEntry,Nat.add_sub_cancel,
      show i.val ≠ 0 by omega,show i.val ≠ 1 by omega,show i.val ≠ m-1 by omega,
      show i.val ≠ m by omega,ite_false,Finset.sum_sub_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum]
    simp (disch := omega) only [sum_pairCoeff]
    refine ⟨paritySign i.val*(p.a+p.b+p.c-p.d),?_⟩
    ring

theorem T_injective : Function.Injective (T (R := ℤ)) := by
  intro i j h
  by_contra hn
  have hh := congrArg (fun f : LP => f i) h
  change (T i : LP) i=(T j : LP) i at hh
  erw [T_apply,T_apply] at hh
  rw [if_pos rfl,if_neg (Ne.symm hn)] at hh
  exact one_ne_zero hh

theorem one_add_T_two_ne_zero : (1+T 2 : LP) ≠ 0 := by
  intro h
  have hh := congrArg (fun f : LP => f 0) h
  change (T 0+T 2 : LP) 0=(0 : LP) 0 at hh
  erw [coeff_add,T_apply,T_apply,coeff_zero] at hh
  norm_num at hh

theorem interior_formula_zero {m : ℕ} (A B : LP) (i : ℕ)
    (hi : 2 ≤ i) (him : i+2 ≤ m) :
    rowFormula m A B i=0 ↔ T (2*(i : ℤ))*A+B=0 := by
  simp only [rowFormula,show i ≠ 0 by omega,show i ≠ 1 by omega,
    show i ≠ m-1 by omega,show i ≠ m by omega,ite_false]
  have hs : (if Even i then (1 : LP) else -1) ≠ 0 := by split <;> norm_num
  rw [mul_eq_zero,or_iff_right (mul_ne_zero hs one_add_T_two_ne_zero)]
  have h (f : LP) : (T (i : ℤ)*f : LP)=0 ↔ f=0 := by
    rw [mul_eq_zero,or_iff_right (isUnit_T (R := ℤ) (i : ℤ)).ne_zero]
  rw [← h]
  have hh : T (i : ℤ)*(T (i : ℤ)*A+T (-(i : ℤ))*B : LP)=T (2*(i : ℤ))*A+B := by
    laurent_ring
  rw [hh]

theorem root_unique (A B : LP) (hne : A ≠ 0 ∨ B ≠ 0) (i j : ℤ)
    (hi : T (2*i)*A+B=0) (hj : T (2*j)*A+B=0) : i=j := by
  have ha : A ≠ 0 := by
    intro h
    rw [h,mul_zero,zero_add] at hi
    rcases hne with hn | hn
    · exact hn h
    · exact hn hi
  have hh : (T (2*i)-T (2*j) : LP)*A=0 := by linear_combination hi-hj
  have he := sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right ha)
  have ht := T_injective he
  omega

theorem no_root_of_one_seed_zero (A B : LP) (hne : A ≠ 0 ∨ B ≠ 0)
    (hz : A=0 ∨ B=0) (i : ℤ) : T (2*i)*A+B ≠ 0 := by
  intro h
  rcases hz with hA | hB
  · rw [hA,mul_zero,zero_add] at h
    rcases hne with ha | hb
    · exact ha hA
    · exact hb h
  · rw [hB,add_zero] at h
    have hA := (mul_eq_zero.mp h).resolve_left (isUnit_T (R := ℤ) (2*i)).ne_zero
    rcases hne with ha | hb
    · exact ha hA
    · exact hb hB

end ShellTomography.Uniform
