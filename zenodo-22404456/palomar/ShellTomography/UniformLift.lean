import ShellTomography.UniformParameters

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

def liftRow {n : ℕ} (f : Fin n → ℤ) : LP := ∑ j, C (f j)*T (j.val : ℤ)

theorem liftRow_add {n : ℕ} (f g : Fin n → ℤ) :
    liftRow (fun j => f j+g j)=liftRow f+liftRow g := by
  simp only [liftRow,map_add,add_mul,Finset.sum_add_distrib]
theorem liftRow_sub {n : ℕ} (f g : Fin n → ℤ) :
    liftRow (fun j => f j-g j)=liftRow f-liftRow g := by
  simp only [liftRow,map_sub,sub_mul,Finset.sum_sub_distrib]
theorem liftRow_neg {n : ℕ} (f : Fin n → ℤ) : liftRow (fun j => -f j) = -liftRow f := by
  simp only [liftRow,map_neg,neg_mul,Finset.sum_neg_distrib]
theorem liftRow_mul {n : ℕ} (a : ℤ) (f : Fin n → ℤ) :
    liftRow (fun j => a*f j)=C a*liftRow f := by
  simp only [liftRow,map_mul,Finset.mul_sum,mul_assoc]

theorem liftRow_mono {n : ℕ} (e : ℕ) (he : e < n) :
    liftRow (fun j : Fin n => monoCoeff e j.val)=T (e : ℤ) := by
  classical
  unfold liftRow monoCoeff
  have h (j : Fin n) : C (if e=j.val then (1 : ℤ) else 0)*T (j.val : ℤ) =
      if j = ⟨e,he⟩ then (T (e : ℤ) : LP) else 0 := by
    by_cases hj : j=⟨e,he⟩
    · subst j; simp
    · have he' : e ≠ j.val := by intro hh; apply hj; apply Fin.ext; change j.val=e; omega
      simp [hj,he']
  simp_rw [h]
  simp

theorem liftRow_pair {n : ℕ} (e : ℕ) (he : e+2 < n) :
    liftRow (fun j : Fin n => pairCoeff e j.val)=(1+T 2 : LP)*T (e : ℤ) := by
  unfold pairCoeff
  rw [liftRow_add,liftRow_mono e (by omega),liftRow_mono (e+2) he]
  simp only [Nat.cast_add,Nat.cast_ofNat]
  laurent_ring

theorem params_ext (p q : Params4) (ha : p.a=q.a) (hb : p.b=q.b)
    (hc : p.c=q.c) (hd : p.d=q.d) : p=q := by
  cases p
  cases q
  simp_all

theorem extract_reconstruct_uniform {n : ℕ} (hn : 6 ≤ n) (p : Params4) :
    alternatingExtract hn (alternatingKernelVector n p)=p := by
  rcases p with ⟨a,b,c,d⟩
  by_cases ho : Odd n
  all_goals
    apply params_ext <;>
      simp (disch := omega) [alternatingExtract,alternatingKernelVector,ho,oddKernelEntry,
        evenKernelEntry,paritySign,monoCoeff,pairCoeff,Nat.even_iff] <;>
      (try split_ifs) <;> (try simp only [mul_zero,mul_one,zero_add,add_zero,sub_zero,zero_sub,neg_neg]) <;> omega

end ShellTomography.Uniform
