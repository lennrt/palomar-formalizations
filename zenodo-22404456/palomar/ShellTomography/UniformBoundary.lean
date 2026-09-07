import ShellTomography.UniformNorm
import ShellTomography.UniformLift

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace ShellTomography.Uniform

theorem rowNorm_sample {n k : ℕ} (z : SignedConfiguration (Grid n)) (i : Fin n)
    (f : Fin k → Fin n) (hf : Function.Injective f) :
    (∑ j : Fin k, (z (i,f j)).natAbs) ≤ rowNorm z i := by
  classical
  have h := Finset.sum_le_sum_of_subset (f := fun j : Fin n => (z (i,j)).natAbs)
    (Finset.subset_univ (Finset.univ.map ⟨f,hf⟩))
  simpa only [Finset.sum_map,Function.Embedding.coeFn_mk,rowNorm] using h

def oddTwoCols {m : ℕ} (hm : 6 ≤ m) : Fin 2 → Fin (m+1) :=
  ![⟨m-2,by omega⟩,⟨m-1,by omega⟩]
def oddSixCols {m : ℕ} (hm : 6 ≤ m) : Fin 6 → Fin (m+1) :=
  ![⟨1,by omega⟩,⟨2,by omega⟩,⟨m-3,by omega⟩,⟨m-2,by omega⟩,⟨m-1,by omega⟩,Fin.last m]

theorem oddTwoCols_injective {m : ℕ} (hm : 6 ≤ m) : Function.Injective (oddTwoCols hm) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> (try rfl)
  all_goals
    have hh := congrArg Fin.val h
    norm_num [oddTwoCols] at hh <;> omega

theorem oddSixCols_injective {m : ℕ} (hm : 6 ≤ m) : Function.Injective (oddSixCols hm) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> (try rfl)
  all_goals
    have hh := congrArg Fin.val h
    norm_num [oddSixCols] at hh <;> omega

theorem odd_boundary_values {m : ℕ} (hm : 6 ≤ m) (ho : Odd (m+1)) (p : Params4) :
    (∀ k, alternatingKernelVector (m+1) p (0,oddTwoCols hm k) = ![-p.a,-p.b] k) ∧
    (∀ k, alternatingKernelVector (m+1) p (⟨1,by omega⟩,oddSixCols hm k) =
      ![-p.c,-p.d,p.a,p.b,p.a,p.b] k) ∧
    (∀ k, alternatingKernelVector (m+1) p (⟨m-1,by omega⟩,oddSixCols hm k) =
      ![p.a,p.b,-p.c,-p.d,-p.c,-p.d] k) ∧
    (∀ k, alternatingKernelVector (m+1) p (Fin.last m,oddTwoCols hm k) = ![p.c,p.d] k) := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    intro k
    fin_cases k <;>
      simp (disch := omega) [alternatingKernelVector,ho,oddKernelEntry,oddTwoCols,oddSixCols,
        monoCoeff,pairCoeff] <;>
      (try split_ifs) <;> (try simp only [mul_zero,mul_one,zero_add,add_zero,sub_zero,zero_sub,neg_neg]) <;> first | omega | simp only [implies_true]

theorem odd_boundary_lower {m : ℕ} (hm : 6 ≤ m) (ho : Odd (m+1)) (p : Params4) :
    4*Params4.l1 p ≤ boundaryNorm (by omega) (alternatingKernelVector (m+1) p) := by
  have hv := odd_boundary_values hm ho p
  have h₀ := rowNorm_sample (alternatingKernelVector (m+1) p) 0 (oddTwoCols hm) (oddTwoCols_injective hm)
  have h₁ := rowNorm_sample (alternatingKernelVector (m+1) p) ⟨1,by omega⟩ (oddSixCols hm) (oddSixCols_injective hm)
  have hp := rowNorm_sample (alternatingKernelVector (m+1) p) ⟨m-1,by omega⟩ (oddSixCols hm) (oddSixCols_injective hm)
  have hl := rowNorm_sample (alternatingKernelVector (m+1) p) (Fin.last m) (oddTwoCols hm) (oddTwoCols_injective hm)
  simp_rw [hv.1] at h₀
  simp_rw [hv.2.1] at h₁
  simp_rw [hv.2.2.1] at hp
  simp_rw [hv.2.2.2] at hl
  norm_num [Fin.sum_univ_succ] at h₀ h₁ hp hl
  unfold boundaryNorm Params4.l1
  omega

theorem even_boundary_values {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1)) (p : Params4) :
    alternatingKernelVector (m+1) p (0,⟨m-1,by omega⟩) = -p.d ∧
    alternatingKernelVector (m+1) p (⟨1,by omega⟩,Fin.last m) = p.d ∧
    alternatingKernelVector (m+1) p (⟨m-1,by omega⟩,0) = -p.d ∧
    alternatingKernelVector (m+1) p (Fin.last m,⟨1,by omega⟩) = p.d := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    simp (disch := omega) [alternatingKernelVector,ho,evenKernelEntry,monoCoeff,pairCoeff] <;>
      (try split_ifs) <;> (try simp only [mul_zero,mul_one,zero_add,add_zero,sub_zero,zero_sub,neg_neg]) <;> first | omega | simp only [implies_true]

theorem even_boundary_lower_d {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1)) (p : Params4) :
    4*p.d.natAbs ≤ boundaryNorm hm (alternatingKernelVector (m+1) p) := by
  have hv := even_boundary_values hm ho p
  have h₀ := entry_norm_le (alternatingKernelVector (m+1) p) 0 ⟨m-1,by omega⟩
  have h₁ := entry_norm_le (alternatingKernelVector (m+1) p) ⟨1,by omega⟩ (Fin.last m)
  have hp := entry_norm_le (alternatingKernelVector (m+1) p) ⟨m-1,by omega⟩ 0
  have hl := entry_norm_le (alternatingKernelVector (m+1) p) (Fin.last m) ⟨1,by omega⟩
  rw [hv.1,Int.natAbs_neg] at h₀
  rw [hv.2.1] at h₁
  rw [hv.2.2.1,Int.natAbs_neg] at hp
  rw [hv.2.2.2] at hl
  unfold boundaryNorm
  omega

def evenLowCols {m : ℕ} (hm : 5 ≤ m) : Fin 3 → Fin (m+1) :=
  ![⟨1,by omega⟩,⟨2,by omega⟩,⟨3,by omega⟩]
def evenHighCols {m : ℕ} (hm : 5 ≤ m) : Fin 3 → Fin (m+1) :=
  ![⟨m-3,by omega⟩,⟨m-2,by omega⟩,⟨m-1,by omega⟩]

theorem evenLowCols_injective {m : ℕ} (hm : 5 ≤ m) : Function.Injective (evenLowCols hm) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> (try rfl)
  all_goals
    have hh := congrArg Fin.val h
    norm_num [evenLowCols] at hh

theorem evenHighCols_injective {m : ℕ} (hm : 5 ≤ m) : Function.Injective (evenHighCols hm) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> (try rfl)
  all_goals
    have hh := congrArg Fin.val h
    norm_num [evenHighCols] at hh <;> omega

theorem even_boundary_values_zero_d {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1))
    (p : Params4) (hd : p.d=0) :
    (∀ k, alternatingKernelVector (m+1) p (⟨1,by omega⟩,evenLowCols hm k) = ![-p.a,-p.b,-p.c] k) ∧
    (∀ k, alternatingKernelVector (m+1) p (⟨m-1,by omega⟩,evenHighCols hm k) = ![p.a,p.b,p.c] k) := by
  constructor
  all_goals
    intro k
    fin_cases k <;>
      simp (disch := omega) [alternatingKernelVector,ho,evenKernelEntry,evenLowCols,evenHighCols,
        monoCoeff,pairCoeff,hd] <;>
      (try split_ifs) <;> (try simp only [mul_zero,mul_one,zero_add,add_zero,sub_zero,zero_sub,neg_neg]) <;> first | omega | simp only [implies_true]

theorem even_boundary_lower_zero_d {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1))
    (p : Params4) (hd : p.d=0) :
    2*Params4.l1 p ≤ boundaryNorm hm (alternatingKernelVector (m+1) p) := by
  have hv := even_boundary_values_zero_d hm ho p hd
  have h₁ := rowNorm_sample (alternatingKernelVector (m+1) p) ⟨1,by omega⟩ (evenLowCols hm) (evenLowCols_injective hm)
  have hp := rowNorm_sample (alternatingKernelVector (m+1) p) ⟨m-1,by omega⟩ (evenHighCols hm) (evenHighCols_injective hm)
  simp_rw [hv.1] at h₁
  simp_rw [hv.2] at hp
  norm_num [Fin.sum_univ_succ] at h₁ hp
  unfold boundaryNorm Params4.l1
  rw [hd]
  norm_num
  omega

end ShellTomography.Uniform
