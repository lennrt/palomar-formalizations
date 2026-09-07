import ShellTomography.UniformReconstruction
import ShellTomography.UniformRowBounds
import ShellTomography.UniformBoundary

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

theorem params_l1_positive (p : Params4) (hp : p ≠ Params4.zero) : 0 < p.l1 := by
  have hh : p.a ≠ 0 ∨ p.b ≠ 0 ∨ p.c ≠ 0 ∨ p.d ≠ 0 := by
    by_contra h
    push Not at h
    exact hp ((Params4.eq_zero_iff p).mpr h)
  unfold Params4.l1
  omega

theorem seeds_nonzero {m : ℕ} (hm : 5 ≤ m) (p : Params4) (hp : p ≠ Params4.zero) :
    parameterA (m+1) p ≠ 0 ∨ parameterB (m+1) p ≠ 0 := by
  by_contra hh
  push Not at hh
  have hr : rows (alternatingKernelVector (m+1) p) =
      rows (alternatingKernelVector (m+1) Params4.zero) := by
    rw [kernel_rows_formula hm,kernel_rows_formula hm,hh.1,hh.2]
    have ha : parameterA (m+1) Params4.zero=0 := by
      simp [parameterA,Params4.zero]
    have hb : parameterB (m+1) Params4.zero=0 := by
      simp [parameterB,Params4.zero]
    rw [ha,hb]
  have hz := rows_injective hr
  have h := congrArg (alternatingExtract (n := m+1) (by omega)) hz
  rw [extract_reconstruct_uniform,extract_reconstruct_uniform] at h
  exact hp h

theorem interior_norm_bound {m : ℕ} (hm : 5 ≤ m) (p : Params4) (hp : p ≠ Params4.zero) :
    2*(m-4) ≤ ∑ i ∈ interiorSet hm, rowNorm (alternatingKernelVector (m+1) p) i := by
  have hf (i : Fin (m+1)) (hi : i ∈ interiorSet hm) :
      rowNorm (alternatingKernelVector (m+1) p) i=0 ∨
        2 ≤ rowNorm (alternatingKernelVector (m+1) p) i := by
    by_cases hz : rows (alternatingKernelVector (m+1) p) i=0
    · exact Or.inl ((rowNorm_zero_iff _ _).mpr hz)
    · have he := (mem_interiorSet hm i).mp hi
      exact Or.inr (rowNorm_ge_two _ _ hz (interior_signed_sum_even hm p i he.1 he.2))
  have hu (i : Fin (m+1)) (hi : i ∈ interiorSet hm) (j : Fin (m+1)) (hj : j ∈ interiorSet hm)
      (hzi : rowNorm (alternatingKernelVector (m+1) p) i=0)
      (hzj : rowNorm (alternatingKernelVector (m+1) p) j=0) : i=j := by
    have hi' := (mem_interiorSet hm i).mp hi
    have hj' := (mem_interiorSet hm j).mp hj
    have zi := (rowNorm_zero_iff _ _).mp hzi
    have zj := (rowNorm_zero_iff _ _).mp hzj
    rw [kernel_rows_formula hm,interior_formula_zero _ _ i.val hi'.1 hi'.2] at zi
    rw [kernel_rows_formula hm,interior_formula_zero _ _ j.val hj'.1 hj'.2] at zj
    have h := root_unique _ _ (seeds_nonzero hm p hp) i.val j.val zi zj
    exact Fin.ext (by exact_mod_cast h)
  have h := sum_norm_lower_one_exception (interiorSet hm) (rowNorm (alternatingKernelVector (m+1) p)) hf hu
  rw [card_interiorSet] at h
  simpa only [Nat.sub_sub] using h

theorem interior_norm_bound_no_zero {m : ℕ} (hm : 5 ≤ m) (p : Params4) (hp : p ≠ Params4.zero)
    (hs : parameterA (m+1) p=0 ∨ parameterB (m+1) p=0) :
    2*(m-3) ≤ ∑ i ∈ interiorSet hm, rowNorm (alternatingKernelVector (m+1) p) i := by
  have hf (i : Fin (m+1)) (hi : i ∈ interiorSet hm) :
      2 ≤ rowNorm (alternatingKernelVector (m+1) p) i := by
    have hi' := (mem_interiorSet hm i).mp hi
    apply rowNorm_ge_two
    · intro h
      rw [kernel_rows_formula hm,interior_formula_zero _ _ i.val hi'.1 hi'.2] at h
      exact no_root_of_one_seed_zero _ _ (seeds_nonzero hm p hp) hs i.val h
    · exact interior_signed_sum_even hm p i hi'.1 hi'.2
  have h := sum_norm_lower (interiorSet hm) (rowNorm (alternatingKernelVector (m+1) p)) hf
  simpa only [card_interiorSet] using h

theorem odd_unit_one_seed_zero {m : ℕ} (ho : Odd (m+1)) (p : Params4) (hp : p.l1=1) :
    parameterA (m+1) p=0 ∨ parameterB (m+1) p=0 := by
  unfold Params4.l1 at hp
  by_cases hab : p.a=0 ∧ p.b=0
  · right
    simp [parameterB,ho,hab.1,hab.2]
  · have hc : p.c=0 := by omega
    have hd : p.d=0 := by omega
    left
    simp [parameterA,ho,hc,hd]

theorem kernel_minimum_odd {m : ℕ} (hm : 5 ≤ m) (ho : Odd (m+1)) (p : Params4)
    (hp : p ≠ Params4.zero) :
    m-1 ≤ mass (positive (alternatingKernelVector (m+1) p)) := by
  have hm6 : 6 ≤ m := by
    have he : Even m := by simpa [Nat.odd_add_one] using ho
    rw [Nat.even_iff] at he
    omega
  have hb := odd_boundary_lower hm6 ho p
  have hpart := totalNorm_partition hm (alternatingKernelVector (m+1) p)
  have hbal := positive_negative_mass (altDistance (n := m+1) (by omega))
    (⟨0,by omega⟩ : AltSensor (m+1)) (alternatingKernelVector (m+1) p) (kernel_sound_uniform (by omega) p)
  have hnorm := totalNorm_mass (alternatingKernelVector (m+1) p) hbal
  have hl := params_l1_positive p hp
  by_cases hu : p.l1=1
  · have hi := interior_norm_bound_no_zero hm p hp (odd_unit_one_seed_zero ho p hu)
    omega
  · have hi := interior_norm_bound hm p hp
    omega

theorem kernel_minimum_even {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1)) (p : Params4)
    (hp : p ≠ Params4.zero) :
    m-2 ≤ mass (positive (alternatingKernelVector (m+1) p)) := by
  have hpart := totalNorm_partition hm (alternatingKernelVector (m+1) p)
  have hbal := positive_negative_mass (altDistance (n := m+1) (by omega))
    (⟨0,by omega⟩ : AltSensor (m+1)) (alternatingKernelVector (m+1) p) (kernel_sound_uniform (by omega) p)
  have hnorm := totalNorm_mass (alternatingKernelVector (m+1) p) hbal
  have hl := params_l1_positive p hp
  by_cases hd : p.d=0
  · have hb := even_boundary_lower_zero_d hm ho p hd
    have hs : parameterB (m+1) p=0 := by simp [parameterB,ho,hd]
    have hi := interior_norm_bound_no_zero hm p hp (Or.inr hs)
    omega
  · have hb := even_boundary_lower_d hm ho p
    have hi := interior_norm_bound hm p hp
    omega

end ShellTomography.Uniform
