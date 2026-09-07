import ShellTomography.UniformReconstruction
import ShellTomography.UniformNorm
import ShellTomography.UniformRowBounds

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace ShellTomography.Uniform

theorem norm_monoCoeff {n : ℕ} (e : ℕ) (he : e < n) :
    (∑ j : Fin n, (monoCoeff e j.val).natAbs)=1 := by
  have h (j : Fin n) : (monoCoeff e j.val).natAbs = if e=j.val then 1 else 0 := by
    unfold monoCoeff
    split_ifs <;> norm_num
  have hh (j : Fin n) : e=j.val ↔ (⟨e,he⟩ : Fin n)=j := by simp [Fin.ext_iff]
  simp only [h,hh]
  simp

theorem norm_pairCoeff {n : ℕ} (e : ℕ) (he : e+2 < n) :
    (∑ j : Fin n, (pairCoeff e j.val).natAbs)=2 := by
  have h (j : Fin n) : (pairCoeff e j.val).natAbs =
      (monoCoeff e j.val).natAbs+(monoCoeff (e+2) j.val).natAbs := by
    unfold pairCoeff monoCoeff
    split_ifs <;> norm_num
  simp only [h,Finset.sum_add_distrib,norm_monoCoeff (n := n) e (by omega),
    norm_monoCoeff (n := n) (e+2) he]

theorem paritySign_natAbs (i : ℕ) : (paritySign i).natAbs=1 := by
  unfold paritySign
  split_ifs <;> norm_num

def oddAttainer : Params4 := ⟨1,0,0,0⟩
def evenAttainer : Params4 := ⟨0,1,0,0⟩

theorem odd_attainer_interior_norm {m : ℕ} (hm : 5 ≤ m) (ho : Odd (m+1))
    (i : Fin (m+1)) (hi : 2 ≤ i.val) (him : i.val+2 ≤ m) :
    rowNorm (alternatingKernelVector (m+1) oddAttainer) i=2 := by
  simp only [rowNorm,alternatingKernelVector,if_pos ho,oddKernelEntry,Nat.add_sub_cancel,
    show i.val ≠ 0 by omega,show i.val ≠ 1 by omega,show i.val ≠ m-1 by omega,
    show i.val ≠ m by omega,ite_false,oddAttainer,zero_mul,one_mul,add_zero,zero_sub,sub_zero,
    Int.natAbs_mul,Int.natAbs_neg,paritySign_natAbs,one_mul]
  exact norm_pairCoeff _ (by omega)

theorem even_attainer_interior_norm {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1))
    (i : Fin (m+1)) (hi : 2 ≤ i.val) (him : i.val+2 ≤ m) :
    rowNorm (alternatingKernelVector (m+1) evenAttainer) i=2 := by
  simp only [rowNorm,alternatingKernelVector,if_neg ho,evenKernelEntry,Nat.add_sub_cancel,
    show i.val ≠ 0 by omega,show i.val ≠ 1 by omega,show i.val ≠ m-1 by omega,
    show i.val ≠ m by omega,ite_false,evenAttainer,zero_mul,one_mul,add_zero,zero_add,sub_zero,
    Int.natAbs_mul,paritySign_natAbs,one_mul]
  exact norm_pairCoeff _ (by omega)

theorem odd_attainer_boundary_norm {m : ℕ} (hm : 5 ≤ m) (ho : Odd (m+1)) :
    boundaryNorm hm (alternatingKernelVector (m+1) oddAttainer)=4 := by
  simp only [boundaryNorm,rowNorm,alternatingKernelVector,if_pos ho,oddKernelEntry,
    Nat.add_sub_cancel,show (1 : ℕ) ≠ 0 by omega,show m ≠ 0 by omega,show m ≠ 1 by omega,
    show m-1 ≠ 0 by omega,show m-1 ≠ 1 by omega,show m ≠ m-1 by omega,
    Fin.val_zero,Fin.val_last,oddAttainer,zero_mul,one_mul,neg_zero,neg_mul,neg_neg,
    add_zero,zero_add,zero_sub,sub_zero,Int.natAbs_neg,ite_true,ite_false,eq_self_iff_true]
  simp (disch := omega) only [norm_monoCoeff,norm_pairCoeff,Finset.sum_const_zero,Int.natAbs_zero]
  norm_num

theorem even_attainer_boundary_norm {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1)) :
    boundaryNorm hm (alternatingKernelVector (m+1) evenAttainer)=2 := by
  simp only [boundaryNorm,rowNorm,alternatingKernelVector,if_neg ho,evenKernelEntry,
    Nat.add_sub_cancel,show (1 : ℕ) ≠ 0 by omega,show m ≠ 0 by omega,show m ≠ 1 by omega,
    show m-1 ≠ 0 by omega,show m-1 ≠ 1 by omega,show m ≠ m-1 by omega,
    Fin.val_zero,Fin.val_last,evenAttainer,zero_mul,one_mul,neg_zero,neg_mul,neg_neg,
    add_zero,zero_add,zero_sub,sub_zero,Int.natAbs_neg,ite_true,ite_false,eq_self_iff_true]
  simp (disch := omega) only [norm_monoCoeff,Finset.sum_const_zero,Int.natAbs_zero]
  norm_num

theorem odd_attainer_mass {m : ℕ} (hm : 5 ≤ m) (ho : Odd (m+1)) :
    mass (positive (alternatingKernelVector (m+1) oddAttainer))=m-1 := by
  have hpart := totalNorm_partition hm (alternatingKernelVector (m+1) oddAttainer)
  rw [odd_attainer_boundary_norm hm ho] at hpart
  have hi : (∑ i ∈ interiorSet hm, rowNorm (alternatingKernelVector (m+1) oddAttainer) i)=2*(m-3) := by
    calc
      _ = ∑ _i ∈ interiorSet hm, 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh := (mem_interiorSet hm i).mp hi
        exact odd_attainer_interior_norm hm ho i hh.1 hh.2
      _ = _ := by simp [card_interiorSet,mul_comm]
  have hb := positive_negative_mass (altDistance (n := m+1) (by omega)) (⟨0,by omega⟩ : AltSensor (m+1))
    (alternatingKernelVector (m+1) oddAttainer) (kernel_sound_uniform (by omega) oddAttainer)
  have hn := totalNorm_mass (alternatingKernelVector (m+1) oddAttainer) hb
  omega

theorem even_attainer_mass {m : ℕ} (hm : 5 ≤ m) (ho : ¬Odd (m+1)) :
    mass (positive (alternatingKernelVector (m+1) evenAttainer))=m-2 := by
  have hpart := totalNorm_partition hm (alternatingKernelVector (m+1) evenAttainer)
  rw [even_attainer_boundary_norm hm ho] at hpart
  have hi : (∑ i ∈ interiorSet hm, rowNorm (alternatingKernelVector (m+1) evenAttainer) i)=2*(m-3) := by
    calc
      _ = ∑ _i ∈ interiorSet hm, 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hh := (mem_interiorSet hm i).mp hi
        exact even_attainer_interior_norm hm ho i hh.1 hh.2
      _ = _ := by simp [card_interiorSet,mul_comm]
  have hb := positive_negative_mass (altDistance (n := m+1) (by omega)) (⟨0,by omega⟩ : AltSensor (m+1))
    (alternatingKernelVector (m+1) evenAttainer) (kernel_sound_uniform (by omega) evenAttainer)
  have hn := totalNorm_mass (alternatingKernelVector (m+1) evenAttainer) hb
  omega

end ShellTomography.Uniform
