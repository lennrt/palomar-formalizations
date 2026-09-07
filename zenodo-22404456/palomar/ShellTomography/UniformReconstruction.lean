import ShellTomography.UniformSufficiency
import ShellTomography.UniformLift

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000
noncomputable section
namespace ShellTomography.Uniform
open LaurentPolynomial

theorem T_C_comm (k a : ℤ) : (T k : LP)*C a = C a*T k := mul_comm _ _

theorem kernel_rows_formula {m : ℕ} (hm : 5 ≤ m) (p : Params4) :
    rows (alternatingKernelVector (m+1) p) = fun i : Fin (m+1) =>
      rowFormula m (parameterA (m+1) p) (parameterB (m+1) p) i.val := by
  funext ⟨i,hi⟩
  change liftRow (fun j : Fin (m+1) => alternatingKernelVector (m+1) p (⟨i,hi⟩,j)) = _
  by_cases ho : Odd (m+1)
  · have he : Even m := by simpa [Nat.odd_add_one] using ho
    simp only [alternatingKernelVector,if_pos ho,oddKernelEntry,Nat.add_sub_cancel,
      rowFormula,parameterA,parameterB,if_pos he,paritySign]
    split_ifs <;> first | omega | skip
    all_goals
      try simp only [liftRow_add,liftRow_sub,liftRow_neg,liftRow_mul,map_neg,map_one,neg_mul,one_mul]
      try simp (disch := omega) only [liftRow_mono,liftRow_pair]
      try simp (disch := omega) only [Nat.cast_sub,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      try simp only [mul_add,add_mul,mul_sub,sub_mul,mul_neg,neg_mul,one_mul,mul_one,
        ← mul_assoc,← T_add,T_pow]
      ring_nf
      all_goals
        try simp only [T_C_comm,LaurentPolynomial.mul_T_assoc,← T_add,T_pow]
        ring_nf
  · have he : ¬Even m := by simpa [Nat.odd_add_one] using ho
    simp only [alternatingKernelVector,if_neg ho,evenKernelEntry,Nat.add_sub_cancel,
      rowFormula,parameterA,parameterB,if_neg he,paritySign]
    split_ifs <;> first | omega | skip
    all_goals
      try simp only [liftRow_add,liftRow_sub,liftRow_neg,liftRow_mul,map_neg,map_one,neg_mul,one_mul]
      try simp (disch := omega) only [liftRow_mono,liftRow_pair]
      try simp (disch := omega) only [Nat.cast_sub,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
      try simp only [mul_add,add_mul,mul_sub,sub_mul,mul_neg,neg_mul,one_mul,mul_one,
        ← mul_assoc,← T_add,T_pow]
      ring_nf
      all_goals
        try simp only [T_C_comm,LaurentPolynomial.mul_T_assoc,← T_add,T_pow]
        ring_nf

theorem kernel_sound_uniform {n : ℕ} (hn : 6 ≤ n) (p : Params4) :
    Invisible (altDistance (by omega)) (alternatingKernelVector n p) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  apply rows_alternating_invisible (by omega)
  rw [kernel_rows_formula (by omega)]
  exact rowFormula_alternating (by omega) _ _

theorem kernel_complete_uniform {n : ℕ} (hn : 6 ≤ n) (z : SignedConfiguration (Grid n))
    (hz : Invisible (altDistance (by omega)) z) :
    z=alternatingKernelVector n (alternatingExtract hn z) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  have ha := invisible_rows_alternating (by omega) z hz
  obtain ⟨p,hA,hB⟩ := exists_parameters (by omega) (rows z) ha (rows_supported z)
  have hr := rowFormula_necessary (by omega) (rows z) ha
  rw [hA,hB] at hr
  have he : z=alternatingKernelVector (m+1) p := rows_injective (hr.trans (kernel_rows_formula (by omega) p).symm)
  rw [he,extract_reconstruct_uniform]

theorem grid_kernel_uniform {n : ℕ} (hn : 6 ≤ n) (z : SignedConfiguration (Grid n)) :
    Invisible (altDistance (by omega)) z ↔ ∃! p : Params4, z=alternatingKernelVector n p := by
  constructor
  · intro hz
    refine ⟨alternatingExtract hn z,kernel_complete_uniform hn z hz,?_⟩
    intro p hp
    rw [hp,extract_reconstruct_uniform]
  · rintro ⟨p,rfl,_⟩
    exact kernel_sound_uniform hn p

end ShellTomography.Uniform
