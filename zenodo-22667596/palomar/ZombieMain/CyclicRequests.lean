import ZombieMain.GameMetric

namespace ZombieMain
variable {V : Type} [Fintype V]

noncomputable def cyclicRequest (hn : 0<Fintype.card V) (i : Nat) : V :=
  (Fintype.equivFin V).symm ⟨i % Fintype.card V,Nat.mod_lt _ hn⟩

theorem cyclicRequest_cofinal (hn : 0<Fintype.card V) (x : V) (N : Nat) :
    ∃ i, N≤ i ∧ cyclicRequest hn i=x := by
  let k := (Fintype.equivFin V) x
  refine ⟨N*Fintype.card V+k.val,?_,?_⟩
  · have h := Nat.le_mul_of_pos_right N hn
    omega
  · dsimp [cyclicRequest]
    have hm : (N*Fintype.card V+k.val)%Fintype.card V=k.val := by
      simp [Nat.add_mod,Nat.mod_eq_of_lt k.isLt]
    have he : (⟨(N*Fintype.card V+k.val)%Fintype.card V,Nat.mod_lt _ hn⟩ : Fin (Fintype.card V))=k :=
      Fin.ext hm
    rw [he]
    exact (Fintype.equivFin V).symm_apply_apply x

end ZombieMain
