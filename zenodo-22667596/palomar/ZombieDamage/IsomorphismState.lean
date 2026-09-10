import ZombieDamage.Isomorphism

namespace ZombieDamage.GraphIso
variable {V W : Type} {G : Graph V} {H : Graph W} (F : GraphIso G H)

@[simp] theorem symm_state (s : FullGame.State V) : F.symm.state (F.state s)=s := by
  cases s
  simp [state,symm,F.left_inv]

@[simp] theorem state_symm (s : FullGame.State W) : F.state (F.symm.state s)=s := by
  cases s
  simp [state,symm,F.right_inv]

end ZombieDamage.GraphIso
