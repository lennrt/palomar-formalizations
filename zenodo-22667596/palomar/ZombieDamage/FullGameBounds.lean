import ZombieDamage.FullGame

namespace ZombieDamage.FullGame.ForcesWithin
variable {V : Type} {G : Graph V} {P : Phase → State V → Prop}
    {b c : Nat} {phase : Phase} {s : State V}

theorem budget_mono (h : ForcesWithin G P b phase s) (hbc : b≤c) :
    ForcesWithin G P c phase s := by
  have he : b+(c-b)=c := by omega
  simpa only [he] using h.pad (c-b)

end ZombieDamage.FullGame.ForcesWithin
