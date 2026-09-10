import ZombieDamage.FullGame
import Mathlib.Logic.Function.Basic

namespace ZombieDamage.FullGame
variable {V : Type} {G : Graph V}

/-- For a positional goal, replacing the damage set changes no legal move
or forcing obligation. Used to remove a hypothetical initial departure. -/
theorem ForcesWithin.damage_irrelevant {P : Phase → V → V → Prop} {b : Nat}
    {phase : Phase} {s : State V}
    (h : ForcesWithin G (fun p t => P p t.zombie t.survivor) b phase s)
    (D : V → Prop) :
    ForcesWithin G (fun p t => P p t.zombie t.survivor) b phase ⟨s.zombie,s.survivor,D⟩ := by
  induction h generalizing D with
  | done b p s hp => exact .done b p _ hp
  | zombie b s hn hex hcap hnext ih =>
    exact .zombie b _ hn hex hcap (fun z hz => ih z hz D)
  | survivor b s w hn hw hnext ih =>
    exact .survivor b _ w hn hw (ih (fun v => D v ∨ v=s.survivor))


theorem first_survivor_move {P : Phase → State V → Prop} {b : Nat} {s : State V}
    (h : ForcesWithin G P b .survivor s) (hn : ¬P .survivor s) :
    ∃ k w,k<b ∧ LegalSurvivor G s w ∧ ForcesWithin G P k .zombie (s.survivorTo w) := by
  cases h with
  | done _ _ _ hp => exact False.elim (hn hp)
  | survivor k _ w _ hw hnext => exact ⟨k,w,Nat.lt_succ_self k,hw,hnext⟩

end ZombieDamage.FullGame
