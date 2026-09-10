import ZombieDamage.FullGame

/-! A pursuer strategy that confines all damaged departures to a proper set.
This proves impossibility at EVERY horizon, including arbitrary survivor
passes and history-dependent survivor strategies. -/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

structure PositionalTrap where
  allowed : V → Prop
  pre : V → V → Prop
  post : V → V → Prop
  missing : ∃ v, ¬ allowed v
  zombie_move : ∀ z s, pre z s → z ≠ s →
    ∃ x, G.GeodesicReply z s x ∧ (x=s ∨ post x s)
  survivor_source : ∀ z s, post z s → allowed s
  survivor_move : ∀ z s, post z s → ∀ w,
    w ≠ z → (w=s ∨ G.adj s w) → pre z w

namespace PositionalTrap
variable {G} (T : PositionalTrap G)

def Invariant (p : Phase) (s : State V) : Prop :=
  (∀ v, s.damaged v → T.allowed v) ∧
  match p with
  | .zombie => T.pre s.zombie s.survivor
  | .survivor => T.post s.zombie s.survivor

theorem blocks (b : Nat) (p : Phase) (s : State V)
    (hI : T.Invariant p s) :
    ¬ ForcesWithin G (fun _ => AllDamaged) b p s := by
  intro h
  induction h with
  | done b p s hgoal =>
    obtain ⟨v,hv⟩ := T.missing
    exact hv (hI.1 v (hgoal v))
  | zombie b s hne _ hcap _ ih =>
    obtain ⟨x,hx,hnext⟩ := T.zombie_move s.zombie s.survivor hI.2 hne
    rcases hnext with hcapture | hpost
    · exact hcap x hx hcapture
    · exact ih x hx ⟨hI.1,hpost⟩
  | survivor b s w _ hlegal _ ih =>
    apply ih
    refine ⟨?_,T.survivor_move s.zombie s.survivor hI.2 w hlegal.1 hlegal.2⟩
    intro v hv
    rcases hv with hv | hv
    · exact hI.1 v hv
    · exact hv ▸ T.survivor_source s.zombie s.survivor hI.2

end PositionalTrap

/-- The zombie can choose one start; its confinement strategy may depend on
the observed survivor start. This is the negation of the correct initial
full-damage quantifiers, not a different game with a fixed survivor start. -/
theorem not_fullDamage_of_traps (z : V)
    (htrap : ∀ v, z ≠ v → ∃ T : PositionalTrap G, T.pre z v) :
    ¬ FullDamage G := by
  rintro ⟨b,hfull⟩
  obtain ⟨v,hne,hwin⟩ := hfull z
  obtain ⟨T,hpre⟩ := htrap v hne
  exact T.blocks b .zombie (initial z v) ⟨by simp [initial],hpre⟩ hwin

end ZombieDamage.FullGame
