import ZombieDamage.Certificates
import ZombieDamage.FullGame

/-! Connects the already checked finite-routing strategies to the full game.
The flag is related to the actual damaged-vertex set, and terminal exits
include the following zombie turn. This is a bridge for the specified local
graph, not an assertion that an arbitrary ambient embedding preserves it. -/
namespace ZombieDamage.Task
open FullGame
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)

def TargetDamaged (D : Fin N → Prop) : Prop :=
  ∀ v, T.target = some v → D v

def FlagSound (s : Position N) (D : Fin N → Prop) : Prop :=
  s.seen = true → T.TargetDamaged D

def fullState (s : Position N) (D : Fin N → Prop) : State (Fin N) :=
  ⟨s.zombie, s.survivor, D⟩

def FullExit (phase : Phase) (s : State (Fin N)) : Prop :=
  phase = .survivor ∧ T.inside s.survivor = false ∧
    T.allowedExit s.survivor = true ∧ T.TargetDamaged s.damaged

theorem afterSeen_sound (s : Position N) (D : Fin N → Prop)
    (hs : T.FlagSound s D) (ha : T.afterSeen s = true) :
    T.TargetDamaged (fun v => D v ∨ v = s.survivor) := by
  intro v hv
  have hm : s.seen = true ∨ s.survivor = v := by
    simpa [afterSeen, hv] using ha
  rcases hm with hseen | heq
  · exact Or.inl (hs hseen v hv)
  · exact Or.inr heq.symm

/-- Every finite certificate strategy is a genuine bounded strategy in the
full zombie-first game once at its specified post-zombie local state. It
handles all geodesic replies and ends after a safe exit and zombie response.
The target flag is never taken as an unexplained damage assumption. -/
theorem metricForcesWithin_fullGame {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (D : Fin N → Prop)
    (hs : T.FlagSound s D) :
    ForcesWithin (T.graph hg) T.FullExit b .survivor (fullState s D) := by
  induction h generalizing D with
  | exit budget s w hpos hsafe hexit =>
    obtain ⟨hinside, hallowed, hflag⟩ := hexit
    have hd := T.afterSeen_sound s D hs hflag
    have hstep : ForcesWithin (T.graph hg) T.FullExit 1 .survivor
        (fullState s D) := by
      apply FullGame.safe_step (T.graph hg) (fullState s D) w
        hsafe.2.1 hsafe.2.2.1 (T.safe_twoApart hg hsafe)
      intro z _
      exact .done 0 .survivor _ ⟨rfl, hinside, hallowed, hd⟩
    have hp := hstep.pad (budget - 1)
    have hsum : 1 + (budget - 1) = budget := by omega
    rw [hsum] at hp
    exact hp
  | step budget s w hsafe _ _ _ ih =>
    apply FullGame.safe_step (T.graph hg) (fullState s D) w
      hsafe.2.1 hsafe.2.2.1 (T.safe_twoApart hg hsafe)
    intro z hz
    have hn : T.FlagSound (T.next s w z) (fun v => D v ∨ v = s.survivor) :=
      fun hflag => T.afterSeen_sound s D hs hflag
    have hc := ih z hz (fun v => D v ∨ v = s.survivor) hn
    simpa [fullState, next, State.survivorTo, State.zombieTo] using hc

end ZombieDamage.Task
