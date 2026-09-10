import ZombieDamage.FullGameBridge
import ZombieDamage.OriginalGameChecks

/-! Completeness of the local routing language for post-zombie exit goals on
leaf-augmented components. Adjacency is the ordinary full-game invariant;
safety and distance two are derived, not imposed on legal survivor moves. -/
namespace ZombieDamage.Task
open FullGame
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)

def BoundaryLeaves : Prop := ∀ v, T.inside v=false →
  ∀ u w, T.adj v u=true → T.adj v w=true → u=w

def FlagComplete (s : Position N) (D : Fin N → Prop) : Prop :=
  ∀ v, T.target=some v → D v → s.seen=true

theorem afterSeen_complete (s : Position N) (D : Fin N → Prop)
    (hs : T.FlagComplete s D) (x w : Fin N) :
    T.FlagComplete (T.next s w x) (fun v => D v ∨ v=s.survivor) := by
  intro v hv hd
  change T.afterSeen s=true
  rcases hd with hd | he
  · simp [afterSeen,hs v hv hd]
  · simp [afterSeen,hv,he]

theorem exit_flag (s : Position N) (D : Fin N → Prop)
    (hs : T.FlagComplete s D)
    (hd : T.TargetDamaged (fun v => D v ∨ v=s.survivor)) :
    T.afterSeen s=true := by
  cases ht : T.target with
  | none => simp [afterSeen,ht]
  | some v =>
    rcases hd v ht with hd | he
    · simp [afterSeen,hs v ht hd]
    · simp [afterSeen,ht,he]

/-- From an adjacent post-zombie state at a leaf, any successful exit-objective
strategy must already have reached that objective. Passing would be captured. -/
theorem leaf_forcing_goal (hl : T.BoundaryLeaves) (s : State (Fin N))
    (hout : T.inside s.survivor=false) (hadj : (T.graph hg).adj s.zombie s.survivor)
    {b : Nat} (h : ForcesWithin (T.graph hg) T.FullExit b .survivor s) :
    T.FullExit .survivor s := by
  cases h with
  | done _ _ _ hp => exact hp
  | survivor n _ w hn hw hc =>
    have he : w=s.survivor := by
      rcases hw.2 with he | hedge
      · exact he
      · have hsame := hl s.survivor hout s.zombie w ((T.graph hg).symm hadj) hedge
        exact False.elim (hw.1 hsame.symm)
    have hadj' : (T.graph hg).adj (s.survivorTo w).zombie (s.survivorTo w).survivor := by
      simpa [State.survivorTo,he] using hadj
    have hgoal : ¬ T.FullExit .zombie (s.survivorTo w) := by
      intro hp
      cases hp.1
    exact False.elim (first_capture_blocks_goal (T.graph hg) _ hgoal hadj' n hc)

/-- A complete bounded full-game routing proof yields the distance-two local
certificate predicate. No restriction of Randy's legal moves is assumed. -/
theorem fullGame_metricForcesWithin (hl : T.BoundaryLeaves) (b : Nat)
    (s : Position N) (D : Fin N → Prop)
    (hinside : T.inside s.survivor=true) (hadj : T.adj s.zombie s.survivor=true)
    (hflag : T.FlagComplete s D)
    (h : ForcesWithin (T.graph hg) T.FullExit b .survivor (fullState s D)) :
    T.MetricForcesWithin hg b s := by
  induction b generalizing s D with
  | zero =>
    cases h with
    | done _ _ _ hp => simp [FullExit,fullState,hinside] at hp
  | succ b ih =>
    cases h with
    | done _ _ _ hp => simp [FullExit,fullState,hinside] at hp
    | survivor _ _ w hne hw hnext =>
      have hgoal : ¬ T.FullExit .zombie ((fullState s D).survivorTo w) := by
        intro hp
        cases hp.1
      have hno : ¬ (T.graph hg).adj s.zombie w := by
        intro ha
        exact first_capture_blocks_goal (T.graph hg) _ hgoal ha b hnext
      have hmove : T.adj s.survivor w=true := by
        rcases hw.2 with he | he
        · exact False.elim (hno (he ▸ hadj))
        · exact he
      have hs : T.Safe s w := ⟨hinside,hadj,hmove,hw.1.symm,by
        cases he : T.adj s.zombie w
        · rfl
        · exact False.elim (hno he)⟩
      cases hnext with
      | done _ _ _ hp => exact False.elim (hgoal hp)
      | zombie _ _ _ hex _ hcont =>
        by_cases hiw : T.inside w=true
        · apply MetricForcesWithin.step b s w hs hiw hex
          intro x hx
          have hrep := (T.safe_replies_are_geodesic hg hs).2 hx
          exact ih (T.next s w x) (fun v => D v ∨ v=s.survivor) hiw hrep.2
            (T.afterSeen_complete s D hflag x w) (hcont x hx)
        · have how : T.inside w=false := by cases h : T.inside w <;> simp_all
          have hv : (T.graph hg).GeodesicReply s.zombie w s.survivor :=
            (T.safe_replies_are_geodesic hg hs).1 ⟨hadj,hmove⟩
          have hfinish := T.leaf_forcing_goal hg hl (((fullState s D).survivorTo w).zombieTo s.survivor) how hmove (hcont s.survivor hv)
          apply MetricForcesWithin.exit (b+1) s w (by omega) hs
          exact ⟨how,hfinish.2.2.1,T.exit_flag s D hflag hfinish.2.2.2⟩

end ZombieDamage.Task
