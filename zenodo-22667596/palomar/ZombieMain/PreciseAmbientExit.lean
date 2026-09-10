import ZombieMain.AmbientModel

namespace ZombieDamage.ShortComponentModel
variable {N : Nat} {V : Type} {T : Task N} {G : Graph V}
variable (M : ShortComponentModel T G) (hg : T.GoodGraph)

/-- The final oriented clean edge, including its labelled internal endpoint.
Both endpoints are retained when boundary images are identified. -/
def PreciseExit (phase : FullGame.Phase) (s : FullGame.State V) : Prop :=
  phase = .survivor ∧ G.Clean s.zombie s.survivor ∧
    (∃ u w, T.inside u=true ∧ T.inside w=false ∧ T.adj u w=true ∧
      T.allowedExit w=true ∧ s.zombie=M.map u ∧ s.survivor=M.map w) ∧
    ∀ v, T.target=some v → s.damaged (M.map v)

/-- Exact ambient transport, retaining the departure port and its leaf. -/
theorem metricForcesWithin_precise {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (D : V → Prop) (hD : M.FlagSound s D) :
    FullGame.ForcesWithin G M.PreciseExit b .survivor (M.state s D) := by
  induction h generalizing D with
  | exit budget s w hpos hsafe hexit =>
    obtain ⟨houtside,hallowed,hseen⟩ := hexit
    have hd := M.afterSeen_sound s D hD hseen
    have hc := M.clean_boundary _ _ hsafe.1 houtside hsafe.2.2.1
    obtain ⟨huv,hvw,ht⟩ := M.safe_metric hg hsafe
    have hw : FullGame.ForcesWithin G M.PreciseExit 1 .survivor (M.state s D) := by
      apply FullGame.safe_step G (M.state s D) (M.map w) huv hvw ht
      intro y hy
      have he := (G.cleanEdge_forces_reply hc huv ht.1).1 hy
      apply FullGame.ForcesWithin.done
      refine ⟨rfl,?_,?_,hd⟩
      · change G.Clean y (M.map w)
        exact he ▸ hc
      · exact ⟨s.survivor,w,hsafe.1,houtside,hsafe.2.2.1,hallowed,he,rfl⟩
    have hb := hw.pad (budget-1)
    have hsum : 1+(budget-1)=budget := by omega
    rw [hsum] at hb
    exact hb
  | step budget s w hsafe _ _ _ ih =>
    obtain ⟨huv,hvw,ht⟩ := M.safe_metric hg hsafe
    apply FullGame.safe_step G (M.state s D) (M.map w) huv hvw ht
    intro y hy
    obtain ⟨x,hx,hxy⟩ := M.reply_lift hg hsafe hy
    have hn : M.FlagSound (T.next s w x)
        (fun v => D v ∨ v=M.map s.survivor) :=
      fun hf => M.afterSeen_sound s D hD hf
    have hi := ih x hx (fun v => D v ∨ v=M.map s.survivor) hn
    simpa [state,Task.next,FullGame.State.survivorTo,FullGame.State.zombieTo,hxy] using hi

end ZombieDamage.ShortComponentModel
