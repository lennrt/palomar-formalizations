import ZombieDamage.ShortGraph
import ZombieDamage.FullGameBridge

/-!
A faithful local model of a whole short-cycle component. Internal vertices
embed injectively; stubs may be identified with each other or with internal
vertices. The hypotheses are graph structure and component closure, not
strategy or full-damage assumptions.
-/
namespace ZombieDamage
variable {N : Nat} {V : Type}

structure ShortComponentModel (T : Task N) (G : Graph V) where
  map : Fin N → V
  internal_injective : ∀ u v, T.inside u=true → T.inside v=true → map u=map v → u=v
  edges : ∀ u v, T.adj u v=true → G.adj (map u) (map v)
  internal_edges : ∀ u v, T.inside u=true → T.inside v=true →
    (T.adj u v=true ↔ G.ShortAdj (map u) (map v))
  clean_boundary : ∀ u v, T.inside u=true → T.inside v=false →
    T.adj u v=true → G.Clean (map u) (map v)
  one_stub : ∀ u v w, T.inside v=true → T.inside u=false → T.inside w=false →
    T.adj u v=true → T.adj v w=true → u=w
  closed : ∀ u, T.inside u=true → ∀ x, G.ShortAdj (map u) x →
    ∃ v, T.inside v=true ∧ map v=x

namespace ShortComponentModel
variable {T : Task N} {G : Graph V} (M : ShortComponentModel T G) (hg : T.GoodGraph)

private theorem bool_false {b : Bool} (h : ¬ b=true) : b=false := by cases b <;> simp_all

include hg in
theorem endpoints_ne {s : Position N} {w : Fin N} (hs : T.Safe s w) :
    M.map s.zombie ≠ M.map w := by
  obtain ⟨hiv,hzv,hvw,hne,_⟩ := hs
  intro he
  by_cases hiz : T.inside s.zombie=true
  · by_cases hiw : T.inside w=true
    · exact hne (M.internal_injective _ _ hiz hiw he)
    · have hc := M.clean_boundary _ _ hiv (bool_false hiw) hvw
      have hshort := (M.internal_edges _ _ hiz hiv).1 hzv
      have hclean := G.clean_symm hc
      rw [← he] at hclean
      exact hshort.2 hclean
  · by_cases hiw : T.inside w=true
    · have hvz : T.adj s.survivor s.zombie=true := by rw [hg.1]; exact hzv
      have hc := M.clean_boundary _ _ hiv (bool_false hiz) hvz
      rw [he] at hc
      exact ((M.internal_edges _ _ hiv hiw).1 hvw).2 hc
    · exact hne (M.one_stub _ _ _ hiv (bool_false hiz) (bool_false hiw) hzv hvw)

include hg in
theorem safe_metric {s : Position N} {w : Fin N} (hs : T.Safe s w) :
    G.adj (M.map s.zombie) (M.map s.survivor) ∧
    G.adj (M.map s.survivor) (M.map w) ∧ G.TwoApart (M.map s.zombie) (M.map w) := by
  have huv := M.edges _ _ hs.2.1
  have hvw := M.edges _ _ hs.2.2.1
  have hne := M.endpoints_ne hg hs
  refine ⟨huv,hvw,?_⟩
  by_cases hiz : T.inside s.zombie=true
  · by_cases hiw : T.inside w=true
    · have hsz := (M.internal_edges _ _ hiz hs.1).1 hs.2.1
      have hsw := (M.internal_edges _ _ hs.1 hiw).1 hs.2.2.1
      refine ⟨hne,?_,M.map s.survivor,huv,hvw⟩
      intro hadj
      have hshort := (G.short_twoStep_closed hsz hsw hne).1 hadj
      have hlocal := (M.internal_edges _ _ hiz hiw).2 hshort
      rw [hs.2.2.2.2] at hlocal
      contradiction
    · exact G.cleanEdge_twoApart
        (M.clean_boundary _ _ hs.1 (bool_false hiw) hs.2.2.1) huv hne
  · have hvz : T.adj s.survivor s.zombie=true := by rw [hg.1]; exact hs.2.1
    exact G.clean_first_twoApart
      (G.clean_symm (M.clean_boundary _ _ hs.1 (bool_false hiz) hvz)) hvw hne

/-- EVERY ambient geodesic reply is the image of a local legal reply.
This includes entry, internal and exit moves, with no global stub injectivity. -/
theorem reply_lift {s : Position N} {w : Fin N} (hs : T.Safe s w)
    {y : V} (hy : G.GeodesicReply (M.map s.zombie) (M.map w) y) :
    ∃ x, (T.graph hg).GeodesicReply s.zombie w x ∧ M.map x=y := by
  have hsmetric := M.safe_metric hg hs
  have hne := M.endpoints_ne hg hs
  have hsource : (T.graph hg).GeodesicReply s.zombie w s.survivor :=
    (T.safe_replies_are_geodesic hg hs).1 ⟨hs.2.1,hs.2.2.1⟩
  by_cases hiz : T.inside s.zombie=true
  · by_cases hiw : T.inside w=true
    · obtain ⟨hzy,hyw⟩ := (G.geodesicReply_iff_commonNeighbor hsmetric.2.2).1 hy
      have hsz := (M.internal_edges _ _ hiz hs.1).1 hs.2.1
      have hsw := (M.internal_edges _ _ hs.1 hiw).1 hs.2.2.1
      have hclosed := (G.short_twoStep_closed hsz hsw hne).2 y hzy hyw
      obtain ⟨x,hix,hx⟩ := M.closed _ hiz y hclosed.1
      have hzx : T.adj s.zombie x=true := by
        apply (M.internal_edges _ _ hiz hix).2
        rw [hx]
        exact hclosed.1
      have hxw : T.adj x w=true := by
        apply (M.internal_edges _ _ hix hiw).2
        rw [hx]
        exact hclosed.2
      exact ⟨x,(T.safe_replies_are_geodesic hg hs).1 ⟨hzx,hxw⟩,hx⟩
    · have he := (G.cleanEdge_forces_reply
        (M.clean_boundary _ _ hs.1 (bool_false hiw) hs.2.2.1) hsmetric.1 hne).1 hy
      exact ⟨s.survivor,hsource,he.symm⟩
  · have hvz : T.adj s.survivor s.zombie=true := by rw [hg.1]; exact hs.2.1
    have he := G.clean_first_reply
      (G.clean_symm (M.clean_boundary _ _ hs.1 (bool_false hiz) hvz)) hsmetric.2.1 hne hy
    exact ⟨s.survivor,hsource,he.symm⟩

def state (s : Position N) (D : V → Prop) : FullGame.State V :=
  ⟨M.map s.zombie,M.map s.survivor,D⟩

def FlagSound (s : Position N) (D : V → Prop) : Prop :=
  s.seen=true → ∀ v, T.target=some v → D (M.map v)

def Exit (phase : FullGame.Phase) (s : FullGame.State V) : Prop :=
  phase = .survivor ∧ G.Clean s.zombie s.survivor ∧
    (∃ w, T.inside w=false ∧ T.allowedExit w=true ∧ s.survivor=M.map w) ∧
    ∀ v, T.target=some v → s.damaged (M.map v)

theorem afterSeen_sound (s : Position N) (D : V → Prop)
    (hD : M.FlagSound s D) (ha : T.afterSeen s=true) :
    ∀ v, T.target=some v → D (M.map v) ∨ M.map v=M.map s.survivor := by
  intro v hv
  have h := T.afterSeen_sound s (fun v => D (M.map v)) hD ha v hv
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (congrArg M.map h)

/-- Full strategy transport, including first/last moves, identified stubs,
all ambient replies, actual target damage, move budget and final clean entry.
The local model's structural hypotheses are explicit above. -/
theorem metricForcesWithin_ambient {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (D : V → Prop) (hD : M.FlagSound s D) :
    FullGame.ForcesWithin G M.Exit b .survivor (M.state s D) := by
  induction h generalizing D with
  | exit budget s w hpos hsafe hexit =>
    obtain ⟨houtside,hallowed,hseen⟩ := hexit
    have hd := M.afterSeen_sound s D hD hseen
    have hc := M.clean_boundary _ _ hsafe.1 houtside hsafe.2.2.1
    obtain ⟨huv,hvw,ht⟩ := M.safe_metric hg hsafe
    have hw : FullGame.ForcesWithin G M.Exit 1 .survivor (M.state s D) := by
      apply FullGame.safe_step G (M.state s D) (M.map w) huv hvw ht
      intro y hy
      have he := (G.cleanEdge_forces_reply hc huv ht.1).1 hy
      apply FullGame.ForcesWithin.done
      refine ⟨rfl,?_,⟨w,houtside,hallowed,rfl⟩,hd⟩
      change G.Clean y (M.map w)
      exact he ▸ hc
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

end ShortComponentModel
end ZombieDamage
