import ZombieMain.ComponentRouting
import ZombieDamage.LeafSteps

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem singleton_component_eq (K : (shortGraph G).ConnectedComponent) [Subsingleton K]
    {u v : V} (hu : u∈K.supp) (hv : v∈K.supp) : u=v :=
  congrArg Subtype.val (Subsingleton.elim (⟨u,hu⟩ : K) ⟨v,hv⟩)

theorem singleton_component_clean (K : (shortGraph G).ConnectedComponent) [Subsingleton K]
    {u v : V} (hu : u∈K.supp) (h : G.Adj u v) : (gameGraph G).Clean u v := by
  classical
  by_contra hn
  have hs := (shortEdge_iff_gameShort G u v).mpr ⟨h,hn⟩
  have hv := K.mem_supp_of_adj_mem_supp hu hs
  exact h.ne (singleton_component_eq K hu hv)

theorem cubic_neighbor_other (hcubic : ∀ v,G.degree v=3) (u z : V) :
    ∃ w,G.Adj u w ∧ w≠z := by
  classical
  by_contra hn
  have hsub : G.neighborSet u ⊆ {z} := by
    intro w hw
    by_contra hwz
    exact hn ⟨w,hw,hwz⟩
  have hcard := Set.ncard_le_ncard hsub
  have hu : (G.neighborSet u).ncard=3 := by
    rw [← Set.fintypeCard_eq_ncard,G.card_neighborSet_eq_degree,hcubic]
  simp only [hu,Set.ncard_singleton] at hcard
  omega

/-- A singleton short-edge component is a clean vertex. Its three incident
edges allow every nonreversing exit and target departure. -/
theorem singleton_component_routing (K : (shortGraph G).ConnectedComponent) [Subsingleton K]
    (hcubic : ∀ v,G.degree v=3) : ComponentRouting G K (2*K.supp.ncard) := by
  classical
  have hcard : K.supp.ncard=1 := by
    obtain ⟨p,hp⟩ := K.nonempty_supp
    apply Set.ncard_eq_one.mpr
    refine ⟨p,?_⟩
    ext v
    exact ⟨fun hv => singleton_component_eq K hv hp,fun hv => hv ▸ hp⟩
  rw [hcard]
  constructor
  · intro s hc hs q w hq hqw hne
    have heq : q=s.survivor := singleton_component_eq K hq hs
    have hw : w≠s.zombie := hne.elim (fun h => False.elim (h heq)) id
    have hadj : (gameGraph G).adj s.survivor w := heq ▸ hqw.1
    have hr : ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
        t.zombie=q ∧ t.survivor=w) 1 .survivor s := by
      apply clean_entry_step (gameGraph G) s w hc hadj (Ne.symm hw)
      exact .done 0 .survivor _ ⟨rfl,heq.symm,rfl⟩
    exact hr.pad 1
  · intro s hc hs x hx
    obtain ⟨w,hw,hne⟩ := cubic_neighbor_other hcubic s.survivor s.zombie
    have hclean := singleton_component_clean K hs hw
    have hxeq : x=s.survivor := singleton_component_eq K hx hs
    have hr : ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
        (gameGraph G).Clean t.zombie t.survivor ∧ t.zombie∈K.supp ∧
        (t.zombie≠s.survivor ∨ t.survivor≠s.zombie) ∧ t.damaged x) 1 .survivor s := by
      apply clean_entry_step (gameGraph G) s w hc hw (Ne.symm hne)
      exact .done 0 .survivor _ ⟨rfl,hclean,hs,Or.inr hne,Or.inr hxeq⟩
    exact hr.pad 1

end ZombieMain
