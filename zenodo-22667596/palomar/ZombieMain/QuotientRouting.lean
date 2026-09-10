import ZombieMain.ComponentMass

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Service one target while restoring a clean-entry state. -/
def TargetEntry (G : SimpleGraph V) (x : V) (phase : Phase) (t : State V) : Prop :=
  phase=.survivor ∧ (gameGraph G).Clean t.zombie t.survivor ∧ t.damaged x

/-- Follow a simple quotient path using the actual component strategies.
The deleted original entry edge handles parallel edges and quotient loops;
later entries are excluded by the simple-path condition. -/
theorem quotient_route (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    (avoid : Sym2 V) {K L : (shortGraph G).ConnectedComponent}
    (P : (componentQuotient G avoid).Walk K L) (hP : P.IsPath)
    (x : V) (hx : x∈L.supp) (s : State V)
    (hc : (gameGraph G).Clean s.zombie s.survivor) (hs : s.survivor∈K.supp)
    (hentry : s(s.zombie,s.survivor)=avoid ∨
      (shortGraph G).connectedComponentMk s.zombie∉P.support) :
    ForcesWithin (gameGraph G) (TargetEntry G x) (2*componentMass P.support) .survivor s := by
  classical
  induction P generalizing s with
  | @nil K =>
    have hr := (component_routing_at hcubic hbridge K hs hc).target_route s hc hs x hx
    apply hr.mono
    intro phase t ht
    exact ⟨ht.1,ht.2.1,ht.2.2.2.2⟩
  | @cons K J L hKJ tail ih =>
    have hpath : tail.IsPath := hP.of_cons
    have hnot : K∉tail.support := (List.nodup_cons.mp hP.support_nodup).1
    obtain ⟨q,w,hq,hw,hqw,ha⟩ := hKJ.2
    have hclean := different_components_clean K J hKJ.1 hq hw hqw
    have hne : q≠s.survivor ∨ w≠s.zombie := by
      by_contra hn
      push_neg at hn
      rcases hentry with he | he
      · apply ha
        rw [hn.1,hn.2,Sym2.eq_swap,he]
      · apply he
        have hwJ : (shortGraph G).connectedComponentMk s.zombie=J := by
          rw [← hn.2]; exact hw
        rw [hwJ]
        exact List.mem_cons_of_mem K tail.start_mem_support
    have hr := (component_routing_at hcubic hbridge K hs hc).exit_route s hc hs q w hq hclean hne
    have hb := hr.bind (2*componentMass tail.support) (by
      intro phase t ht
      rcases ht with ⟨rfl,hz,hsur⟩
      apply ih hpath hx t
      · rw [hz,hsur]; exact hclean
      · rw [hsur]; exact hw
      · right
        rw [hz,show (shortGraph G).connectedComponentMk q=K from hq]
        exact hnot)
    simpa [Walk.support_cons,componentMass_cons,Nat.mul_add] using hb

/-- Every target can be damaged and safely departed within twice the order,
from every actual clean entry in a connected bridgeless cubic graph. -/
theorem target_contract (hconn : G.Connected) (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    (s : State V) (hc : (gameGraph G).Clean s.zombie s.survivor) (x : V) :
    ForcesWithin (gameGraph G) (TargetEntry G x) (2*Fintype.card V) .survivor s := by
  classical
  obtain ⟨P,hP⟩ := quotient_path hconn s.zombie s.survivor x (hbridge _ _ hc.1)
  have hr := quotient_route hcubic hbridge s(s.zombie,s.survivor) P hP x rfl s hc rfl (Or.inl rfl)
  have hb := componentMass_le P.support hP.support_nodup
  have hpad := hr.pad (2*Fintype.card V-2*componentMass P.support)
  have he : 2*componentMass P.support+(2*Fintype.card V-2*componentMass P.support)=2*Fintype.card V := by omega
  rwa [he] at hpad

end ZombieMain
