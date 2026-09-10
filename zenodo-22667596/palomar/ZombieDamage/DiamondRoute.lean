import ZombieDamage.LeafSteps

namespace ZombieDamage.DiamondRoute
open FullGame

def port (p : Bool) : Fin 6 := if p then 3 else 0
def stub (p : Bool) : Fin 6 := if p then 5 else 4
def middle (b : Bool) : Fin 6 := if b then 2 else 1

def Adj (u v : Fin 6) : Prop :=
  (u.val<4 ∧ v.val<4 ∧ u≠v ∧ ¬(u.val=0 ∧ v.val=3) ∧ ¬(u.val=3 ∧ v.val=0)) ∨
  (u.val=0 ∧ v.val=4) ∨ (u.val=4 ∧ v.val=0) ∨
  (u.val=3 ∧ v.val=5) ∨ (u.val=5 ∧ v.val=3)
instance : DecidableRel Adj := by intro u v; unfold Adj; infer_instance

def graph : Graph (Fin 6) where
  adj := Adj
  symm := by decide
  loopless := by decide
instance : DecidableRel graph.adj := inferInstanceAs (DecidableRel Adj)

/-- The diamond base case allows both central geodesic replies at the
second move. Its proof does not silently force a unique zombie response. -/
theorem through_middle (p b : Bool) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=port p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      t.zombie=port (!p) ∧ t.survivor=stub (!p) ∧
      t.damaged (port p) ∧ t.damaged (middle b) ∧ t.damaged (port (!p)))
      3 .survivor s := by
  have hc : graph.Clean s.zombie s.survivor := by
    rw [hz,hs]
    apply graph.leaf_clean
    · exact (by decide : ∀ p, graph.adj (stub p) (port p)) p
    · exact (by decide : ∀ p x, graph.adj (stub p) x → x=port p) p
  have he : graph.adj s.survivor (middle b) := by
    rw [hs]
    exact (by decide : ∀ p b, graph.adj (port p) (middle b)) p b
  have hn : s.zombie≠middle b := by
    rw [hz]
    exact (by decide : ∀ p b, stub p≠middle b) p b
  apply clean_entry_step graph s (middle b) hc he hn
  let t := (s.survivorTo (middle b)).zombieTo s.survivor
  have ht : graph.TwoApart t.zombie (port (!p)) := by
    change graph.TwoApart s.survivor (port (!p))
    rw [hs]
    refine ⟨(by decide : ∀ p, port p≠port (!p)) p,
      (by decide : ∀ p, ¬graph.adj (port p) (port (!p))) p,middle b,?_,?_⟩
    · exact (by decide : ∀ p b, graph.adj (port p) (middle b)) p b
    · exact (by decide : ∀ p b, graph.adj (middle b) (port p)) (!p) b
  have he' : graph.adj t.survivor (port (!p)) :=
    (by decide : ∀ p b, graph.adj (middle b) (port p)) (!p) b
  apply safe_step graph t (port (!p)) he he' ht
  intro z hrep
  have hreps := (graph.geodesicReply_iff_commonNeighbor ht).1 hrep
  let u := (t.survivorTo (port (!p))).zombieTo z
  have hn' : u.zombie≠stub (!p) := by
    change z≠_
    intro hh
    have hzport := (by decide : ∀ p x, graph.adj (stub p) x → x=port p)
      (!p) t.zombie (graph.symm (hh ▸ hreps.1))
    change s.survivor=port (!p) at hzport
    rw [hs] at hzport
    exact (by decide : ∀ p, port p≠port (!p)) p hzport
  have he'' : graph.adj u.survivor (stub (!p)) :=
    (by decide : ∀ p, graph.adj (port p) (stub p)) (!p)
  have hdp : u.damaged (port p) := Or.inl (Or.inr hs.symm)
  have hdb : u.damaged (middle b) := Or.inr rfl
  apply ((leaf_exit_step graph u (stub (!p)) hreps.2 he''
    ((by decide : ∀ p x, graph.adj (stub p) x → x=port p) (!p)) hn').preserve_set
    u.damaged (fun _ h => h)).mono
  intro phase v hv
  exact ⟨hv.1.1,hv.1.2.1,hv.1.2.2.1,hv.2 _ hdp,hv.2 _ hdb,hv.1.2.2.2⟩

/-- Every internal diamond target is served before the unique nonentry exit. -/
theorem target_route (p : Bool) (a : Fin 6) (ha : a.val<4) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=port p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      t.zombie=port (!p) ∧ t.survivor=stub (!p) ∧ t.damaged a)
      3 .survivor s := by
  obtain ⟨b,hb⟩ := (by decide : ∀ p a, a.val<4 → ∃ b,
    a=port p ∨ a=middle b ∨ a=port (!p)) p a ha
  apply (through_middle p b s hz hs).mono
  intro phase u hu
  refine ⟨hu.1,hu.2.1,hu.2.2.1,?_⟩
  rcases hb with h | h | h
  · exact h ▸ hu.2.2.2.1
  · exact h ▸ hu.2.2.2.2.1
  · exact h ▸ hu.2.2.2.2.2

end ZombieDamage.DiamondRoute
