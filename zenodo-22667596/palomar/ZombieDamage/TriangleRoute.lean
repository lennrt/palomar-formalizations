import ZombieDamage.LeafSteps

namespace ZombieDamage.TriangleRoute
open FullGame

def vertex (p : Fin 3) : Fin 6 := ⟨p.val,by omega⟩
def stub (p : Fin 3) : Fin 6 := ⟨p.val+3,by omega⟩
def Adj (u v : Fin 6) : Prop :=
  (u.val<3 ∧ v.val<3 ∧ u≠v) ∨
  (u.val<3 ∧ v.val=u.val+3) ∨ (v.val<3 ∧ u.val=v.val+3)
instance : DecidableRel Adj := by
  intro u v
  unfold Adj
  infer_instance

def graph : Graph (Fin 6) where
  adj := Adj
  symm := by decide
  loopless := by decide

instance : DecidableRel graph.adj := inferInstanceAs (DecidableRel Adj)

theorem entry_clean : ∀ p, graph.Clean (stub p) (vertex p) := by
  intro p
  apply graph.leaf_clean
  · exact (by decide : ∀ p, graph.adj (stub p) (vertex p)) p
  · exact (by decide : ∀ p x, graph.adj (stub p) x → x=vertex p) p

/-- Every ordered pair of distinct triangle ports has a two-move route,
and both the entry and exit port are damaged. -/
theorem prescribed_exit (p q : Fin 3) (hne : p≠q) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=vertex p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      t.zombie=vertex q ∧ t.survivor=stub q ∧
      t.damaged (vertex p) ∧ t.damaged (vertex q)) 2 .survivor s := by
  have hc : graph.Clean s.zombie s.survivor := by rw [hz,hs]; exact entry_clean p
  have he : graph.adj s.survivor (vertex q) := by
    rw [hs]
    exact (by decide : ∀ p q, p≠q → graph.adj (vertex p) (vertex q)) p q hne
  have hn : s.zombie≠vertex q := by
    rw [hz]
    exact (by decide : ∀ p q, stub p≠vertex q) p q
  apply clean_entry_step graph s (vertex q) hc he hn
  let t := (s.survivorTo (vertex q)).zombieTo s.survivor
  have hd : t.damaged (vertex p) := Or.inr hs.symm
  have he' : graph.adj t.survivor (stub q) :=
    (by decide : ∀ q, graph.adj (vertex q) (stub q)) q
  have hn' : t.zombie≠stub q := by
    change s.survivor≠_
    rw [hs]
    exact (by decide : ∀ p q, vertex p≠stub q) p q
  apply ((leaf_exit_step graph t (stub q) he he'
      ((by decide : ∀ q x, graph.adj (stub q) x → x=vertex q) q) hn').preserve_set
      (fun v => v=vertex p) (fun v hv => hv ▸ hd)).mono
  intro phase u hu
  exact ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.2 _ rfl,hu.1.2.2.2⟩

/-- All target and entry choices for the one-rung one-cap base case. -/
theorem target_route (p a : Fin 3) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=vertex p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      ∃ q, q≠p ∧ t.zombie=vertex q ∧ t.survivor=stub q ∧ t.damaged (vertex a))
      2 .survivor s := by
  by_cases h : p=a
  · obtain ⟨q,hq⟩ := (by decide : ∀ p : Fin 3, ∃ q : Fin 3, p≠q) p
    apply (prescribed_exit p q hq s hz hs).mono
    intro phase u hu
    exact ⟨hu.1,q,Ne.symm hq,hu.2.1,hu.2.2.1,h ▸ hu.2.2.2.1⟩
  · apply (prescribed_exit p a h s hz hs).mono
    intro phase u hu
    exact ⟨hu.1,a,Ne.symm h,hu.2.1,hu.2.2.1,hu.2.2.2.2⟩

end ZombieDamage.TriangleRoute
