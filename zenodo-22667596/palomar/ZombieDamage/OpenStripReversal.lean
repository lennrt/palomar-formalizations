import ZombieDamage.OpenStripCappedRoutes
import ZombieDamage.OpenStripSymmetry
import ZombieDamage.IsomorphismState

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat)

/-- A rung position at a capped end can turn back and cover the complete
rail before leaving through its original open end. The zombie retains every
legal geodesic choice throughout the reversal. -/
theorem reverse_to_open (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=rail m (!b) (m-1) (by omega))
    (hs : s.survivor=rail m b (m-1) (by omega)) :
    ForcesWithin (graph m false true hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b 0 (by omega) ∧
        t.survivor=stub m false b ∧ ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      m .survivor s := by
  let F := reflection m hm false true
  let s' := F.state s
  have hf : Forward m 0 (by omega) b s' := by
    constructor
    · change reflect m hm s.survivor=_
      rw [hs,reflect_rail]
      simp only [Nat.sub_self]
    · apply Or.inr
      change reflect m hm s.zombie=_
      rw [hz,reflect_rail]
      simp only [Nat.sub_self]
  have h := open_route m true hm 0 (by omega) b s' hf
  have hback := F.symm.forcesWithin h (Q := fun p t => p=.survivor ∧
      t.zombie=rail m b 0 (by omega) ∧ t.survivor=stub m false b ∧
      ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj)) (by
    intro p u hu
    refine ⟨hu.1,?_,?_,?_⟩
    · change reflect m hm u.zombie=_
      rw [hu.2.1,reflect_rail]
      simp only [Nat.sub_self]
    · change reflect m hm u.survivor=_
      rw [hu.2.2.1,reflect_stub]
      rfl
    · intro j hj
      change u.damaged (reflect m hm (rail m b j hj))
      rw [reflect_rail]
      exact hu.2.2.2 _ (by omega) (Nat.zero_le _))
  simpa only [s',F.symm_state,Nat.sub_zero] using hback

/-- Entry from an open end, keeping the entry rail, immediately establishes
an exact trailing state regardless of the presence of a far cap. -/
theorem open_prefix (hm : 2≤m) (right b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false b) (hs : s.survivor=rail m b 0 (by omega)) :
    ForcesWithin (graph m false right hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b 0 (by omega) ∧
        t.survivor=rail m b 1 (by omega) ∧ t.damaged (rail m b 0 (by omega)))
      1 .survivor s := by
  have hc : (graph m false right hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_stub_clean m hm right b
  have he : (graph m false right hm).adj s.survivor (rail m b 1 (by omega)) := by
    rw [hs]
    change Adj m false right _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 1 (by omega) := by
    rw [hz]
    intro hh
    have hv := congrArg Fin.val hh
    cases b <;> simp [rail,stub] at hv <;> omega
  apply clean_entry_step (graph m false right hm) s (rail m b 1 (by omega)) hc he hn
  exact .done 0 .survivor _ ⟨rfl,hs,rfl,Or.inr hs.symm⟩

/-- From an open-end entry, its own rail and the far cap are all damaged
before exit at that cap. -/
theorem open_to_cap (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false b) (hs : s.survivor=rail m b 0 (by omega)) :
    ForcesWithin (graph m false true hm)
      (fun p t => p=.survivor ∧ t.zombie=cap m true ∧ t.survivor=capStub m true ∧
        t.damaged (cap m true) ∧ ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      (m+1) .survivor s := by
  have hb : m+1=1+(m-1+1) := by omega
  conv => arg 3; rw [hb]
  apply (open_prefix m hm true b s hz hs).bind (m-1+1)
  intro phase t ht
  obtain ⟨hp,hz',hs',hzero⟩ := ht
  subst phase
  apply ((capped_suffix m hm false b 1 (by omega) (by omega) t hz' hs').preserve_set
    t.damaged (fun _ h => h)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.1.2.2.2.1,?_⟩
  intro j hj
  cases j with
  | zero => exact hu.2 _ hzero
  | succ j => exact hu.1.2.2.2.2 _ hj (by omega)

/-- Crossing the first rung allows the neighboring open-end exit in two
moves, including both source departures. -/
theorem near_open_exit (hm : 2≤m) (right b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false (!b)) (hs : s.survivor=rail m (!b) 0 (by omega)) :
    ForcesWithin (graph m false right hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b 0 (by omega) ∧
        t.survivor=stub m false b ∧ t.damaged (rail m b 0 (by omega)))
      2 .survivor s := by
  have hc : (graph m false right hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_stub_clean m hm right (!b)
  have he : (graph m false right hm).adj s.survivor (rail m b 0 (by omega)) := by
    rw [hs]
    change Adj m false right _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 0 (by omega) := by
    rw [hz]
    intro hh
    have hv := congrArg Fin.val hh
    cases b <;> simp [rail,stub] at hv <;> omega
  apply clean_entry_step (graph m false right hm) s (rail m b 0 (by omega)) hc he hn
  let t := (s.survivorTo (rail m b 0 (by omega))).zombieTo s.survivor
  have he' : (graph m false right hm).adj t.survivor (stub m false b) := by
    change Adj m false right (rail m b 0 (by omega)).val (stub m false b).val
    cases b <;> simp [rail,stub,Adj] <;> omega
  have hn' : t.zombie≠stub m false b := by
    change s.survivor≠_
    rw [hs]
    intro hh
    have hv := congrArg Fin.val hh
    cases b <;> simp [rail,stub] at hv <;> omega
  exact leaf_exit_step (graph m false right hm) t (stub m false b) he he'
    (left_stub_neighbor m hm right b) hn'

end ZombieDamage.OpenStrip
