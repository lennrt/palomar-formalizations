import ZombieDamage.OpenStripCaps

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat)

/-- Entering an uncapped ladder and choosing the opposite rail covers that
whole rail before a nonentry exit. All lengths m>=2 are included. -/
theorem crossed_open_route (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false (!b)) (hs : s.survivor=rail m (!b) 0 (by omega)) :
    ForcesWithin (graph m false false hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (m-1) (by omega) ∧
        t.survivor=stub m true b ∧ ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      (m+1) .survivor s := by
  have hc : (graph m false false hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_stub_clean m hm false (!b)
  have he : (graph m false false hm).adj s.survivor (rail m b 0 (by omega)) := by
    rw [hs]
    change Adj m false false _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 0 (by omega) := by
    rw [hz]
    intro h
    have hv := congrArg Fin.val h
    cases b <;> simp [stub,rail] at hv <;> omega
  apply clean_entry_step (graph m false false hm) s (rail m b 0 (by omega)) hc he hn
  have hf : Forward m 0 (by omega) b
      ((s.survivorTo (rail m b 0 (by omega))).zombieTo s.survivor) :=
    ⟨rfl,Or.inr hs⟩
  apply (open_route m false hm 0 (by omega) b _ hf).mono
  intro p t ht
  exact ⟨ht.1,ht.2.1,ht.2.2.1,fun j hj => ht.2.2.2 j hj (Nat.zero_le _)⟩

/-- Entering an uncapped ladder and keeping the entry rail also covers that
whole rail, with its exact final departure, before the opposite-end exit. -/
theorem straight_open_route (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false b) (hs : s.survivor=rail m b 0 (by omega)) :
    ForcesWithin (graph m false false hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (m-1) (by omega) ∧
        t.survivor=stub m true b ∧ ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      m .survivor s := by
  have hc : (graph m false false hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_stub_clean m hm false b
  have he : (graph m false false hm).adj s.survivor (rail m b 1 (by omega)) := by
    rw [hs]
    change Adj m false false _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 1 (by omega) := by
    rw [hz]
    intro h
    have hv := congrArg Fin.val h
    cases b <;> simp [stub,rail] at hv <;> omega
  have hb : m=(m-1)+1 := by omega
  conv => arg 3; rw [hb]
  apply clean_entry_step (graph m false false hm) s (rail m b 1 (by omega)) hc he hn
  let t := (s.survivorTo (rail m b 1 (by omega))).zombieTo s.survivor
  have hf : Forward m 1 (by omega) b t := ⟨rfl,Or.inl ⟨0,by omega,rfl,hs⟩⟩
  have hd : t.damaged (rail m b 0 (by omega)) := Or.inr hs.symm
  apply ((open_route m false hm 1 (by omega) b t hf).preserve_set
    (fun v => v=rail m b 0 (by omega)) (fun v hv => hv ▸ hd)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,?_⟩
  intro j hj
  cases j with
  | zero => exact hu.2 _ rfl
  | succ j => exact hu.1.2.2.2 _ hj (by omega)

/-- The two moves from a left cap entry establish a trailing rail state,
crediting both completed departures. -/
theorem cap_prefix (hm : 2≤m) (right b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=capStub m false) (hs : s.survivor=cap m false) :
    ForcesWithin (graph m true right hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b 0 (by omega) ∧
        t.survivor=rail m b 1 (by omega) ∧ t.damaged (cap m false) ∧
        t.damaged (rail m b 0 (by omega))) 2 .survivor s := by
  have hc : (graph m true right hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_capStub_clean m hm right
  have he : (graph m true right hm).adj s.survivor (rail m b 0 (by omega)) := by
    rw [hs]
    change Adj m true right _ _
    cases b <;> simp [cap,rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 0 (by omega) := by
    rw [hz]
    intro h
    have hv := congrArg Fin.val h
    cases b <;> simp [capStub,rail] at hv <;> omega
  apply clean_entry_step (graph m true right hm) s (rail m b 0 (by omega)) hc he hn
  let t := (s.survivorTo (rail m b 0 (by omega))).zombieTo s.survivor
  have hzt : t.zombie=cap m false := hs
  have huv : (graph m true right hm).adj t.zombie t.survivor := he
  have hvw : (graph m true right hm).adj t.survivor (rail m b 1 (by omega)) := by
    change Adj m true right _ _
    cases b <;> simp [t,State.zombieTo,State.survivorTo,rail,Adj] <;> omega
  have ht := cap_rail_step m hm right b
  apply safe_step (graph m true right hm) t (rail m b 1 (by omega)) huv hvw (hzt ▸ ht.1)
  intro z hrep
  rw [hzt] at hrep
  exact .done 0 .survivor _ ⟨rfl,ht.2 z hrep,rfl,Or.inl (Or.inr hs.symm),Or.inr rfl⟩

/-- From a one-cap entry, either whole rail can be covered before exiting. -/
theorem one_cap_entry_route (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=capStub m false) (hs : s.survivor=cap m false) :
    ForcesWithin (graph m true false hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (m-1) (by omega) ∧ t.survivor=stub m true b ∧
        t.damaged (cap m false) ∧ ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      (m+1) .survivor s := by
  have hb : m+1=2+(m-1) := by omega
  conv => arg 3; rw [hb]
  apply (cap_prefix m hm false b s hz hs).bind (m-1)
  intro phase t ht
  obtain ⟨hp,hz',hs',hc,hzero⟩ := ht
  subst phase
  have hf : Forward m 1 (by omega) b t := ⟨hs',Or.inl ⟨0,by omega,rfl,hz'⟩⟩
  apply ((open_route m true hm 1 (by omega) b t hf).preserve_set t.damaged (fun _ h => h)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.2 _ hc,?_⟩
  intro j hj
  cases j with
  | zero => exact hu.2 _ hzero
  | succ j => exact hu.1.2.2.2 _ hj (by omega)

end ZombieDamage.OpenStrip
