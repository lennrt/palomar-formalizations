import ZombieDamage.OpenStripReversal

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat)

/-- The one-cap target route, including the adversarial rung branch that
blocks the cap. Both possible exits differ from the original entry. -/
theorem crossed_capped_route (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false (!b)) (hs : s.survivor=rail m (!b) 0 (by omega)) :
    ForcesWithin (graph m false true hm)
      (fun p t => p=.survivor ∧
        ((t.zombie=cap m true ∧ t.survivor=capStub m true) ∨
          (t.zombie=rail m b 0 (by omega) ∧ t.survivor=stub m false b)) ∧
        ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      (2*m) .survivor s := by
  have hc : (graph m false true hm).Clean s.zombie s.survivor := by
    rw [hz,hs]
    exact left_stub_clean m hm true (!b)
  have he : (graph m false true hm).adj s.survivor (rail m b 0 (by omega)) := by
    rw [hs]
    change Adj m false true _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hn : s.zombie≠rail m b 0 (by omega) := by
    rw [hz]
    intro hh
    have hv := congrArg Fin.val hh
    cases b <;> simp [rail,stub] at hv <;> omega
  have hb : 2*m=((m-1)+m)+1 := by omega
  conv => arg 3; rw [hb]
  apply clean_entry_step (graph m false true hm) s (rail m b 0 (by omega)) hc he hn
  let t := (s.survivorTo (rail m b 0 (by omega))).zombieTo s.survivor
  have hf : Forward m 0 (by omega) b t := ⟨rfl,Or.inr hs⟩
  apply (forward_route m false true hm (m-1) 0 (by omega) b t hf).bind m
  intro phase u hu
  obtain ⟨hp,hf',hD⟩ := hu
  subst phase
  simp only [Nat.zero_add] at hf' hD
  obtain ⟨hs',hz'⟩ := hf'
  rcases hz' with ⟨j,hj,hji,hz'⟩ | hz'
  · have hj' : j=m-2 := by omega
    have hz'' : u.zombie=rail m b (m-2) (by omega) := by
      simpa only [hj'] using hz'
    have hfinish := (capped_exit m hm false b u hz'' hs').pad (m-2)
    have hbudget : 2+(m-2)=m := by omega
    simp only [hbudget] at hfinish
    apply (hfinish.preserve_set
      u.damaged (fun _ h => h)).mono
    intro q v hv
    refine ⟨hv.1.1,Or.inl ⟨hv.1.2.1,hv.1.2.2.1⟩,?_⟩
    intro k hk
    by_cases hend : k=m-1
    · subst k
      exact hv.1.2.2.2.1
    · exact hv.2 _ (hD k (by omega))
  · apply (reverse_to_open m hm b u hz' hs').mono
    intro q v hv
    exact ⟨hv.1,Or.inr ⟨hv.2.1,hv.2.2.1⟩,hv.2.2.2⟩

end ZombieDamage.OpenStrip
