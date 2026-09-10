import ZombieDamage.OpenStripTrailing
import ZombieDamage.OpenStripEntry

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat)

theorem right_capStub_neighbor (hm : 2≤m) (left : Bool) (x : Fin (2*m+8))
    (h : (graph m left true hm).adj (capStub m true) x) : x=cap m true := by
  apply Fin.ext
  change Adj m left true _ _ at h
  simp [capStub,cap,Adj] at *
  omega

/-- A trailing zombie at the far end has exactly the expected reply to entry
into the cap. Rung states are deliberately excluded from this statement. -/
theorem rail_cap_step (hm : 2≤m) (left b : Bool) :
    (graph m left true hm).TwoApart (rail m b (m-2) (by omega)) (cap m true) ∧
    ∀ x, (graph m left true hm).GeodesicReply (rail m b (m-2) (by omega))
      (cap m true) x → x=rail m b (m-1) (by omega) := by
  have ht : (graph m left true hm).TwoApart (rail m b (m-2) (by omega)) (cap m true) := by
    refine ⟨?_,?_,rail m b (m-1) (by omega),?_,?_⟩
    · intro he
      have hv := congrArg Fin.val he
      cases b <;> simp [cap,rail] at hv <;> omega
    · change ¬ Adj m left true _ _
      cases b <;> simp [cap,rail,Adj] <;> omega
    · change Adj m left true _ _
      cases b <;> simp [rail,Adj] <;> omega
    · change Adj m left true _ _
      cases b <;> simp [cap,rail,Adj] <;> omega
  refine ⟨ht,?_⟩
  intro x hx
  obtain ⟨h1,h2⟩ := ((graph m left true hm).geodesicReply_iff_commonNeighbor ht).1 hx
  apply Fin.ext
  change Adj m left true _ _ at h1 h2
  cases left <;> cases b <;>
    simp only [cap,rail,Bool.false_eq_true,↓reduceIte] at * <;> unfold Adj at * <;> omega

theorem capped_exit (hm : 2≤m) (left b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=rail m b (m-2) (by omega))
    (hs : s.survivor=rail m b (m-1) (by omega)) :
    ForcesWithin (graph m left true hm)
      (fun p t => p=.survivor ∧ t.zombie=cap m true ∧ t.survivor=capStub m true ∧
        t.damaged (rail m b (m-1) (by omega)) ∧ t.damaged (cap m true))
      2 .survivor s := by
  have huv : (graph m left true hm).adj s.zombie s.survivor := by
    rw [hz,hs]
    change Adj m left true _ _
    cases b <;> simp [rail,Adj] <;> omega
  have hvw : (graph m left true hm).adj s.survivor (cap m true) := by
    rw [hs]
    change Adj m left true _ _
    cases b <;> simp [rail,cap,Adj] <;> omega
  have ht := rail_cap_step m hm left b
  apply safe_step (graph m left true hm) s (cap m true) huv hvw (hz ▸ ht.1)
  intro z hrep
  rw [hz] at hrep
  have hz' := ht.2 z hrep
  let t := (s.survivorTo (cap m true)).zombieTo z
  have ha : (graph m left true hm).adj t.zombie t.survivor := by
    change (graph m left true hm).adj z (cap m true)
    rw [hz']
    exact hs ▸ hvw
  have he : (graph m left true hm).adj t.survivor (capStub m true) := by
    change Adj m left true _ _
    simp [t,State.survivorTo,State.zombieTo,cap,capStub,Adj]
  have hn : t.zombie≠capStub m true := by
    change z≠_
    rw [hz']
    intro hh
    have hv := congrArg Fin.val hh
    cases b <;> simp [rail,capStub] at hv <;> omega
  have hD : t.damaged (rail m b (m-1) (by omega)) := Or.inr hs.symm
  apply ((leaf_exit_step (graph m left true hm) t (capStub m true) ha he
    (right_capStub_neighbor m hm left) hn).preserve_set
    (fun v => v=rail m b (m-1) (by omega)) (fun v hv => hv ▸ hD)).mono
  intro p u hu
  exact ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.2 _ rfl,hu.1.2.2.2⟩

/-- All remaining vertices of a rail and the right cap can be served from
any trailing state, with the exit included in the bound. -/
theorem capped_suffix (hm : 2≤m) (left b : Bool) (i : Nat) (hip : 0<i) (hi : i<m)
    (s : State (Fin (2*m+8))) (hz : s.zombie=rail m b (i-1) (by omega))
    (hs : s.survivor=rail m b i hi) :
    ForcesWithin (graph m left true hm)
      (fun p t => p=.survivor ∧ t.zombie=cap m true ∧ t.survivor=capStub m true ∧
        t.damaged (cap m true) ∧
        ∀ j, ∀ hj : j<m, i≤j → t.damaged (rail m b j hj))
      (m-i+1) .survivor s := by
  have hc : i+(m-1-i)=m-1 := by omega
  have first := trailing_route m left true hm (m-1-i) i hip (by omega) b s hz hs
  have hb : m-i+1=(m-1-i)+2 := by omega
  conv => arg 3; rw [hb]
  apply first.bind 2
  intro phase t ht
  obtain ⟨hp,hz',hs',hD⟩ := ht
  subst phase
  have hz'' : t.zombie=rail m b (m-2) (by omega) := by
    have he : i+(m-1-i)-1=m-2 := by omega
    simpa only [he] using hz'
  have hs'' : t.survivor=rail m b (m-1) (by omega) := by simpa only [hc] using hs'
  apply ((capped_exit m hm left b t hz'' hs'').preserve_set t.damaged (fun _ h => h)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.1.2.2.2.2,?_⟩
  intro j hj hij
  by_cases he : j=m-1
  · subst j
    exact hu.1.2.2.2.1
  · have hd := hD (j-i) (by omega)
    have he : i+(j-i)=j := by omega
    have hd' : t.damaged (rail m b j hj) := by simpa only [he] using hd
    exact hu.2 _ hd'

/-- For every two-cap strip of length at least two, entry at the left cap
can cover either complete rail and both caps before the sole nonentry exit. -/
theorem two_cap_entry_route (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=capStub m false) (hs : s.survivor=cap m false) :
    ForcesWithin (graph m true true hm)
      (fun p t => p=.survivor ∧ t.zombie=cap m true ∧ t.survivor=capStub m true ∧
        t.damaged (cap m false) ∧ t.damaged (cap m true) ∧
        ∀ j, ∀ hj : j<m, t.damaged (rail m b j hj))
      (m+2) .survivor s := by
  have hb : m+2=2+(m-1+1) := by omega
  conv => arg 3; rw [hb]
  apply (cap_prefix m hm true b s hz hs).bind (m-1+1)
  intro phase t ht
  obtain ⟨hp,hz',hs',hc,hzero⟩ := ht
  subst phase
  apply ((capped_suffix m hm true b 1 (by omega) (by omega) t hz' hs').preserve_set
    t.damaged (fun _ h => h)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,hu.2 _ hc,hu.1.2.2.2.1,?_⟩
  intro j hj
  cases j with
  | zero => exact hu.2 _ hzero
  | succ j => exact hu.1.2.2.2.2 _ hj (by omega)

end ZombieDamage.OpenStrip
