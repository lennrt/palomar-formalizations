import ZombieDamage.CycleGame
import ZombieDamage.ForcedTraceRoute

namespace ZombieDamage.PrismGame
open Cyclic FullGame
variable {m : Nat}

def graph (hm : 5 ≤ m) : Graph (Fin m × Bool) where
  adj u v := (u.2=v.2 ∧ (CycleGame.graph hm).adj u.1 v.1) ∨
    (u.1=v.1 ∧ u.2≠v.2)
  symm := by
    intro u v h
    rcases h with ⟨hs,hi⟩ | ⟨hi,hs⟩
    · exact Or.inl ⟨hs.symm,(CycleGame.graph hm).symm hi⟩
    · exact Or.inr ⟨hi.symm,hs.symm⟩
  loopless := by
    intro u h
    rcases h with ⟨_,hi⟩ | ⟨_,hs⟩
    · exact (CycleGame.graph hm).loopless u.1 hi
    · exact hs rfl

theorem rail_twoApart (hm : 5 ≤ m) (i : Fin m) (b : Bool) :
    (graph hm).TwoApart (i,b) (shift (CycleGame.pos hm) i 2,b) := by
  have ht := CycleGame.twoApart hm i
  refine ⟨?_, ?_, (shift (CycleGame.pos hm) i 1,b),
    Or.inl ⟨rfl,Or.inl rfl⟩,Or.inl ⟨rfl,Or.inl ?_⟩⟩
  · intro h
    exact ht.1 (congrArg Prod.fst h)
  · intro h
    rcases h with ⟨_,hi⟩ | ⟨_,hs⟩
    · exact ht.2.1 hi
    · exact hs rfl
  · exact (shift_add (CycleGame.pos hm) i 1 1).symm

theorem rail_reply (hm : 5 ≤ m) (i : Fin m) (b : Bool) (x : Fin m × Bool)
    (h : (graph hm).GeodesicReply (i,b) (shift (CycleGame.pos hm) i 2,b) x) :
    x=(shift (CycleGame.pos hm) i 1,b) := by
  obtain ⟨hix,hxw⟩ := ((graph hm).geodesicReply_iff_commonNeighbor (rail_twoApart hm i b)).1 h
  rcases hix with ⟨hb,hi⟩ | ⟨hi,hb⟩
  · rcases hxw with ⟨_,hw⟩ | ⟨_,hw⟩
    · have hgeo := ((CycleGame.graph hm).geodesicReply_iff_commonNeighbor (CycleGame.twoApart hm i)).2 ⟨hi,hw⟩
      exact Prod.ext (CycleGame.reply hm i x.1 hgeo) hb.symm
    · exact False.elim (hw hb.symm)
  · rcases hxw with ⟨hw,_⟩ | ⟨hw,_⟩
    · exact False.elim (hb hw.symm)
    · exact False.elim ((CycleGame.twoApart hm i).1 (hi.trans hw))

theorem rung_twoApart (hm : 5 ≤ m) (i : Fin m) (b : Bool) :
    (graph hm).TwoApart (i,!b) (shift (CycleGame.pos hm) i 1,b) := by
  have hne := shift_ne (CycleGame.pos hm) i 1 (by omega) (by omega)
  refine ⟨?_, ?_, (i,b), Or.inr ⟨rfl,by cases b <;> simp⟩,
    Or.inl ⟨rfl,Or.inl rfl⟩⟩
  · intro h
    exact hne (congrArg Prod.fst h).symm
  · intro h
    rcases h with ⟨hb,_⟩ | ⟨hi,_⟩
    · cases b <;> cases hb
    · exact hne hi.symm

theorem rung_reply (hm : 5 ≤ m) (i : Fin m) (b : Bool) (x : Fin m × Bool)
    (h : (graph hm).GeodesicReply (i,!b) (shift (CycleGame.pos hm) i 1,b) x) :
    x=(i,b) ∨ x=(shift (CycleGame.pos hm) i 1,!b) := by
  obtain ⟨hix,hxw⟩ := ((graph hm).geodesicReply_iff_commonNeighbor (rung_twoApart hm i b)).1 h
  rcases hix with ⟨hb,_⟩ | ⟨hi,hb⟩
  · rcases hxw with ⟨hw,_⟩ | ⟨hw,_⟩
    · have he := hb.trans hw
      cases b <;> cases he
    · exact Or.inr (Prod.ext hw hb.symm)
  · have hside : x.2=b := by cases b <;> cases h : x.2 <;> simp_all
    exact Or.inl (Prod.ext hi.symm hside)

theorem rail_forcedTrace (hm : 5 ≤ m) (z : Fin m) (b : Bool) :
    ForcedTrace (graph hm) (fun k => (shift (CycleGame.pos hm) z k,b)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    exact Or.inl ⟨rfl,Or.inl (shift_add (CycleGame.pos hm) z k 1).symm⟩
  · intro k
    have h := rail_twoApart hm (shift (CycleGame.pos hm) z k) b
    simpa [shift_add] using h
  · intro k x hx
    have h := rail_reply hm (shift (CycleGame.pos hm) z k) b x
    rw [shift_add,shift_add] at h
    exact h hx

theorem back_forward (hm : 5 ≤ m) (i : Fin m) :
    shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i (m-1)) 1=i := by
  rw [shift_add]
  have h : m-1+1=m := by omega
  rw [h, shift_n]

theorem forward_back (hm : 5 ≤ m) (i : Fin m) :
    shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i 1) (m-1)=i := by
  rw [shift_add]
  have h : 1+(m-1)=m := by omega
  rw [h, shift_n]

theorem back_two (hm : 5 ≤ m) (i : Fin m) :
    shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i (m-1)) 2=
      shift (CycleGame.pos hm) i 1 := by
  rw [← shift_add (CycleGame.pos hm) (shift (CycleGame.pos hm) i (m-1)) 1 1]
  rw [back_forward hm i]

def Forward (hm : 5 ≤ m) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) : Prop :=
  s.survivor=(i,b) ∧ (s.zombie=(shift (CycleGame.pos hm) i (m-1),b) ∨
    s.zombie=(i,!b))

theorem forward_step (hm : 5 ≤ m) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) (hf : Forward hm i b s) :
    (graph hm).adj s.zombie s.survivor ∧
    (graph hm).adj s.survivor (shift (CycleGame.pos hm) i 1,b) ∧
    (graph hm).TwoApart s.zombie (shift (CycleGame.pos hm) i 1,b) ∧
    ∀ z, (graph hm).GeodesicReply s.zombie (shift (CycleGame.pos hm) i 1,b) z →
      Forward hm (shift (CycleGame.pos hm) i 1) b
        ((s.survivorTo (shift (CycleGame.pos hm) i 1,b)).zombieTo z) := by
  obtain ⟨hs,hz⟩ := hf
  have hedge : (graph hm).adj s.survivor (shift (CycleGame.pos hm) i 1,b) := by
    rw [hs]
    exact Or.inl ⟨rfl,Or.inl rfl⟩
  rcases hz with hz | hz
  · have huv : (graph hm).adj s.zombie s.survivor := by
      rw [hz,hs]
      exact Or.inl ⟨rfl,Or.inl (back_forward hm i).symm⟩
    have ht := rail_twoApart hm (shift (CycleGame.pos hm) i (m-1)) b
    rw [back_two hm i] at ht
    refine ⟨huv,hedge,hz ▸ ht,?_⟩
    intro z hreply
    rw [hz] at hreply
    have hrep := rail_reply hm (shift (CycleGame.pos hm) i (m-1)) b z
    rw [back_two hm i,back_forward hm i] at hrep
    have he := hrep hreply
    refine ⟨rfl,Or.inl ?_⟩
    change z=(shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i 1) (m-1),b)
    rw [forward_back hm i]
    exact he
  · have huv : (graph hm).adj s.zombie s.survivor := by
      rw [hz,hs]
      exact Or.inr ⟨rfl,by cases b <;> simp⟩
    refine ⟨huv,hedge,hz ▸ rung_twoApart hm i b,?_⟩
    intro z hreply
    rw [hz] at hreply
    have hrep := rung_reply hm i b z hreply
    refine ⟨rfl,?_⟩
    rcases hrep with ht | hr
    · apply Or.inl
      change z=(shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i 1) (m-1),b)
      rw [forward_back hm i]
      exact ht
    · exact Or.inr hr

theorem forward_cover (hm : 5 ≤ m) (count : Nat) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) (hf : Forward hm i b s) :
    ForcesWithin (graph hm) (fun _ t => ∀ k, k<count →
      t.damaged (shift (CycleGame.pos hm) i k,b)) count .survivor s := by
  induction count generalizing i s with
  | zero =>
    apply ForcesWithin.done
    intro k hk
    omega
  | succ count ih =>
    obtain ⟨huv,hvw,ht,hnext⟩ := forward_step hm i b s hf
    apply safe_step (graph hm) s (shift (CycleGame.pos hm) i 1,b) huv hvw ht
    intro z hz
    let t := (s.survivorTo (shift (CycleGame.pos hm) i 1,b)).zombieTo z
    have h := ih (shift (CycleGame.pos hm) i 1) t (hnext z hz)
    have hD : t.damaged (i,b) := Or.inr hf.1.symm
    apply (h.preserve_set (fun v => v=(i,b)) (fun v hv => hv ▸ hD)).mono
    intro _ u hu k hk
    cases k with
    | zero =>
      simpa [shift_zero] using hu.2 (i,b) rfl
    | succ k =>
      have hk' : k<count := by omega
      have hdk := hu.1 k hk'
      simpa [shift_add,Nat.add_comm] using hdk

theorem whole_rail (hm : 5 ≤ m) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) (hf : Forward hm i b s) :
    ForcesWithin (graph hm) (fun _ t => ∀ j, t.damaged (j,b)) m .survivor s := by
  apply (forward_cover hm m i b s hf).mono
  intro _ t ht j
  obtain ⟨k,hk,he⟩ := CycleGame.covers (CycleGame.pos hm) i j 0
  have hd := ht k hk
  simp only [Nat.zero_add] at he
  exact he ▸ hd

theorem cross_rung (hm : 5 ≤ m) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) (hz : s.zombie=(i,b))
    (hs : s.survivor=(shift (CycleGame.pos hm) i 1,b)) :
    ForcesWithin (graph hm) (fun _ t => (∀ j, t.damaged (j,!b)) ∧
      t.damaged (shift (CycleGame.pos hm) i 1,b)) (m+1) .survivor s := by
  have huv : (graph hm).adj s.zombie s.survivor := by
    rw [hz,hs]
    exact Or.inl ⟨rfl,Or.inl rfl⟩
  have hvw : (graph hm).adj s.survivor (shift (CycleGame.pos hm) i 1,!b) := by
    rw [hs]
    exact Or.inr ⟨rfl,by cases b <;> simp⟩
  have ht : (graph hm).TwoApart s.zombie (shift (CycleGame.pos hm) i 1,!b) := by
    rw [hz]
    simpa using rung_twoApart hm i (!b)
  apply safe_step (graph hm) s (shift (CycleGame.pos hm) i 1,!b) huv hvw ht
  intro z hr
  rw [hz] at hr
  have hrep : z=(i,!b) ∨ z=(shift (CycleGame.pos hm) i 1,b) := by
    have h := rung_reply hm i (!b) z
    simp only [Bool.not_not] at h
    exact h hr
  let t := (s.survivorTo (shift (CycleGame.pos hm) i 1,!b)).zombieTo z
  have hf : Forward hm (shift (CycleGame.pos hm) i 1) (!b) t := by
    refine ⟨rfl,?_⟩
    rcases hrep with he | he
    · apply Or.inl
      change z=(shift (CycleGame.pos hm) (shift (CycleGame.pos hm) i 1) (m-1),!b)
      rw [forward_back hm i]
      exact he
    · apply Or.inr
      simpa [t,State.zombieTo] using he
  have hD : t.damaged (shift (CycleGame.pos hm) i 1,b) := Or.inr hs.symm
  have h := (whole_rail hm (shift (CycleGame.pos hm) i 1) (!b) t hf).preserve_set
    (fun v => v=(shift (CycleGame.pos hm) i 1,b)) (fun v hv => hv ▸ hD)
  apply h.mono
  intro _ u hu
  exact ⟨hu.1,hu.2 _ rfl⟩

theorem from_trailing (hm : 5 ≤ m) (i : Fin m) (b : Bool)
    (s : State (Fin m × Bool)) (hz : s.zombie=(shift (CycleGame.pos hm) i 1,b))
    (hs : s.survivor=(shift (CycleGame.pos hm) i 2,b)) :
    ForcesWithin (graph hm) (fun _ => AllDamaged) (2*m) .survivor s := by
  let f := fun k => (shift (CycleGame.pos hm) i k,b)
  have first := forced_trace_route (graph hm) f (rail_forcedTrace hm i b) (m-1) 0 s hz hs
  have hbound : (m-1)+(m+1)=2*m := by omega
  rw [← hbound]
  apply first.bind (m+1)
  intro phase t hfirst
  obtain ⟨hp,hzt,hst,hpre⟩ := hfirst
  subst phase
  have he1 : 0+1+(m-1)=m := by omega
  have he2 : 0+2+(m-1)=m+1 := by omega
  have sh1 : shift (CycleGame.pos hm) i (m+1)=shift (CycleGame.pos hm) i 1 := by
    rw [← shift_add (CycleGame.pos hm) i m 1, shift_n]
  have hzt' : t.zombie=(i,b) := by simpa [f,he1,shift_n] using hzt
  have hst' : t.survivor=(shift (CycleGame.pos hm) i 1,b) := by
    simpa [f,he2,sh1] using hst
  have hcross := (cross_rung hm i b t hzt' hst').preserve_set t.damaged (fun _ h => h)
  apply hcross.mono
  intro _ u hu v
  rcases v with ⟨j,r⟩
  by_cases hr : r=b
  · subst r
    obtain ⟨k,hk,he⟩ := CycleGame.covers (CycleGame.pos hm) i j 2
    by_cases hk' : k<m-1
    · have hd := hpre k hk'
      have hd' : t.damaged (j,b) := by simpa [f,he] using hd
      exact hu.2 _ hd'
    · have hke : k=m-1 := by omega
      have hsum : 2+k=m+1 := by omega
      have hj : shift (CycleGame.pos hm) i 1=j := by simpa [hsum,sh1] using he
      exact hj ▸ hu.1.2
  · have hr' : r = !b := by cases r <;> cases b <;> simp_all
    subst r
    exact hu.1.1 j

/-- Full damage in exactly the paper's bound of 2m survivor moves, for every
prism parameter m ≥ 5 and every adversarial sequence of geodesic replies. -/
theorem full_damage (hm : 5 ≤ m) : FullDamageWithin (graph hm) (2*m) := by
  rintro ⟨i,b⟩
  have ht := rail_twoApart hm i b
  refine ⟨(shift (CycleGame.pos hm) i 2,b),ht.1,?_⟩
  apply ForcesWithin.zombie (2*m) _ ht.1 (twoApart_zombie_turn (graph hm) ht).1
    (twoApart_zombie_turn (graph hm) ht).2
  intro z hz
  exact from_trailing hm i b _ (rail_reply hm i b z hz) rfl

end ZombieDamage.PrismGame
