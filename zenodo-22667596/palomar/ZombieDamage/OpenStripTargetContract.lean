import ZombieDamage.OpenStripExitContract

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (hm : 2≤m)

theorem cap_target_contract (right : Bool) (x : Fin (2*m+8))
    (hx : Internal m true right x) (s : State (Fin (2*m+8)))
    (hz : s.zombie=capStub m false) (hs : s.survivor=cap m false) :
    ForcesWithin (graph m true right hm)
      (TargetExit m hm true right (false,none) x) (2*m) .survivor s := by
  obtain ⟨b,hcover⟩ : ∃ b, x=cap m false ∨ (right=true ∧ x=cap m true) ∨
      ∃ j, ∃ hj : j<m, x=rail m b j hj := by
    rcases hx with ⟨b,j,hj,hx⟩ | ⟨_,hx⟩ | ⟨hr,hx⟩
    · exact ⟨b,Or.inr (Or.inr ⟨j,hj,hx⟩)⟩
    · exact ⟨false,Or.inl hx⟩
    · exact ⟨false,Or.inr (Or.inl ⟨hr,hx⟩)⟩
  cases right with
  | false =>
    apply ((one_cap_entry_route m hm b s hz hs).budget_mono (by omega)).mono
    intro phase t ht
    refine ⟨(true,some b),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,?_⟩
    rcases hcover with he | ⟨h,_⟩ | ⟨j,hj,he⟩
    · exact he ▸ ht.2.2.2.1
    · contradiction
    · exact he ▸ ht.2.2.2.2 j hj
  | true =>
    apply ((two_cap_entry_route m hm b s hz hs).budget_mono (by omega)).mono
    intro phase t ht
    refine ⟨(true,none),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,?_⟩
    rcases hcover with he | ⟨_,he⟩ | ⟨j,hj,he⟩
    · exact he ▸ ht.2.2.2.1
    · exact he ▸ ht.2.2.2.2.1
    · exact he ▸ ht.2.2.2.2.2 j hj

theorem open_target_contract (right a : Bool) (x : Fin (2*m+8))
    (hx : Internal m false right x) (s : State (Fin (2*m+8)))
    (hz : s.zombie=stub m false a) (hs : s.survivor=rail m a 0 (by omega)) :
    ForcesWithin (graph m false right hm)
      (TargetExit m hm false right (false,some a) x) (2*m) .survivor s := by
  rcases hx with ⟨b,j,hj,hx⟩ | ⟨hl,_⟩ | ⟨hr,hx⟩
  · cases right with
    | false =>
      by_cases hab : a=b
      · subst b
        apply ((straight_open_route m hm a s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨(true,some a),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,hx ▸ ht.2.2.2 j hj⟩
      · have hab' : a=(!b) := by cases a <;> cases b <;> simp_all
        have hz' : s.zombie=stub m false (!b) := by rw [hz,hab']
        have hs' : s.survivor=rail m (!b) 0 (by omega) := by rw [hs,hab']
        apply ((crossed_open_route m hm b s hz' hs').budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨(true,some b),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,hx ▸ ht.2.2.2 j hj⟩
    | true =>
      by_cases hab : a=b
      · subst b
        apply ((open_to_cap m hm a s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨(true,none),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,hx ▸ ht.2.2.2.2 j hj⟩
      · have hab' : a=(!b) := by cases a <;> cases b <;> simp_all
        have hz' : s.zombie=stub m false (!b) := by rw [hz,hab']
        have hs' : s.survivor=rail m (!b) 0 (by omega) := by rw [hs,hab']
        apply (crossed_capped_route m hm b s hz' hs').mono
        intro phase t ht
        rcases ht.2.1 with ⟨hzt,hst⟩ | ⟨hzt,hst⟩
        · exact ⟨(true,none),rfl,by simp,⟨ht.1,hzt,hst⟩,hx ▸ ht.2.2 j hj⟩
        · refine ⟨(false,some b),rfl,?_,⟨ht.1,hzt,hst⟩,hx ▸ ht.2.2 j hj⟩
          intro h
          have he := congrArg Prod.snd h
          exact hab (Option.some.inj he).symm
  · contradiction
  · subst right
    apply ((open_to_cap m hm a s hz hs).budget_mono (by omega)).mono
    intro phase t ht
    exact ⟨(true,none),rfl,by simp,⟨ht.1,ht.2.1,ht.2.2.1⟩,hx ▸ ht.2.2.2.1⟩

theorem left_target_contract (left right : Bool) (entry : Option Bool)
    (hin : Active left right (false,entry)) (x : Fin (2*m+8))
    (hx : Internal m left right x) (s : State (Fin (2*m+8)))
    (hz : s.zombie=portStub m (false,entry))
    (hs : s.survivor=portVertex m hm (false,entry)) :
    ForcesWithin (graph m left right hm)
      (TargetExit m hm left right (false,entry) x) (2*m) .survivor s := by
  cases entry with
  | none =>
    have hl : left=true := hin
    subst left
    exact cap_target_contract m hm right x hx s hz hs
  | some a =>
    have hl : left=false := hin
    subst left
    exact open_target_contract m hm right a x hx s hz hs

/-- All entries and all internal targets, uniformly over arbitrary lengths
and all cap patterns. The exit is an active incidence different from entry. -/
theorem target_contract (left right : Bool) (entry : Port)
    (hin : Active left right entry) (x : Fin (2*m+8)) (hx : Internal m left right x)
    (s : State (Fin (2*m+8))) (hz : s.zombie=portStub m entry)
    (hs : s.survivor=portVertex m hm entry) :
    ForcesWithin (graph m left right hm)
      (TargetExit m hm left right entry x) (2*m) .survivor s := by
  rcases entry with ⟨side,e⟩
  cases side with
  | false => exact left_target_contract m hm left right e hin x hx s hz hs
  | true =>
    let F := reflection m hm left right
    have hin' : Active right left (false,e) := (active_flip left right (true,e)).2 hin
    have hz' : (F.state s).zombie=portStub m (false,e) := by
      change reflect m hm s.zombie=_
      rw [hz,reflect_portStub]
      rfl
    have hs' : (F.state s).survivor=portVertex m hm (false,e) := by
      change reflect m hm s.survivor=_
      rw [hs,reflect_portVertex]
      rfl
    have h := left_target_contract m hm right left e hin' (reflect m hm x)
      (internal_reflect m hm left right hx) (F.state s) hz' hs'
    have hback := F.symm.forcesWithin h (Q := TargetExit m hm left right (true,e) x) (by
      intro phase t ht
      obtain ⟨q,hq,hneq,hex,hd⟩ := ht
      refine ⟨flipPort q,(active_flip right left q).2 hq,?_,⟨hex.1,?_,?_⟩,hd⟩
      · intro hh
        have hh' := congrArg flipPort hh
        have heq : q=flipPort (true,e) := by simpa only [flipPort_involutive] using hh'
        exact hneq heq
      · change reflect m hm t.zombie=_
        rw [hex.2.1,reflect_portVertex]
      · change reflect m hm t.survivor=_
        rw [hex.2.2,reflect_portStub])
    simpa only [F.symm_state] using hback

end ZombieDamage.OpenStrip
