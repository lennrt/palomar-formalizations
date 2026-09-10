import ZombieDamage.OpenStripPorts

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (hm : 2≤m)

/-- Prescribed-exit contract from every active left incidence. -/
theorem left_exit_contract (left right : Bool) (entry : Option Bool) (q : Port)
    (hin : Active left right (false,entry)) (hq : Active left right q)
    (hne : q≠(false,entry)) (s : State (Fin (2*m+8)))
    (hz : s.zombie=portStub m (false,entry))
    (hs : s.survivor=portVertex m hm (false,entry)) :
    ForcesWithin (graph m left right hm) (ExitAt m hm q) (2*m) .survivor s := by
  rcases q with ⟨side,out⟩
  cases entry with
  | none =>
    have hl : left=true := hin
    subst left
    cases side with
    | false =>
      cases out with
      | none => exact False.elim (hne rfl)
      | some b => simp [Active,capOn] at hq
    | true =>
      cases out with
      | none =>
        have hr : right=true := hq
        subst right
        apply ((two_cap_entry_route m hm false s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨ht.1,ht.2.1,ht.2.2.1⟩
      | some b =>
        have hr : right=false := hq
        subst right
        apply ((one_cap_entry_route m hm b s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨ht.1,ht.2.1,ht.2.2.1⟩
  | some b =>
    have hl : left=false := hin
    subst left
    cases side with
    | false =>
      cases out with
      | none => simp [Active,capOn] at hq
      | some c =>
        have hb : b=(!c) := by
          cases b <;> cases c <;> simp_all
        subst b
        apply ((near_open_exit m hm right c s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨ht.1,ht.2.1,ht.2.2.1⟩
    | true =>
      cases out with
      | none =>
        have hr : right=true := hq
        subst right
        apply ((open_to_cap m hm b s hz hs).budget_mono (by omega)).mono
        intro phase t ht
        exact ⟨ht.1,ht.2.1,ht.2.2.1⟩
      | some c =>
        have hr : right=false := hq
        subst right
        by_cases hbc : b=c
        · subst c
          apply ((straight_open_route m hm b s hz hs).budget_mono (by omega)).mono
          intro phase t ht
          exact ⟨ht.1,ht.2.1,ht.2.2.1⟩
        · have hb : b=(!c) := by cases b <;> cases c <;> simp_all
          subst b
          apply ((crossed_open_route m hm c s hz hs).budget_mono (by omega)).mono
          intro phase t ht
          exact ⟨ht.1,ht.2.1,ht.2.2.1⟩

/-- Every ordered pair of distinct active incidences, on every strip length
m>=2 and every cap pattern, has a route in at most 2m survivor moves. -/
theorem exit_contract (left right : Bool) (entry q : Port)
    (hin : Active left right entry) (hq : Active left right q) (hne : q≠entry)
    (s : State (Fin (2*m+8))) (hz : s.zombie=portStub m entry)
    (hs : s.survivor=portVertex m hm entry) :
    ForcesWithin (graph m left right hm) (ExitAt m hm q) (2*m) .survivor s := by
  rcases entry with ⟨side,e⟩
  cases side with
  | false => exact left_exit_contract m hm left right e q hin hq hne s hz hs
  | true =>
    let F := reflection m hm left right
    have hin' : Active right left (false,e) := (active_flip left right (true,e)).2 hin
    have hq' := (active_flip left right q).2 hq
    have hne' : flipPort q≠(false,e) := by
      intro hh
      exact hne (flipPort_injective hh)
    have hz' : (F.state s).zombie=portStub m (false,e) := by
      change reflect m hm s.zombie=_
      rw [hz,reflect_portStub]
      rfl
    have hs' : (F.state s).survivor=portVertex m hm (false,e) := by
      change reflect m hm s.survivor=_
      rw [hs,reflect_portVertex]
      rfl
    have h := left_exit_contract m hm right left e (flipPort q) hin' hq' hne'
      (F.state s) hz' hs'
    have hback := F.symm.forcesWithin h (Q := ExitAt m hm q) (by
      intro phase t ht
      refine ⟨ht.1,?_,?_⟩
      · change reflect m hm t.zombie=_
        rw [ht.2.1,reflect_portVertex,flipPort_involutive]
      · change reflect m hm t.survivor=_
        rw [ht.2.2,reflect_portStub,flipPort_involutive])
    simpa only [F.symm_state] using hback

end ZombieDamage.OpenStrip
