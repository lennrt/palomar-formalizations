import ZombieDamage.OpenStripCaps

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (left right : Bool)

/-- Monotone rail traversal preserves the stronger trailing configuration,
which permits entry to a cap at the far end. -/
theorem trailing_route (hm : 2≤m) (count i : Nat) (hip : 0<i) (hi : i+count<m)
    (b : Bool) (s : State (Fin (2*m+8)))
    (hz : s.zombie=rail m b (i-1) (by omega)) (hs : s.survivor=rail m b i (by omega)) :
    ForcesWithin (graph m left right hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (i+count-1) (by omega) ∧
        t.survivor=rail m b (i+count) hi ∧
        ∀ k, ∀ hk : k<count, t.damaged (rail m b (i+k) (by omega)))
      count .survivor s := by
  induction count generalizing i s with
  | zero =>
    apply ForcesWithin.done
    refine ⟨rfl,hz,hs,?_⟩
    intro k hk
    omega
  | succ count ih =>
    have hstep := rail_step m left right hm b (i-1) (by omega)
    have he1 : i-1+1=i := by omega
    have he2 : i-1+2=i+1 := by omega
    simp only [he1,he2] at hstep
    have huv : (graph m left right hm).adj s.zombie s.survivor := by
      rw [hz,hs]
      change Adj m left right _ _
      cases b <;> simp [rail,Adj] <;> omega
    have hvw : (graph m left right hm).adj s.survivor (rail m b (i+1) (by omega)) := by
      rw [hs]
      change Adj m left right _ _
      cases b <;> simp [rail,Adj] <;> omega
    apply safe_step (graph m left right hm) s (rail m b (i+1) (by omega)) huv hvw (hz ▸ hstep.1)
    intro z hrep
    rw [hz] at hrep
    let t := (s.survivorTo (rail m b (i+1) (by omega))).zombieTo z
    have hz' : t.zombie=rail m b (i+1-1) (by omega) := by
      simpa only [t, State.zombieTo, Nat.add_sub_cancel] using hstep.2 z hrep
    have hnext := ih (i+1) (by omega) (by omega) t hz' rfl
    have hd : t.damaged (rail m b i (by omega)) := Or.inr hs.symm
    apply (hnext.preserve_set (fun v => v=rail m b i (by omega)) (fun v hv => hv ▸ hd)).mono
    intro p u hu
    have hsum : i+1+count=i+(count+1) := by omega
    refine ⟨hu.1.1,?_,?_,?_⟩
    · simpa only [hsum] using hu.1.2.1
    · simpa only [hsum] using hu.1.2.2.1
    · intro k hk
      cases k with
      | zero => exact hu.2 _ rfl
      | succ k =>
        have hd' := hu.1.2.2.2 k (by omega)
        have he : i+1+k=i+(k+1) := by omega
        simpa only [he] using hd'

end ZombieDamage.OpenStrip
