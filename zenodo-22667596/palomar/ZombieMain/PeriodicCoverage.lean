import ZombieMain.RecurrentDefinitions
import ZombieDamage.MobiusGame

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame ZombieDamage.Cyclic
variable {n : Nat} (G : Graph (Fin n)) (hn : 0 < n)
variable (hedge : ∀ u, G.adj u (shift hn u 1))
variable (htwo : ∀ u, G.TwoApart u (shift hn u 2))
variable (hreply : ∀ u y, G.GeodesicReply u (shift hn u 2) y → y = shift hn u 1)

def periodicController : SurvivorController G where
  Memory := Fin n
  zombie := id
  survivor := fun u => shift hn u 1
  move := fun u => shift hn u 2
  live := by
    intro u he
    change u=shift hn u 1 at he
    exact G.loopless u (by simpa only [← he] using hedge u)
  legal := fun u => ⟨(htwo u).1.symm, Or.inr (by
    change G.adj (shift hn u 1) (shift hn u 2)
    have h := hedge (shift hn u 1)
    simpa only [shift_add] using h)⟩
  replies := fun u => (twoApart_zombie_turn G (htwo u)).1
  safe := fun u => (twoApart_zombie_turn G (htwo u)).2
  next := fun _ y _ => y
  next_zombie := fun _ _ _ => rfl
  next_survivor := by
    intro u y h
    rw [hreply u y h, shift_add]

theorem periodicController_recurrent :
    (periodicController G hn hedge htwo hreply).Recurrent := by
  intro m h x N
  have hstep : ∀ t, m (t+1) = shift hn (m t) 1 := by
    intro t
    obtain ⟨y,hy,he⟩ := h t
    change y=m (t+1) at he
    rw [← he]
    exact hreply (m t) y hy
  have hm : ∀ t, m t = shift hn (m 0) t := by
    intro t
    induction t with
    | zero => exact (shift_zero hn (m 0)).symm
    | succ t ih => rw [hstep, ih, shift_add]
  obtain ⟨k,hk,hx⟩ := CycleGame.covers hn (m 0) x (N+1)
  refine ⟨N+k, by omega, ?_⟩
  change shift hn (m (N+k)) 1=x
  rw [hm,shift_add]
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx

include hn hedge htwo hreply
/-- A periodic forced trace supplies a fixed infinite controller and a safe
initial zombie turn, with zero survivor moves needed for initialization. -/
theorem periodic_recurrent_coverage : RecurrentCoverageWithin G 0 := by
  refine ⟨periodicController G hn hedge htwo hreply,
    periodicController_recurrent G hn hedge htwo hreply, ?_⟩
  intro z
  refine ⟨shift hn z 2,(htwo z).1,?_⟩
  apply ForcesWithin.zombie 0 _ (htwo z).1
    (twoApart_zombie_turn G (htwo z)).1 (twoApart_zombie_turn G (htwo z)).2
  intro y hy
  apply ForcesWithin.done
  refine ⟨rfl,shift hn z 1,hreply z y hy |>.symm,?_⟩
  change shift hn (shift hn z 1) 1=shift hn z 2
  exact shift_add hn z 1 1

omit hn hedge htwo hreply in
theorem mobius_recurrent_coverage {m : Nat} (hm : 4 ≤ m) :
    RecurrentCoverageWithin (MobiusGame.graph hm) 0 :=
  periodic_recurrent_coverage (MobiusGame.graph hm) (MobiusGame.pos hm)
    (fun _ => Or.inl rfl) (MobiusGame.twoApart hm) (MobiusGame.reply hm)

end ZombieMain
