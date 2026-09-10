import ZombieMain.BoundaryDefinitions
import ZombieDamage.DiamondRing

namespace ZombieMain
open ZombieDamage ZombieDamage.DiamondRing

/-- Counting the disjoint central pairs in the known diamond-ring sensor
obstruction. This is not a new metric-dimension priority claim. -/
theorem diamond_ring_sensor_bound (k : Nat) (S : Finset (Vertex k))
    (h : Nat) (hh : 1 ≤ h) (hrec : (graph k).Recovers (fun v => v∈S) h) :
    k+3 ≤ S.card := by
  classical
  have hex : ∀ i : Fin (k+3), ∃ v : {v // v∈S}, v.val.1=i := by
    intro i
    rcases central_pair_sensor k (fun v => v∈S) h hh hrec i with ha | hb
    · exact ⟨⟨(i,.a),ha⟩,rfl⟩
    · exact ⟨⟨(i,.b),hb⟩,rfl⟩
  let f : Fin (k+3) → {v // v∈S} := fun i => Classical.choose (hex i)
  have hi : Function.Injective f := by
    intro i j he
    have h := congrArg (fun v : {v // v∈S} => v.val.1) he
    exact (Classical.choose_spec (hex i)).symm.trans (h.trans (Classical.choose_spec (hex j)))
  simpa using Fintype.card_le_of_injective f hi

end ZombieMain
