import ZombieDamage.ForcedTrace

namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

/-- Finite forced traversal with both endpoint positions retained, allowing
composition with a later strategy that changes direction or crosses a rung. -/
theorem forced_trace_route (f : Nat → V) (hf : ForcedTrace G f)
    (count i : Nat) (s : State V)
    (hz : s.zombie = f (i+1)) (hs : s.survivor = f (i+2)) :
    ForcesWithin G (fun p t => p = .survivor ∧
      t.zombie = f (i+1+count) ∧ t.survivor = f (i+2+count) ∧
      ∀ k, k < count → t.damaged (f (i+2+k))) count .survivor s := by
  induction count generalizing i s with
  | zero =>
    apply ForcesWithin.done
    refine ⟨rfl, hz, hs, ?_⟩
    intro k hk
    omega
  | succ count ih =>
    have huv : G.adj s.zombie s.survivor := by rw [hz, hs]; exact hf.1 (i+1)
    have hvw : G.adj s.survivor (f (i+3)) := by rw [hs]; exact hf.1 (i+2)
    have htwo : G.TwoApart s.zombie (f (i+3)) := by rw [hz]; exact hf.2.1 (i+1)
    apply safe_step G s (f (i+3)) huv hvw htwo
    intro z hreply
    have hz' : z=f (i+2) := hf.2.2 (i+1) z (hz ▸ hreply)
    let t := (s.survivorTo (f (i+3))).zombieTo z
    have ht := ih (i+1) t hz' rfl
    have hD : t.damaged (f (i+2)) := Or.inr hs.symm
    have hkeep := ht.preserve_set (fun v => v=f (i+2)) (fun v hv => hv ▸ hD)
    apply hkeep.mono
    intro p u hu
    refine ⟨hu.1.1, ?_, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu.1.2.1
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu.1.2.2.1
    · intro k hk
      cases k with
      | zero => exact hu.2 _ rfl
      | succ k =>
        have hlt : k<count := by omega
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu.1.2.2.2 k hlt

end ZombieDamage.FullGame
