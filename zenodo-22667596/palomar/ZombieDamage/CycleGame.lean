import ZombieDamage.Cyclic

/-! Davila's full-damage cycle result for EVERY n ≥ 5, with the original
initial move order and exactly n survivor departures. -/
namespace ZombieDamage.CycleGame
open Cyclic FullGame

variable {n : Nat}
theorem pos (hn : 5 ≤ n) : 0 < n := by omega

def graph (hn : 5 ≤ n) : Graph (Fin n) where
  adj u v := v = shift (pos hn) u 1 ∨ u = shift (pos hn) v 1
  symm := fun h => h.symm
  loopless := by
    intro v hv
    have hne := shift_ne (pos hn) v 1 (by omega) (by omega)
    rcases hv with h | h <;> exact hne h.symm

theorem twoApart (hn : 5 ≤ n) (u : Fin n) :
    (graph hn).TwoApart u (shift (pos hn) u 2) := by
  have hne := shift_ne (pos hn) u 2 (by omega) (by omega)
  refine ⟨hne.symm, ?_, shift (pos hn) u 1, Or.inl rfl, ?_⟩
  · intro ha
    rcases ha with he | he
    · have hbad := shift_ne (pos hn) (shift (pos hn) u 1) 1 (by omega) (by omega)
      apply hbad
      simpa [shift_add] using he
    · have hbad := shift_ne (pos hn) u 3 (by omega) (by omega)
      apply hbad
      simpa [shift_add] using he.symm
  · apply Or.inl
    exact (shift_add (pos hn) u 1 1).symm

theorem reply (hn : 5 ≤ n) (u x : Fin n)
    (h : (graph hn).GeodesicReply u (shift (pos hn) u 2) x) :
    x = shift (pos hn) u 1 := by
  obtain ⟨hux, hxv⟩ := ((graph hn).geodesicReply_iff_commonNeighbor (twoApart hn u)).1 h
  rcases hux with h | h
  · exact h
  · rcases hxv with hx | hx
    · exact False.elim ((twoApart hn u).1 (h.trans hx.symm))
    · have he : u = shift (pos hn) u 4 := by
        rw [hx] at h
        simpa [shift_add] using h
      exact False.elim ((shift_ne (pos hn) u 4 (by omega) (by omega)) he.symm)

theorem forcedTrace (hn : 5 ≤ n) (z : Fin n) :
    FullGame.ForcedTrace (graph hn) (fun i => shift (pos hn) z i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact Or.inl (shift_add (pos hn) z i 1).symm
  · intro i
    have h := twoApart hn (shift (pos hn) z i)
    simpa [shift_add] using h
  · intro i x hx
    have h := reply hn (shift (pos hn) z i) x
    rw [shift_add, shift_add] at h
    exact h hx

/-- Every consecutive block of n shifts contains every vertex. -/
theorem covers (hn : 0 < n) (z v : Fin n) (offset : Nat) :
    ∃ k, k < n ∧ shift hn z (offset+k) = v := by
  let a := shift hn z offset
  let k := (v.val+n-a.val)%n
  have hk : k<n := Nat.mod_lt _ hn
  refine ⟨k, hk, ?_⟩
  rw [← shift_add]
  change shift hn a k=v
  apply Fin.ext
  change (a.val+(v.val+n-a.val)%n)%n=v.val
  rw [Nat.add_mod_mod]
  have hsum : a.val+(v.val+n-a.val)=v.val+n := by omega
  rw [hsum]
  simp [Nat.mod_eq_of_lt v.isLt]

/-- All-orders formal verification of the n ≥ 5 part of Davila Theorem 6. -/
theorem full_damage (hn : 5 ≤ n) : FullDamageWithin (graph hn) n := by
  apply fullDamage_of_forced_traces (graph hn) n
  intro z
  refine ⟨fun i => shift (pos hn) z i, shift_zero (pos hn) z,
    forcedTrace hn z, ?_⟩
  intro v
  exact covers (pos hn) z v 2

end ZombieDamage.CycleGame
