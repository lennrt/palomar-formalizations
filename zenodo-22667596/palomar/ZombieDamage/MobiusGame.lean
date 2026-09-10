import ZombieDamage.CycleGame

/-! The all-orders Möbius-ladder part of the manuscript, in the full game. -/
namespace ZombieDamage.MobiusGame
open Cyclic FullGame
variable {m : Nat}
theorem pos (hm : 4 ≤ m) : 0 < 2*m := by omega

def adjacency (hm : 4 ≤ m) (u v : Fin (2*m)) : Prop :=
  v = shift (pos hm) u 1 ∨ v = shift (pos hm) u (2*m-1) ∨
    v = shift (pos hm) u m

def graph (hm : 4 ≤ m) : Graph (Fin (2*m)) where
  adj := adjacency hm
  symm := by
    intro u v h
    rcases h with h | h | h
    · apply Or.inr; apply Or.inl
      rw [h, shift_add]
      have he : 1+(2*m-1)=2*m := by omega
      rw [he, shift_n]
    · apply Or.inl
      rw [h, shift_add]
      have he : 2*m-1+1=2*m := by omega
      rw [he, shift_n]
    · apply Or.inr; apply Or.inr
      rw [h, shift_add]
      have he : m+m=2*m := by omega
      rw [he, shift_n]
  loopless := by
    intro u h
    rcases h with h | h | h
    · exact shift_ne (pos hm) u 1 (by omega) (by omega) h.symm
    · exact shift_ne (pos hm) u (2*m-1) (by omega) (by omega) h.symm
    · exact shift_ne (pos hm) u m (by omega) (by omega) h.symm

theorem twoApart (hm : 4 ≤ m) (u : Fin (2*m)) :
    (graph hm).TwoApart u (shift (pos hm) u 2) := by
  refine ⟨(shift_ne (pos hm) u 2 (by omega) (by omega)).symm, ?_,
    shift (pos hm) u 1, Or.inl rfl, Or.inl ?_⟩
  · intro h
    rcases h with h | h | h
    · have hh := (shift_eq_iff_of_lt (pos hm) u 2 1 (by omega) (by omega)).1 h
      omega
    · have hh := (shift_eq_iff_of_lt (pos hm) u 2 (2*m-1) (by omega) (by omega)).1 h
      omega
    · have hh := (shift_eq_iff_of_lt (pos hm) u 2 m (by omega) (by omega)).1 h
      omega
  · exact (shift_add (pos hm) u 1 1).symm

/-- Six unwanted combinations of jumps are excluded without any cutoff. -/
theorem jump_not_two (hm : 4 ≤ m) (a b : Nat)
    (ha : a=2*m-1 ∨ a=m) (hb : b=1 ∨ b=2*m-1 ∨ b=m) :
    (a+b)%(2*m) ≠ 2 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb | hb
  all_goals rw [ha, hb]
  all_goals intro h
  · have he : 2*m-1+1=2*m := by omega
    rw [he, Nat.mod_self] at h
    omega
  · have hge : 2*m ≤ (2*m-1)+(2*m-1) := by omega
    have hlt : (2*m-1)+(2*m-1)-2*m<2*m := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at h
    omega
  · have hge : 2*m ≤ (2*m-1)+m := by omega
    have hlt : (2*m-1)+m-2*m<2*m := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at h
    omega
  · have hlt : m+1<2*m := by omega
    rw [Nat.mod_eq_of_lt hlt] at h
    omega
  · have hge : 2*m ≤ m+(2*m-1) := by omega
    have hlt : m+(2*m-1)-2*m<2*m := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt] at h
    omega
  · have he : m+m=2*m := by omega
    rw [he, Nat.mod_self] at h
    omega

theorem reply (hm : 4 ≤ m) (u x : Fin (2*m))
    (h : (graph hm).GeodesicReply u (shift (pos hm) u 2) x) :
    x = shift (pos hm) u 1 := by
  obtain ⟨hux, hxv⟩ := ((graph hm).geodesicReply_iff_commonNeighbor (twoApart hm u)).1 h
  rcases hux with h | h | h
  · exact h
  all_goals
    have hx : ∃ a, (a=2*m-1 ∨ a=m) ∧ x=shift (pos hm) u a := by
      first | exact ⟨2*m-1, Or.inl rfl, h⟩ | exact ⟨m, Or.inr rfl, h⟩
    obtain ⟨a, ha, hxa⟩ := hx
    have hy : ∃ b, (b=1 ∨ b=2*m-1 ∨ b=m) ∧
        shift (pos hm) u 2=shift (pos hm) x b := by
      rcases hxv with h | h | h
      · exact ⟨1, Or.inl rfl, h⟩
      · exact ⟨2*m-1, Or.inr (Or.inl rfl), h⟩
      · exact ⟨m, Or.inr (Or.inr rfl), h⟩
    obtain ⟨b, hb, he⟩ := hy
    rw [hxa, shift_add] at he
    have hr := (shift_eq_iff_mod (pos hm) u 2 (a+b)).1 he
    rw [Nat.mod_eq_of_lt (show 2<2*m by omega)] at hr
    exact False.elim (jump_not_two hm a b ha hb hr.symm)

theorem full_damage (hm : 4 ≤ m) : FullDamageWithin (graph hm) (2*m) := by
  apply fullDamage_of_forced_traces (graph hm) (2*m)
  intro z
  refine ⟨fun i => shift (pos hm) z i, shift_zero (pos hm) z, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro i
      exact Or.inl (shift_add (pos hm) z i 1).symm
    · intro i
      have h := twoApart hm (shift (pos hm) z i)
      simpa [shift_add] using h
    · intro i x hx
      have h := reply hm (shift (pos hm) z i) x
      rw [shift_add, shift_add] at h
      exact h hx
  · intro v
    exact CycleGame.covers (pos hm) z v 2

end ZombieDamage.MobiusGame
