import ZombieDamage.ForcedTrace

namespace ZombieDamage.Cyclic
variable {n : Nat}

def shift (hn : 0 < n) (i : Fin n) (a : Nat) : Fin n :=
  ⟨(i.val + a) % n, Nat.mod_lt _ hn⟩

theorem shift_zero (hn : 0 < n) (i : Fin n) : shift hn i 0 = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]

theorem shift_add (hn : 0 < n) (i : Fin n) (a b : Nat) :
    shift hn (shift hn i a) b = shift hn i (a+b) := by
  apply Fin.ext
  simp [shift, Nat.mod_add_mod, Nat.add_assoc]

theorem shift_ne (hn : 0 < n) (i : Fin n) (a : Nat)
    (ha : 0 < a) (han : a < n) : shift hn i a ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  change (i.val+a)%n=i.val at hv
  by_cases hlt : i.val+a<n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have hge : n ≤ i.val+a := by omega
    have hsmall : i.val+a-n<n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsmall] at hv
    omega

theorem shift_n (hn : 0 < n) (i : Fin n) : shift hn i n = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]

theorem shift_injective (hn : 0 < n) (a : Nat) (u v : Fin n)
    (h : shift hn u a = shift hn v a) : u = v := by
  have h' := congrArg (fun i => shift hn i (n-(a%n))) h
  rw [shift_add, shift_add] at h'
  apply Fin.ext
  have hu : (u.val+a+(n-a%n))%n=u.val := by
    rw [Nat.add_mod, Nat.add_mod u.val a]
    have har : a%n<n := Nat.mod_lt _ hn
    have hu := u.isLt
    rw [Nat.mod_eq_of_lt hu]
    rw [Nat.mod_add_mod]
    have he : u.val+a%n+(n-a%n)=u.val+n := by omega
    rw [Nat.add_mod_mod, he]
    simp [Nat.mod_eq_of_lt hu]
  have hv : (v.val+a+(n-a%n))%n=v.val := by
    rw [Nat.add_mod, Nat.add_mod v.val a]
    have har : a%n<n := Nat.mod_lt _ hn
    have hv := v.isLt
    rw [Nat.mod_eq_of_lt hv]
    rw [Nat.mod_add_mod]
    have he : v.val+a%n+(n-a%n)=v.val+n := by omega
    rw [Nat.add_mod_mod, he]
    simp [Nat.mod_eq_of_lt hv]
  have he := congrArg Fin.val h'
  simpa [shift, ← Nat.add_assoc, hu, hv] using he

end ZombieDamage.Cyclic

namespace ZombieDamage.Cyclic
variable {n : Nat}
theorem shift_eq_iff_mod (hn : 0 < n) (u : Fin n) (a b : Nat) :
    shift hn u a = shift hn u b ↔ a%n=b%n := by
  constructor
  · intro h
    let va : Fin n := ⟨a%n, Nat.mod_lt _ hn⟩
    let vb : Fin n := ⟨b%n, Nat.mod_lt _ hn⟩
    have hab : shift hn va u.val = shift hn vb u.val := by
      have ha : shift hn va u.val=shift hn u a := by
        apply Fin.ext
        simp [shift, va, Nat.add_comm]
      have hb : shift hn vb u.val=shift hn u b := by
        apply Fin.ext
        simp [shift, vb, Nat.add_comm]
      exact ha.trans (h.trans hb.symm)
    exact congrArg Fin.val (shift_injective hn u.val va vb hab)
  · intro h
    apply Fin.ext
    change (u.val+a)%n=(u.val+b)%n
    simp only [Nat.add_mod u.val a, Nat.add_mod u.val b, h]

theorem shift_eq_iff_of_lt (hn : 0 < n) (u : Fin n) (a b : Nat)
    (ha : a<n) (hb : b<n) : shift hn u a=shift hn u b ↔ a=b := by
  rw [shift_eq_iff_mod, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
end ZombieDamage.Cyclic
