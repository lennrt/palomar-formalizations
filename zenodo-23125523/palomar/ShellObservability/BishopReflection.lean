module

public import Mathlib

@[expose] public section

/-! The arithmetic reflection obstruction behind even-order bishop domination. -/

namespace ShellObservability.BishopReflection

/-- If only even diagonal indices carry mass and reflection about an odd
midpoint preserves that mass, the total is twice the lower-half total. -/
theorem reflected_sum_twice (N : ℕ) (p : ℕ → ℕ)
    (hN : N % 2 = 1)
    (hodd : ∀ s ≤ 2*N, s % 2 = 1 → p s = 0)
    (href : ∀ s ≤ N, s % 2 = 0 → p s = p (2*N-s)) :
    (∑ s ∈ Finset.range (2*N+1), p s) = 2 * ∑ s ∈ Finset.range N, p s := by
  have hmid : p N = 0 := hodd N (by omega) hN
  have hreflect : ∀ s ≤ N, p s = p (2*N-s) := by
    intro s hs
    by_cases he : s % 2 = 0
    · exact href s hs he
    · have ho : s % 2 = 1 := by omega
      have ho' : (2*N-s) % 2 = 1 := by omega
      rw [hodd s (by omega) ho, hodd (2*N-s) (by omega) ho']
  have hlast : (∑ i ∈ Finset.range N, p (N+1+i)) = ∑ i ∈ Finset.range N, p i := by
    calc
      _ = ∑ i ∈ Finset.range N, p (N-1-i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < N := Finset.mem_range.mp hi
        have hr := hreflect (N-1-i) (by omega)
        have hind : 2*N-(N-1-i) = N+1+i := by omega
        rw [hind] at hr
        exact hr.symm
      _ = _ := Finset.sum_range_reflect p N
  have hind : 2*N+1 = (N+1)+N := by omega
  rw [hind, Finset.sum_range_add, Finset.sum_range_succ, hmid, hlast]
  omega

/-- In particular, an odd prescribed total cannot satisfy those reflections. -/
theorem reflected_sum_even (N : ℕ) (p : ℕ → ℕ)
    (hN : N % 2 = 1)
    (hodd : ∀ s ≤ 2*N, s % 2 = 1 → p s = 0)
    (href : ∀ s ≤ N, s % 2 = 0 → p s = p (2*N-s)) :
    (∑ s ∈ Finset.range (2*N+1), p s) % 2 = 0 := by
  rw [reflected_sum_twice N p hN hodd href]
  omega

/-- Finite-indexed form for a literal array of diagonal loads. -/
theorem fin_reflected_sum_even (N : ℕ) (p : Fin (2*N+1) → ℕ)
    (hN : N % 2 = 1)
    (hodd : ∀ s, s.val % 2 = 1 → p s = 0)
    (href : ∀ s, s.val ≤ N → s.val % 2 = 0 →
      p s = p ⟨2*N-s.val, by omega⟩) :
    (∑ s, p s) % 2 = 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  apply reflected_sum_even N _ hN
  · intro s hs ho
    rw [dif_pos (by omega)]
    exact hodd ⟨s,by omega⟩ ho
  · intro s hs he
    rw [dif_pos (by omega), dif_pos (by omega)]
    exact href ⟨s,by omega⟩ hs he

end ShellObservability.BishopReflection
