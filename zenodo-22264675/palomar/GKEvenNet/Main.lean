/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Author: Lennart Rudolph
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import GKEvenNet.Certificate

/-!
# Main statements in the order parameter `m = 2 r`

The development is parametrized by `s` with `m = 2 s + 4`.  This file restates the
results for the reader in terms of `r = m / 2 ≥ 2`, with the point coordinates written as
in the source header, using the closed form `2 ^ r * rev r k` for its 32-bit reversal term:

  `X r k j = (2 ^ r · rev r k + ⌊k / 4⌋ + 2 ^ (r - 2) · (j + 1)) mod 2 ^ (2 r)`,
  `Y r k j = k + 2 ^ r · j`,

for `0 ≤ k, j < 2 ^ r`.
-/

namespace GKEvenNet

/-- First integer coordinate for even order `m = 2 r`, `r ≥ 2`. -/
def X (r k j : ℕ) : ℕ := (2 ^ r * rev r k + k / 4 + 2 ^ (r - 2) * (j + 1)) % 2 ^ (2 * r)

/-- Second integer coordinate for even order `m = 2 r`. -/
def Y (r k j : ℕ) : ℕ := k + 2 ^ r * j

theorem X_eq (s k j : ℕ) : X (s + 2) k j = xc s k j := by
  unfold X xc
  rw [Nat.add_sub_cancel, show 2 * (s + 2) = 2 * s + 4 by ring]

theorem Y_eq (s k j : ℕ) : Y (s + 2) k j = yc s k j := rfl

/-- **Theorem A** (classical form).  For every even `m = 2 r ≥ 4`, every resolution
`a ≤ m`, and every dyadic box `(bx, by)` with `bx < 2 ^ a`, `by < 2 ^ (m - a)`, exactly one
index pair `(k, j)` with `k, j < 2 ^ r` has its point in that box, i.e.
`⌊X / 2 ^ (m - a)⌋ = bx` and `⌊Y / 2 ^ a⌋ = by`.  Hence the `2 ^ m` normalized points form a
`(0, m, 2)`-net in base 2. -/
theorem net (r : ℕ) (hr : 2 ≤ r) (a : ℕ) (ha : a ≤ 2 * r)
    (bx by_ : ℕ) (hbx : bx < 2 ^ a) (hby : by_ < 2 ^ (2 * r - a)) :
    ∃! p : ℕ × ℕ, p.1 < 2 ^ r ∧ p.2 < 2 ^ r ∧
      X r p.1 p.2 / 2 ^ (2 * r - a) = bx ∧ Y r p.1 p.2 / 2 ^ a = by_ := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  have ha' : a ≤ 2 * s + 4 := by omega
  have e : 2 * (s + 2) = 2 * s + 4 := by ring
  rw [e] at hby ⊢
  obtain ⟨⟨⟨k, hk⟩, ⟨j, hj⟩⟩, hp, huniq⟩ :=
    exists_unique_in_box s a ha' (⟨bx, hbx⟩, ⟨by_, hby⟩)
  simp only [boxMap, Prod.mk.injEq, Fin.mk.injEq] at hp
  refine ⟨(k, j), ⟨hk, hj, ?_, ?_⟩, ?_⟩
  · rw [X_eq]; exact hp.1
  · rw [Y_eq]; exact hp.2
  · rintro ⟨k', j'⟩ ⟨hk', hj', hx', hy'⟩
    rw [X_eq] at hx'
    rw [Y_eq] at hy'
    have := huniq (⟨k', hk'⟩, ⟨j', hj'⟩)
      (by simp only [boxMap, Prod.mk.injEq, Fin.mk.injEq]; exact ⟨hx', hy'⟩)
    simp only [Prod.mk.injEq, Fin.mk.injEq] at this
    rw [this.1, this.2]

/-- Bijection form of Theorem A (indices in `Fin (2 ^ r) × Fin (2 ^ r)`). -/
theorem net_bijective (s a : ℕ) (ha : a ≤ 2 * s + 4) :
    Function.Bijective (boxMap s a ha) :=
  boxMap_bijective s a ha

/-- **Theorem B, upper bound for every even `m ≥ 8`.**  Writing `m = 2 r = 2 t + 8`, the
points indexed by `(k, j) = (2 ^ (r - 1), 0)` and `(2 ^ (r - 2), 0)` are distinct and their
untranslated squared difference is `241 · 2 ^ (m - 8)`; so the minimum squared tiling
distance is at most `241 · 2 ^ (m - 8)`. -/
theorem distance_upper (t : ℕ) :
    (2 ^ (t + 3) : ℕ) ≠ 2 ^ (t + 2) ∧
    latVal (2 ^ (2 * (t + 4)))
      ((X (t + 4) (2 ^ (t + 3)) 0 : ℤ) - X (t + 4) (2 ^ (t + 2)) 0)
      ((Y (t + 4) (2 ^ (t + 3)) 0 : ℤ) - Y (t + 4) (2 ^ (t + 2)) 0) 0 0
      = 241 * 2 ^ (2 * t) := by
  refine ⟨witness_ne t, ?_⟩
  have e : 2 * (t + 4) = 2 * (t + 2) + 4 := by ring
  rw [e]
  have h := witness_latVal t
  rw [show t + 2 = (t + 2) by rfl] at h
  simpa [X_eq, Y_eq] using h

/-- **Theorem B at `m = 8`, exact.**  The minimum squared tiling distance is `241`:
every pair of distinct points and every lattice translate has squared distance at least
`241`, and the pair `(k, j) = (8, 0), (4, 0)` attains `241`. -/
theorem distance_m8_exact :
    (∀ k j k' j' : ℕ, k < 16 → j < 16 → k' < 16 → j' < 16 → (k, j) ≠ (k', j') →
      ∀ A B : ℤ, 241 ≤ latVal 256 ((X 4 k' j' : ℤ) - X 4 k j) ((Y 4 k' j' : ℤ) - Y 4 k j) A B)
    ∧ (∃ A B : ℤ, latVal 256 ((X 4 8 0 : ℤ) - X 4 4 0) ((Y 4 8 0 : ℤ) - Y 4 4 0) A B = 241) := by
  have h := m8_exact
  refine ⟨fun k j k' j' hk hj hk' hj' hne A B => ?_, ⟨0, 0, ?_⟩⟩
  · have := h.1 k j k' j' hk hj hk' hj' hne A B
    simpa [X_eq, Y_eq] using this
  · have := witness_latVal 0
    norm_num at this
    simpa [X_eq, Y_eq] using this

end GKEvenNet
