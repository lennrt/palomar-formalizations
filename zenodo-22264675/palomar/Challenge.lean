/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.22264675
Preprint version 1.0.0 dated 2026-09-03; Palomar formalization packaged 2026-09-03.
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import Mathlib.Tactic

/-!
# Challenge: even-order Grünschloß–Keller permutation nets

For even `m = 2 r` with `r ≥ 2`, the source header `gendiag0m2.h` (Grünschloß and Keller,
"(t,m,s)-Nets and Maximized Minimum Distance, Part II", MCQMC 2008) generates the `2 ^ m`
integer points

  `X r k j = (2 ^ r · rev r k + ⌊k / 4⌋ + 2 ^ (r - 2) · (j + 1)) mod 2 ^ (2 r)`,
  `Y r k j = k + 2 ^ r · j`,      for `0 ≤ k, j < 2 ^ r`,

where `rev r` reverses `r` binary digits (the 32-bit van der Corput term shifted right by
`32 - m`).  The source states that the `t = 0` property was verified by computer for even
`m ≤ 22` and that the minimum distance in its row-shifted tiling metric is `√241` at `m = 8`
and `√(241 · 2 ^ (m - 8)) / 2 ^ m` for even `10 ≤ m ≤ 22`.

Three statements are advertised.

* `net`: for every even `m = 2 r ≥ 4`, every resolution `a ≤ m`, and every dyadic box, exactly
  one point lies in the box; that is, the normalized point set is a `(0, m, 2)`-net in base 2.
* `distance_upper`: for every even `m ≥ 8` an explicit pair of distinct points has
  untranslated squared difference `241 · 2 ^ (m - 8)`, so the minimum squared tiling
  distance is at most `241 · 2 ^ (m - 8)`.
* `distance_m8_exact`: at `m = 8`, every pair of distinct points and every translate by the
  tiling lattice `⟨(256, 0), (64, 256)⟩` has squared distance at least `241`, and the bound
  is attained.
-/

namespace GKEvenNet

/-- Reverse the low `n` binary digits of `k`: bit `i` of `k` becomes bit `n-1-i`. -/
def rev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => 2 ^ n * (k % 2) + rev n (k / 2)

/-- First integer coordinate for even order `m = 2 r`, `r ≥ 2`. -/
def X (r k j : ℕ) : ℕ := (2 ^ r * rev r k + k / 4 + 2 ^ (r - 2) * (j + 1)) % 2 ^ (2 * r)

/-- Second integer coordinate for even order `m = 2 r`. -/
def Y (r k j : ℕ) : ℕ := k + 2 ^ r * j

/-- Squared length of the difference vector `(dx, dy)` after translation by the lattice
vector `A (N, 0) + B (N / 4, N)` of the row-shifted tiling. -/
def latVal (N : ℕ) (dx dy A B : ℤ) : ℤ :=
  (dx + A * N + B * ((N / 4 : ℕ) : ℤ)) ^ 2 + (dy + B * N) ^ 2

/-- **Theorem A.**  For every even `m = 2 r ≥ 4`, every `a ≤ m`, and every dyadic box
`(bx, by)` with `bx < 2 ^ a` and `by < 2 ^ (m - a)`, exactly one index pair `(k, j)` with
`k, j < 2 ^ r` satisfies `⌊X / 2 ^ (m - a)⌋ = bx` and `⌊Y / 2 ^ a⌋ = by`; equivalently the
normalized point `(X / 2 ^ m, Y / 2 ^ m)` lies in the elementary interval
`[bx / 2 ^ a, (bx + 1) / 2 ^ a) × [by / 2 ^ (m - a), (by + 1) / 2 ^ (m - a))`. -/
theorem net (r : ℕ) (hr : 2 ≤ r) (a : ℕ) (ha : a ≤ 2 * r)
    (bx by_ : ℕ) (hbx : bx < 2 ^ a) (hby : by_ < 2 ^ (2 * r - a)) :
    ∃! p : ℕ × ℕ, p.1 < 2 ^ r ∧ p.2 < 2 ^ r ∧
      X r p.1 p.2 / 2 ^ (2 * r - a) = bx ∧ Y r p.1 p.2 / 2 ^ a = by_ := by
  sorry

/-- **Theorem B, upper bound.**  With `m = 2 t + 8` (so `r = t + 4`), the points indexed by
`(k, j) = (2 ^ (t + 3), 0)` and `(2 ^ (t + 2), 0)` are distinct and their squared distance
is `241 · 2 ^ (2 t) = 241 · 2 ^ (m - 8)`. -/
theorem distance_upper (t : ℕ) :
    (2 ^ (t + 3) : ℕ) ≠ 2 ^ (t + 2) ∧
    latVal (2 ^ (2 * (t + 4)))
      ((X (t + 4) (2 ^ (t + 3)) 0 : ℤ) - X (t + 4) (2 ^ (t + 2)) 0)
      ((Y (t + 4) (2 ^ (t + 3)) 0 : ℤ) - Y (t + 4) (2 ^ (t + 2)) 0) 0 0
      = 241 * 2 ^ (2 * t) := by
  sorry

/-- **Theorem B at `m = 8`, exact.**  Every pair of distinct points and every lattice
translate has squared distance at least `241`, and the pair `(k, j) = (8, 0), (4, 0)`
attains `241`. -/
theorem distance_m8_exact :
    (∀ k j k' j' : ℕ, k < 16 → j < 16 → k' < 16 → j' < 16 → (k, j) ≠ (k', j') →
      ∀ A B : ℤ, 241 ≤ latVal 256 ((X 4 k' j' : ℤ) - X 4 k j) ((Y 4 k' j' : ℤ) - Y 4 k j) A B)
    ∧ (∃ A B : ℤ, latVal 256 ((X 4 8 0 : ℤ) - X 4 4 0) ((Y 4 8 0 : ℤ) - Y 4 4 0) A B = 241) := by
  sorry

end GKEvenNet
