/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Author: Lennart Rudolph
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import GKEvenNet.Distance

/-!
# Distance certificates

* `witness_latVal`: for every `t` (so every even `m = 2 t + 8 ≥ 8`) the pair of points
  indexed by `(k, j) = (2 ^ (t + 3), 0)` and `(2 ^ (t + 2), 0)` has squared difference
  `241 · 2 ^ (2 t) = 241 · 2 ^ (m - 8)` with no lattice translation.  This is the
  all-parameter upper bound.
* `lowerCheck_m8`: kernel-checked exhaustive lower bound `241` over all pairs at `m = 8`.
* `attain_m8`: kernel count of the pairs attaining `241` at `m = 8`: exactly `64 = 2^(m-2)`.
* `m8_exact`: the two combine with the exactness lemmas into the statement that `241` is
  the minimum squared tiling distance at `m = 8`.
* `netCheck_m4`, `netCheck_m6`, `netCheck_m8`: kernel-checked bitmask evaluations of the
  net property, kept as statement-fidelity tests of the definitions (Theorem A already
  covers them symbolically); `netCheck_mutated_m4` shows the test can fail.
-/

namespace GKEvenNet

/-! ### The explicit witness pair, all even `m ≥ 8` -/

theorem xc_witness₁ (t : ℕ) : xc (t + 2) (2 ^ (t + 3)) 0 = 22 * 2 ^ t := by
  unfold xc
  have hrev : rev (t + 2 + 2) (2 ^ (t + 3)) = 1 := by
    have := rev_pow (t + 3) 0
    rw [show t + 3 + (0 + 1) = t + 2 + 2 by ring] at this
    simpa using this
  rw [hrev]
  have e1 : 2 ^ (t + 3) / 4 = 2 * 2 ^ t := by
    rw [show (2 : ℕ) ^ (t + 3) = 2 * 2 ^ t * 4 by ring]
    exact Nat.mul_div_cancel _ (by norm_num)
  rw [e1]
  have e2 : (2 : ℕ) ^ (t + 2 + 2) * 1 + 2 * 2 ^ t + 2 ^ (t + 2) * (0 + 1) = 22 * 2 ^ t := by ring
  rw [e2]
  apply Nat.mod_eq_of_lt
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have e3 : (2 : ℕ) ^ (2 * (t + 2) + 4) = 256 * 2 ^ t * 2 ^ t := by ring
  rw [e3]
  nlinarith

theorem xc_witness₂ (t : ℕ) : xc (t + 2) (2 ^ (t + 2)) 0 = 37 * 2 ^ t := by
  unfold xc
  have hrev : rev (t + 2 + 2) (2 ^ (t + 2)) = 2 := by
    have := rev_pow (t + 2) 1
    rw [show t + 2 + (1 + 1) = t + 2 + 2 by ring] at this
    simpa using this
  rw [hrev]
  have e1 : 2 ^ (t + 2) / 4 = 2 ^ t := by
    rw [show (2 : ℕ) ^ (t + 2) = 2 ^ t * 4 by ring]
    exact Nat.mul_div_cancel _ (by norm_num)
  rw [e1]
  have e2 : (2 : ℕ) ^ (t + 2 + 2) * 2 + 2 ^ t + 2 ^ (t + 2) * (0 + 1) = 37 * 2 ^ t := by ring
  rw [e2]
  apply Nat.mod_eq_of_lt
  have h1 : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have e3 : (2 : ℕ) ^ (2 * (t + 2) + 4) = 256 * 2 ^ t * 2 ^ t := by ring
  rw [e3]
  nlinarith

theorem yc_witness₁ (t : ℕ) : yc (t + 2) (2 ^ (t + 3)) 0 = 8 * 2 ^ t := by
  unfold yc; ring

theorem yc_witness₂ (t : ℕ) : yc (t + 2) (2 ^ (t + 2)) 0 = 4 * 2 ^ t := by
  unfold yc; ring

/-- **Upper bound, all even `m ≥ 8`.**  With `m = 2 t + 8`, the points indexed by
`(2 ^ (t + 3), 0)` and `(2 ^ (t + 2), 0)` are distinct and their untranslated squared
difference is `241 · 2 ^ (2 t) = 241 · 2 ^ (m - 8)`. -/
theorem witness_latVal (t : ℕ) :
    latVal (2 ^ (2 * (t + 2) + 4))
      ((xc (t + 2) (2 ^ (t + 3)) 0 : ℤ) - xc (t + 2) (2 ^ (t + 2)) 0)
      ((yc (t + 2) (2 ^ (t + 3)) 0 : ℤ) - yc (t + 2) (2 ^ (t + 2)) 0) 0 0
      = 241 * 2 ^ (2 * t) := by
  rw [xc_witness₁, xc_witness₂, yc_witness₁, yc_witness₂]
  unfold latVal
  push_cast
  ring

theorem witness_ne (t : ℕ) : (2 ^ (t + 3) : ℕ) ≠ 2 ^ (t + 2) := by
  have : (2 : ℕ) ^ (t + 3) = 2 * 2 ^ (t + 2) := by ring
  have h := Nat.one_le_two_pow (n := t + 2)
  omega

/-- The same pair evaluated through `shiftedSq` (the exact tiling minimum). -/
theorem witness_shiftedSq (t : ℕ) :
    shiftedSq (2 ^ (2 * (t + 2) + 4))
      (xc (t + 2) (2 ^ (t + 2)) 0) (yc (t + 2) (2 ^ (t + 2)) 0)
      (xc (t + 2) (2 ^ (t + 3)) 0) (yc (t + 2) (2 ^ (t + 3)) 0)
      ≤ 241 * 2 ^ (2 * t) := by
  rw [xc_witness₁, xc_witness₂, yc_witness₁, yc_witness₂]
  have hT : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  have hP : 2 ^ t ≤ 2 ^ t * 2 ^ t := Nat.le_mul_self _
  have hN : (2 : ℕ) ^ (2 * (t + 2) + 4) = 4 * (64 * (2 ^ t * 2 ^ t)) := by ring
  rw [hN]
  refine (shiftedSq_le_c0 _ _ _ _ _).trans ?_
  have hc : cres (4 * (64 * (2 ^ t * 2 ^ t))) (22 * 2 ^ t + 4 * (64 * (2 ^ t * 2 ^ t)) - 37 * 2 ^ t)
      = 15 * 2 ^ t := by
    unfold cres
    have hu : 22 * 2 ^ t + 4 * (64 * (2 ^ t * 2 ^ t)) - 37 * 2 ^ t
        = 4 * (64 * (2 ^ t * 2 ^ t)) - 15 * 2 ^ t := by omega
    rw [hu]
    have hlt : 4 * (64 * (2 ^ t * 2 ^ t)) - 15 * 2 ^ t < 4 * (64 * (2 ^ t * 2 ^ t)) := by omega
    rw [Nat.mod_eq_of_lt hlt]
    omega
  rw [hc, show 8 * 2 ^ t - 4 * 2 ^ t = 4 * 2 ^ t by omega]
  ring_nf
  omega

/-! ### Exhaustive kernel-checked lower bound at `m = 8` -/

/-- The first coordinate of the point whose second coordinate is `y`
(`y ↦ (k, j) = (y mod Q, y div Q)` is the inverse of `yc`). -/
def xOf (s y : ℕ) : ℕ := xc s (y % 2 ^ (s + 2)) (y / 2 ^ (s + 2))

/-- Exhaustive check that every pair `y < y' < N` has squared tiling distance at least
`bound`. -/
def lowerCheck (s bound : ℕ) : Bool :=
  (List.range (2 ^ (2 * s + 4))).all fun y' =>
    (List.range y').all fun y =>
      decide (bound ≤ shiftedSq (2 ^ (2 * s + 4)) (xOf s y) y (xOf s y') y')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem lowerCheck_m8 : lowerCheck 2 241 = true := by decide +kernel

/-- Number of pairs `y < y' < N` whose squared tiling distance equals `bound`. -/
def attainCount (s bound : ℕ) : ℕ :=
  ((List.range (2 ^ (2 * s + 4))).map fun y' =>
    ((List.range y').filter fun y =>
      decide (shiftedSq (2 ^ (2 * s + 4)) (xOf s y) y (xOf s y') y' = bound)).length).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exactly `64 = 2 ^ (m - 2)` unordered pairs attain the minimum `241` at `m = 8`
(`shiftedSq` is the exact lattice minimum by `shiftedSq_le_latVal` and
`shiftedSq_attained`). -/
theorem attain_m8 : attainCount 2 241 = 64 := by decide +kernel

/-- Bridge for the count: for `y < y' < 256` the candidate minimum equals `241` exactly when
every lattice translate of the difference has squared length at least `241` and some
translate has squared length `241`.  Together with `attain_m8`, exactly `64` index pairs
attain the tiling minimum at `m = 8`. -/
theorem attain_m8_spec : attainCount 2 241 = 64 ∧
    ∀ y' < 256, ∀ y < y',
      (shiftedSq 256 (xOf 2 y) y (xOf 2 y') y' = 241 ↔
        (∀ A B : ℤ, (241 : ℤ) ≤ latVal 256 ((xOf 2 y' : ℤ) - xOf 2 y) ((y' : ℤ) - y) A B) ∧
        (∃ A B : ℤ, latVal 256 ((xOf 2 y' : ℤ) - xOf 2 y) ((y' : ℤ) - y) A B = 241)) := by
  refine ⟨attain_m8, fun y' hy' y hy => ?_⟩
  have hx : xOf 2 y < 4 * 64 := by
    have h := xc_lt 2 (y % 2 ^ (2 + 2)) (y / 2 ^ (2 + 2))
    unfold xOf
    norm_num at h ⊢
    exact h
  have hy'' : y' < 4 * 64 := by omega
  have h := shiftedSq_eq_iff 64 (xOf 2 y) y (xOf 2 y') y' (by norm_num) hx hy'' hy 241
  norm_num at h ⊢
  exact h

theorem lowerCheck_spec {s bound : ℕ} (h : lowerCheck s bound = true) :
    ∀ y' < 2 ^ (2 * s + 4), ∀ y < y',
      bound ≤ shiftedSq (2 ^ (2 * s + 4)) (xOf s y) y (xOf s y') y' := by
  unfold lowerCheck at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h

theorem xOf_yc (s k j : ℕ) (hk : k < 2 ^ (s + 2)) : xOf s (yc s k j) = xc s k j := by
  unfold xOf yc
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk, add_mul_div_self' _ _ _ hk]

theorem latVal_neg (N : ℕ) (dx dy A B : ℤ) :
    latVal N (-dx) (-dy) (-A) (-B) = latVal N dx dy A B := by
  unfold latVal; ring

theorem yc_injective (s : ℕ) {k j k' j' : ℕ} (hk : k < 2 ^ (s + 2)) (hk' : k' < 2 ^ (s + 2))
    (h : yc s k j = yc s k' j') : k = k' ∧ j = j' := by
  unfold yc at h
  exact concat_unique hk hk' h

/-- **Lower bound at `m = 8`.**  Every pair of distinct points and every lattice translate
has squared distance at least `241`. -/
theorem m8_lower {k j k' j' : ℕ} (hk : k < 16) (hj : j < 16) (hk' : k' < 16) (hj' : j' < 16)
    (hne : (k, j) ≠ (k', j')) (A B : ℤ) :
    241 ≤ latVal 256 ((xc 2 k' j' : ℤ) - xc 2 k j) ((yc 2 k' j' : ℤ) - yc 2 k j) A B := by
  have hk16 : k < 2 ^ (2 + 2) := by norm_num; exact hk
  have hj16 : j < 2 ^ (2 + 2) := by norm_num; exact hj
  have hk16' : k' < 2 ^ (2 + 2) := by norm_num; exact hk'
  have hj16' : j' < 2 ^ (2 + 2) := by norm_num; exact hj'
  have hN : (2 : ℕ) ^ (2 * 2 + 4) = 256 := by norm_num
  have hN' : (256 : ℕ) = 4 * 64 := by norm_num
  have hy : yc 2 k j ≠ yc 2 k' j' := by
    intro h
    obtain ⟨h1, h2⟩ := yc_injective 2 hk16 hk16' h
    exact hne (by rw [h1, h2])
  have hxlt : ∀ k j, xc 2 k j < 4 * 64 := fun k j => by
    have := xc_lt 2 k j; rw [hN] at this; exact this
  have hylt : ∀ k j, k < 2 ^ (2 + 2) → j < 2 ^ (2 + 2) → yc 2 k j < 4 * 64 :=
    fun k j hk hj => by
      have := yc_lt 2 k j hk hj; rw [hN] at this; exact this
  have spec := lowerCheck_spec lowerCheck_m8
  rw [hN] at spec
  rcases Nat.lt_or_gt_of_ne hy with hlt | hgt
  · have h1 := spec (yc 2 k' j') (hylt k' j' hk16' hj16') (yc 2 k j) hlt
    rw [xOf_yc 2 k j hk16, xOf_yc 2 k' j' hk16'] at h1
    have h2 := shiftedSq_le_latVal 64 (xc 2 k j) (yc 2 k j) (xc 2 k' j') (yc 2 k' j')
      (by norm_num) (hxlt k j) (hylt k' j' hk16' hj16') hlt A B
    rw [← hN'] at h2
    have h1' : (241 : ℤ) ≤ ((shiftedSq 256 (xc 2 k j) (yc 2 k j) (xc 2 k' j') (yc 2 k' j') : ℕ) : ℤ) := by
      exact_mod_cast h1
    exact h1'.trans h2
  · have h1 := spec (yc 2 k j) (hylt k j hk16 hj16) (yc 2 k' j') hgt
    rw [xOf_yc 2 k j hk16, xOf_yc 2 k' j' hk16'] at h1
    have h2 := shiftedSq_le_latVal 64 (xc 2 k' j') (yc 2 k' j') (xc 2 k j) (yc 2 k j)
      (by norm_num) (hxlt k' j') (hylt k j hk16 hj16) hgt (-A) (-B)
    rw [← hN'] at h2
    have h1' : (241 : ℤ) ≤ ((shiftedSq 256 (xc 2 k' j') (yc 2 k' j') (xc 2 k j) (yc 2 k j) : ℕ) : ℤ) := by
      exact_mod_cast h1
    have h3 : latVal 256 ((xc 2 k j : ℤ) - xc 2 k' j') ((yc 2 k j : ℤ) - yc 2 k' j') (-A) (-B)
        = latVal 256 ((xc 2 k' j' : ℤ) - xc 2 k j) ((yc 2 k' j' : ℤ) - yc 2 k j) A B := by
      rw [← latVal_neg 256 ((xc 2 k' j' : ℤ) - xc 2 k j) ((yc 2 k' j' : ℤ) - yc 2 k j) A B]
      congr 1 <;> ring
    rw [h3] at h2
    exact h1'.trans h2

/-- **Exact minimum at `m = 8`.**  The squared tiling distance is at least `241` for every
pair of distinct points and every lattice translate, and one explicit pair attains `241`. -/
theorem m8_exact :
    (∀ k j k' j' : ℕ, k < 16 → j < 16 → k' < 16 → j' < 16 → (k, j) ≠ (k', j') →
      ∀ A B : ℤ, 241 ≤ latVal 256 ((xc 2 k' j' : ℤ) - xc 2 k j) ((yc 2 k' j' : ℤ) - yc 2 k j) A B)
    ∧ (∃ k j k' j' : ℕ, k < 16 ∧ j < 16 ∧ k' < 16 ∧ j' < 16 ∧ (k, j) ≠ (k', j') ∧
      ∃ A B : ℤ, latVal 256 ((xc 2 k' j' : ℤ) - xc 2 k j) ((yc 2 k' j' : ℤ) - yc 2 k j) A B = 241) := by
  refine ⟨fun k j k' j' hk hj hk' hj' hne A B => m8_lower hk hj hk' hj' hne A B, ?_⟩
  refine ⟨4, 0, 8, 0, by norm_num, by norm_num, by norm_num, by norm_num, by decide, 0, 0, ?_⟩
  have := witness_latVal 0
  norm_num at this
  exact this

/-! ### Kernel-checked evaluations of the net property (definition sanity) -/

/-- Bitmask over the `2 ^ m` boxes of resolution `a`; equal to `2 ^ (2 ^ m) - 1` exactly
when every box is hit by some point. -/
def netCheckWith (xf : ℕ → ℕ) (s a : ℕ) : Bool :=
  (List.range (2 ^ (2 * s + 4))).foldl
    (fun acc y => acc ||| (1 <<< ((xf y / 2 ^ (2 * s + 4 - a)) <<< (2 * s + 4 - a) ||| (y / 2 ^ a))))
    0 == 2 ^ (2 ^ (2 * s + 4)) - 1

/-- The net property at every resolution `a ≤ m`. -/
def netCheck (s : ℕ) : Bool :=
  (List.range (2 * s + 5)).all fun a => netCheckWith (xOf s) s a

set_option maxRecDepth 100000 in
theorem netCheck_m4 : netCheck 0 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem netCheck_m6 : netCheck 1 = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem netCheck_m8 : netCheck 2 = true := by decide +kernel

/-- A mutated point set (the first two points swap first coordinates with a shift) fails. -/
def xOfMutated (s y : ℕ) : ℕ := if y = 0 then xOf s 1 else xOf s y

set_option maxRecDepth 100000 in
theorem netCheck_mutated_m4 :
    ((List.range 5).all fun a => netCheckWith (xOfMutated 0) 0 a) = false := by decide +kernel

end GKEvenNet
