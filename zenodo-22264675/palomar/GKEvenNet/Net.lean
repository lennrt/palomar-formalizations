/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Author: Lennart Rudolph
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import GKEvenNet.Rev

/-!
# The even-order construction is a `(0, m, 2)`-net for every even `m ≥ 4`

Parameters.  We write `m = 2 * s + 4`, so `r = m / 2 = s + 2`, `Q = 2 ^ (s + 2)`
points per diagonal, `S = 2 ^ s`, and `N = 2 ^ (2 * s + 4)` points in total.
For `0 ≤ k, j < Q` the point on diagonal `k` in position `j` has integer
coordinates

  `xc s k j = (Q * rev r k + k / 4 + S * (j + 1)) mod N`,
  `yc s k j = k + Q * j`.

This is the even branch of `gendiag0m2.h`: the 32-bit van der Corput term
shifted right by `32 - m` equals `Q * rev r k` for `k < Q`.

The net property for resolution `a` (with `0 ≤ a ≤ m`) says that the map
`(k, j) ↦ (xc / 2 ^ (m - a), yc / 2 ^ a)` onto the `2 ^ a × 2 ^ (m - a)` grid of
dyadic boxes is a bijection.  The proof shows injectivity through the
concatenation `xc = k / 4 + S * zc`, where `zc = (j + 1 + 4 * rev r k) mod 4Q`,
and splits into the cases `a ≤ r` and `a = r + c` (`c = 1` and `c ≥ 2`).
-/

namespace GKEvenNet

/-! ### Elementary arithmetic lemmas -/

/-- `(q + B * w) / B = w` when `q < B`. -/
theorem add_mul_div_self' (q B w : ℕ) (hq : q < B) : (q + B * w) / B = w := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hq, zero_add]

/-- `(q + B * w) % (B * M) = q + B * (w % M)` when `q < B`. -/
theorem add_mul_mod_mul (q B w M : ℕ) (hq : q < B) (hM : 0 < M) :
    (q + B * w) % (B * M) = q + B * (w % M) := by
  have h1 : q + B * w = q + B * (w % M) + (B * M) * (w / M) := by
    calc q + B * w = q + B * (M * (w / M) + w % M) := by rw [Nat.div_add_mod]
      _ = q + B * (w % M) + (B * M) * (w / M) := by ring
  rw [h1, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have : w % M < M := Nat.mod_lt _ hM
  nlinarith

/-- A concatenation `lo + B * hi` with `lo < B` determines both parts. -/
theorem concat_unique {lo lo' hi hi' B : ℕ} (h1 : lo < B) (h2 : lo' < B)
    (h : lo + B * hi = lo' + B * hi') : lo = lo' ∧ hi = hi' := by
  have hB : 0 < B := by omega
  constructor
  · have := congrArg (· % B) h
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this
    exact this
  · have := congrArg (· / B) h
    simp only [add_mul_div_self' _ _ _ h1, add_mul_div_self' _ _ _ h2] at this
    exact this

/-- Cancellation of a common summand modulo `M` for residues below `M`. -/
theorem mod_add_cancel {C R R' M : ℕ} (hR : R < M) (hR' : R' < M)
    (h : (C + R) % M = (C + R') % M) : R = R' := by
  have h' : R ≡ R' [MOD M] := Nat.ModEq.add_left_cancel' C h
  exact Nat.ModEq.eq_of_lt_of_lt h' hR hR'

theorem two_pow_split (a b : ℕ) (h : a ≤ b) : (2 : ℕ) ^ b = 2 ^ a * 2 ^ (b - a) := by
  rw [← pow_add, Nat.add_sub_cancel' h]

/-! ### The point set -/

/-- First integer coordinate (modulo `N = 2 ^ (2 s + 4)`) of the point on diagonal `k`
in position `j`, for `m = 2 s + 4`. -/
def xc (s k j : ℕ) : ℕ :=
  (2 ^ (s + 2) * rev (s + 2) k + k / 4 + 2 ^ s * (j + 1)) % 2 ^ (2 * s + 4)

/-- Second integer coordinate. -/
def yc (s k j : ℕ) : ℕ := k + 2 ^ (s + 2) * j

/-- The high `s + 4` bits of `xc`. -/
def zc (s k j : ℕ) : ℕ := (j + 1 + 4 * rev (s + 2) k) % 2 ^ (s + 4)

theorem xc_lt (s k j : ℕ) : xc s k j < 2 ^ (2 * s + 4) := Nat.mod_lt _ (by positivity)

theorem zc_lt (s k j : ℕ) : zc s k j < 2 ^ (s + 4) := Nat.mod_lt _ (by positivity)

theorem yc_lt (s k j : ℕ) (hk : k < 2 ^ (s + 2)) (hj : j < 2 ^ (s + 2)) :
    yc s k j < 2 ^ (2 * s + 4) := by
  unfold yc
  have e : (2 : ℕ) ^ (2 * s + 4) = 2 ^ (s + 2) * 2 ^ (s + 2) := by
    rw [← pow_add]; congr 1; ring
  rw [e]
  nlinarith

theorem quarter_lt (s k : ℕ) (hk : k < 2 ^ (s + 2)) : k / 4 < 2 ^ s := by
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  calc k < 2 ^ (s + 2) := hk
    _ = 2 ^ s * 4 := by rw [pow_add]; norm_num

/-- The concatenation identity `xc = k / 4 + S * zc`; no carry and no wrap occurs. -/
theorem xc_eq (s k j : ℕ) (hk : k < 2 ^ (s + 2)) :
    xc s k j = k / 4 + 2 ^ s * zc s k j := by
  unfold xc zc
  have hq := quarter_lt s k hk
  have e1 : 2 ^ (s + 2) * rev (s + 2) k + k / 4 + 2 ^ s * (j + 1)
      = k / 4 + 2 ^ s * (j + 1 + 4 * rev (s + 2) k) := by ring
  have e2 : (2 : ℕ) ^ (2 * s + 4) = 2 ^ s * 2 ^ (s + 4) := by
    rw [← pow_add]; congr 1; ring
  rw [e1, e2, add_mul_mod_mul _ _ _ _ hq (by positivity)]

/-! ### Case `a ≤ r` -/

theorem net_inj_low (s a : ℕ) (ha : a ≤ s + 2) {k j k' j' : ℕ}
    (hk : k < 2 ^ (s + 2)) (hk' : k' < 2 ^ (s + 2))
    (hx : xc s k j / 2 ^ (2 * s + 4 - a) = xc s k' j' / 2 ^ (2 * s + 4 - a))
    (hy : yc s k j / 2 ^ a = yc s k' j' / 2 ^ a) :
    k = k' ∧ j = j' := by
  have hQ : (2 : ℕ) ^ (s + 2) = 2 ^ a * 2 ^ (s + 2 - a) := two_pow_split a (s + 2) ha
  -- the second box coordinate is the concatenation `k / 2^a + 2^(r-a) * j`
  have ydiv : ∀ k j : ℕ, yc s k j / 2 ^ a = k / 2 ^ a + 2 ^ (s + 2 - a) * j := by
    intro k j
    unfold yc
    rw [hQ, mul_assoc, Nat.add_mul_div_left _ _ (by positivity)]
  have kdiv_lt : ∀ k : ℕ, k < 2 ^ (s + 2) → k / 2 ^ a < 2 ^ (s + 2 - a) := by
    intro k hk
    rw [Nat.div_lt_iff_lt_mul (by positivity), mul_comm, ← hQ]
    exact hk
  rw [ydiv k j, ydiv k' j'] at hy
  obtain ⟨hK, hj⟩ := concat_unique (kdiv_lt k hk) (kdiv_lt k' hk') hy
  subst hj
  -- the first box coordinate is the top `a` bits of `zc`
  have xdiv : ∀ k j : ℕ, k < 2 ^ (s + 2) →
      xc s k j / 2 ^ (2 * s + 4 - a) = zc s k j / 2 ^ (s + 4 - a) := by
    intro k j hk
    rw [xc_eq s k j hk]
    have e : (2 : ℕ) ^ (2 * s + 4 - a) = 2 ^ s * 2 ^ (s + 4 - a) := by
      rw [← pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, add_mul_div_self' _ _ _ (quarter_lt s k hk)]
  rw [xdiv k j hk, xdiv k' j hk'] at hx
  set L : ℕ := 2 ^ (s + 4 - a) with hL
  have hL4 : L = 4 * 2 ^ (s + 2 - a) := by
    rw [hL, show s + 4 - a = (s + 2 - a) + 2 by omega, pow_add]; ring
  have hLM : (2 : ℕ) ^ (s + 4) = L * 2 ^ a := by
    rw [hL, ← pow_add]; congr 1; omega
  have zdiv : ∀ k j : ℕ, zc s k j / L
      = ((j + 1 + 4 * rev (s + 2 - a) (k / 2 ^ a)) / L + rev a (k % 2 ^ a)) % 2 ^ a := by
    intro k j
    unfold zc
    have hsplit : rev (s + 2) k
        = 2 ^ (s + 2 - a) * rev a (k % 2 ^ a) + rev (s + 2 - a) (k / 2 ^ a) := by
      have := rev_split a (s + 2 - a) (k / 2 ^ a) (k % 2 ^ a) (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod, show a + (s + 2 - a) = s + 2 by omega] at this
      exact this
    rw [hsplit, hLM]
    have e : j + 1 + 4 * (2 ^ (s + 2 - a) * rev a (k % 2 ^ a) + rev (s + 2 - a) (k / 2 ^ a))
        = (j + 1 + 4 * rev (s + 2 - a) (k / 2 ^ a)) + L * rev a (k % 2 ^ a) := by
      rw [hL4]; ring
    rw [e, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ (by positivity)]
  rw [zdiv k j, zdiv k' j, hK] at hx
  have hR := mod_add_cancel (rev_lt a _) (rev_lt a _) hx
  have ht := rev_inj (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity)) hR
  refine ⟨?_, rfl⟩
  calc k = 2 ^ a * (k / 2 ^ a) + k % 2 ^ a := (Nat.div_add_mod k _).symm
    _ = 2 ^ a * (k' / 2 ^ a) + k' % 2 ^ a := by rw [hK, ht]
    _ = k' := Nat.div_add_mod k' _

/-! ### Case `a = r + 1` -/

theorem net_inj_c1 (s : ℕ) {k j k' j' : ℕ}
    (hk : k < 2 ^ (s + 2)) (hk' : k' < 2 ^ (s + 2))
    (hx : xc s k j / 2 ^ (s + 1) = xc s k' j' / 2 ^ (s + 1))
    (hy : yc s k j / 2 ^ (s + 3) = yc s k' j' / 2 ^ (s + 3)) :
    k = k' ∧ j = j' := by
  have ydiv : ∀ k j : ℕ, k < 2 ^ (s + 2) → yc s k j / 2 ^ (s + 3) = j / 2 := by
    intro k j hk
    unfold yc
    rw [show (2 : ℕ) ^ (s + 3) = 2 ^ (s + 2) * 2 by ring, ← Nat.div_div_eq_div_mul,
      add_mul_div_self' _ _ _ hk]
  rw [ydiv k j hk, ydiv k' j' hk'] at hy
  have xdiv : ∀ k j : ℕ, k < 2 ^ (s + 2) → xc s k j / 2 ^ (s + 1) = zc s k j / 2 := by
    intro k j hk
    rw [xc_eq s k j hk, show (2 : ℕ) ^ (s + 1) = 2 ^ s * 2 by ring,
      ← Nat.div_div_eq_div_mul, add_mul_div_self' _ _ _ (quarter_lt s k hk)]
  rw [xdiv k j hk, xdiv k' j' hk'] at hx
  have zdiv : ∀ k j : ℕ, zc s k j / 2 = (j / 2 + (2 * rev (s + 2) k + j % 2)) % 2 ^ (s + 3) := by
    intro k j
    unfold zc
    rw [show (2 : ℕ) ^ (s + 4) = 2 * 2 ^ (s + 3) by ring, Nat.mod_mul_right_div_self]
    congr 1
    have e : j + 1 + 4 * rev (s + 2) k = 2 * (j / 2 + 2 * rev (s + 2) k) + (j % 2 + 1) := by
      have := Nat.div_add_mod j 2
      omega
    rw [e, Nat.mul_add_div (by norm_num)]
    have : (j % 2 + 1) / 2 = j % 2 := by omega
    omega
  rw [zdiv, zdiv, hy] at hx
  have hlt : ∀ k j : ℕ, k < 2 ^ (s + 2) → 2 * rev (s + 2) k + j % 2 < 2 ^ (s + 3) := by
    intro k j hk
    have h1 := rev_lt (s + 2) k
    have h2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have e : (2 : ℕ) ^ (s + 3) = 2 * 2 ^ (s + 2) := by ring
    omega
  have h2 := mod_add_cancel (hlt k j hk) (hlt k' j' hk') hx
  have hu : j % 2 = j' % 2 := by omega
  have hrev : rev (s + 2) k = rev (s + 2) k' := by omega
  refine ⟨rev_inj hk hk' hrev, ?_⟩
  have := Nat.div_add_mod j 2
  have := Nat.div_add_mod j' 2
  omega

/-! ### Case `a = r + c`, `c ≥ 2` (written `s = c + d`, `a = 2 c + d + 4`) -/

theorem net_inj_c2 (c d : ℕ) {k j k' j' : ℕ}
    (hk : k < 2 ^ (c + d + 2)) (hk' : k' < 2 ^ (c + d + 2))
    (hx : xc (c + d) k j / 2 ^ d = xc (c + d) k' j' / 2 ^ d)
    (hy : yc (c + d) k j / 2 ^ (c + d + 2 + (c + 2))
        = yc (c + d) k' j' / 2 ^ (c + d + 2 + (c + 2))) :
    k = k' ∧ j = j' := by
  have ydiv : ∀ k j : ℕ, k < 2 ^ (c + d + 2) →
      yc (c + d) k j / 2 ^ (c + d + 2 + (c + 2)) = j / 2 ^ (c + 2) := by
    intro k j hk
    unfold yc
    rw [pow_add (2 : ℕ) (c + d + 2) (c + 2), ← Nat.div_div_eq_div_mul, add_mul_div_self' _ _ _ hk]
  rw [ydiv k j hk, ydiv k' j' hk'] at hy
  have xdiv : ∀ k j : ℕ, k < 2 ^ (c + d + 2) →
      xc (c + d) k j / 2 ^ d = k / 2 ^ (d + 2) + 2 ^ c * zc (c + d) k j := by
    intro k j hk
    rw [xc_eq (c + d) k j hk]
    have e : (2 : ℕ) ^ (c + d) = 2 ^ d * 2 ^ c := by rw [← pow_add]; congr 1; ring
    rw [e, mul_assoc, Nat.add_mul_div_left _ _ (by positivity), Nat.div_div_eq_div_mul]
    congr 2
    rw [pow_add]; ring
  rw [xdiv k j hk, xdiv k' j' hk'] at hx
  have hh : ∀ k : ℕ, k < 2 ^ (c + d + 2) → k / 2 ^ (d + 2) < 2 ^ c := by
    intro k hk
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show c + (d + 2) = c + d + 2 by ring]
    exact hk
  obtain ⟨hH, hz⟩ := concat_unique (hh k hk) (hh k' hk') hx
  -- expand `zc` as `2^(c+2) * (J + R) + w` modulo `2^(c+2) * 2^(d+2)`
  have zexp : ∀ k j : ℕ, zc (c + d) k j
      = (2 ^ (c + 2) * (j / 2 ^ (c + 2) + rev (d + 2) (k % 2 ^ (d + 2)))
          + (j % 2 ^ (c + 2) + 1 + 4 * rev c (k / 2 ^ (d + 2)))) % (2 ^ (c + 2) * 2 ^ (d + 2)) := by
    intro k j
    unfold zc
    have hMP : (2 : ℕ) ^ (c + d + 4) = 2 ^ (c + 2) * 2 ^ (d + 2) := by
      rw [← pow_add]; congr 1; ring
    rw [hMP]
    congr 1
    have hsplit : rev (c + d + 2) k
        = 2 ^ c * rev (d + 2) (k % 2 ^ (d + 2)) + rev c (k / 2 ^ (d + 2)) := by
      have := rev_split (d + 2) c (k / 2 ^ (d + 2)) (k % 2 ^ (d + 2))
        (Nat.mod_lt _ (by positivity))
      rw [Nat.div_add_mod, show d + 2 + c = c + d + 2 by ring] at this
      exact this
    rw [hsplit]
    have hj := Nat.div_add_mod j (2 ^ (c + 2))
    have e4 : (2 : ℕ) ^ (c + 2) = 4 * 2 ^ c := by rw [pow_add]; ring
    rw [e4] at hj ⊢
    nth_rewrite 1 [← hj]
    ring
  rw [zexp k j, zexp k' j'] at hz
  set M : ℕ := 2 ^ (c + 2) with hM
  set P : ℕ := 2 ^ (d + 2) with hP
  have hMpos : 0 < M := by positivity
  have hPpos : 0 < P := by positivity
  -- recover the low part `u = j % M`
  have hu : j % M = j' % M := by
    have h1 := congrArg (· % M) hz
    simp only at h1
    rw [Nat.mod_mod_of_dvd _ (dvd_mul_right M P), Nat.mod_mod_of_dvd _ (dvd_mul_right M P),
      Nat.mul_add_mod, Nat.mul_add_mod, hH] at h1
    have h2 : ((1 + 4 * rev c (k' / P)) + j % M) % M = ((1 + 4 * rev c (k' / P)) + j' % M) % M := by
      have e1 : j % M + 1 + 4 * rev c (k' / P) = (1 + 4 * rev c (k' / P)) + j % M := by ring
      have e2 : j' % M + 1 + 4 * rev c (k' / P) = (1 + 4 * rev c (k' / P)) + j' % M := by ring
      rw [← e1, ← e2]; exact h1
    exact mod_add_cancel (Nat.mod_lt _ hMpos) (Nat.mod_lt _ hMpos) h2
  have hw : j % M + 1 + 4 * rev c (k / P) = j' % M + 1 + 4 * rev c (k' / P) := by
    rw [hu, hH]
  -- recover the reversed low part of `k`
  have hR : rev (d + 2) (k % P) = rev (d + 2) (k' % P) := by
    have h1 := congrArg (· / M) hz
    simp only at h1
    rw [Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self, Nat.mul_add_div hMpos,
      Nat.mul_add_div hMpos, hy, hw] at h1
    have h2 : ((j' / M + (j' % M + 1 + 4 * rev c (k' / P)) / M) + rev (d + 2) (k % P)) % P
        = ((j' / M + (j' % M + 1 + 4 * rev c (k' / P)) / M) + rev (d + 2) (k' % P)) % P := by
      have e1 : ∀ R : ℕ, j' / M + R + (j' % M + 1 + 4 * rev c (k' / P)) / M
          = (j' / M + (j' % M + 1 + 4 * rev c (k' / P)) / M) + R := fun R => by ring
      rw [← e1, ← e1]; exact h1
    exact mod_add_cancel (rev_lt _ _) (rev_lt _ _) h2
  have hl := rev_inj (Nat.mod_lt _ hPpos) (Nat.mod_lt _ hPpos) hR
  constructor
  · calc k = P * (k / P) + k % P := (Nat.div_add_mod k P).symm
      _ = P * (k' / P) + k' % P := by rw [hH, hl]
      _ = k' := Nat.div_add_mod k' P
  · calc j = M * (j / M) + j % M := (Nat.div_add_mod j M).symm
      _ = M * (j' / M) + j' % M := by rw [hy, hu]
      _ = j' := Nat.div_add_mod j' M

/-! ### All resolutions -/

/-- Injectivity of the dyadic-box map at every resolution `a ≤ m = 2 s + 4`. -/
theorem net_inj (s a : ℕ) (ha : a ≤ 2 * s + 4) {k j k' j' : ℕ}
    (hk : k < 2 ^ (s + 2)) (hk' : k' < 2 ^ (s + 2))
    (hx : xc s k j / 2 ^ (2 * s + 4 - a) = xc s k' j' / 2 ^ (2 * s + 4 - a))
    (hy : yc s k j / 2 ^ a = yc s k' j' / 2 ^ a) :
    k = k' ∧ j = j' := by
  rcases Nat.lt_or_ge a (s + 3) with hlo | hhi
  · exact net_inj_low s a (by omega) hk hk' hx hy
  · obtain ⟨c, rfl⟩ : ∃ c, a = s + 3 + c := ⟨a - (s + 3), by omega⟩
    rcases c with _ | c
    · -- `a = r + 1`
      have e1 : 2 * s + 4 - (s + 3 + 0) = s + 1 := by omega
      have e2 : s + 3 + 0 = s + 3 := by omega
      rw [e1] at hx
      rw [e2] at hy
      exact net_inj_c1 s hk hk' hx hy
    · -- `a = r + c + 2`, with `s = c + d`
      obtain ⟨d, rfl⟩ : ∃ d, s = c + d := ⟨s - c, by omega⟩
      have e1 : 2 * (c + d) + 4 - (c + d + 3 + (c + 1)) = d := by omega
      have e2 : c + d + 3 + (c + 1) = c + d + 2 + (c + 2) := by omega
      rw [e1] at hx
      rw [e2] at hy
      exact net_inj_c2 c d hk hk' hx hy

/-- The dyadic box of resolution `a` (with `a` leading bits of `x` and `m - a` leading bits
of `y` prescribed) containing the point indexed by `p = (k, j)`. -/
def boxMap (s a : ℕ) (ha : a ≤ 2 * s + 4)
    (p : Fin (2 ^ (s + 2)) × Fin (2 ^ (s + 2))) :
    Fin (2 ^ a) × Fin (2 ^ (2 * s + 4 - a)) :=
  (⟨xc s p.1 p.2 / 2 ^ (2 * s + 4 - a), by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_sub_cancel' ha]
      exact xc_lt _ _ _⟩,
   ⟨yc s p.1 p.2 / 2 ^ a, by
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
        show 2 * s + 4 - a + a = 2 * s + 4 by omega]
      exact yc_lt _ _ _ p.1.2 p.2.2⟩)

theorem boxMap_injective (s a : ℕ) (ha : a ≤ 2 * s + 4) :
    Function.Injective (boxMap s a ha) := by
  rintro ⟨⟨k, hk⟩, ⟨j, hj⟩⟩ ⟨⟨k', hk'⟩, ⟨j', hj'⟩⟩ h
  simp only [boxMap, Prod.mk.injEq, Fin.mk.injEq] at h
  obtain ⟨h1, h2⟩ := net_inj s a ha hk hk' h.1 h.2
  subst h1; subst h2
  rfl

/-- **Theorem A** (index form).  For `m = 2 s + 4` and every resolution `a ≤ m`, the map
sending a point to its dyadic box is a bijection: every elementary interval of area
`2 ^ (-m)` contains exactly one point. -/
theorem boxMap_bijective (s a : ℕ) (ha : a ≤ 2 * s + 4) :
    Function.Bijective (boxMap s a ha) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨boxMap_injective s a ha, ?_⟩
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← pow_add, ← pow_add, Nat.add_sub_cancel' ha]
  congr 1
  ring

theorem exists_unique_in_box (s a : ℕ) (ha : a ≤ 2 * s + 4)
    (b : Fin (2 ^ a) × Fin (2 ^ (2 * s + 4 - a))) :
    ∃! p, boxMap s a ha p = b :=
  (boxMap_bijective s a ha).existsUnique b

/-! ### Dictionary: box index versus elementary interval -/

/-- `x / 2 ^ e = b` exactly when `x` lies in the half-open interval
`[b * 2 ^ e, (b + 1) * 2 ^ e)`; after division by `2 ^ m` this is the dyadic
elementary interval `[b / 2 ^ (m - e), (b + 1) / 2 ^ (m - e))`. -/
theorem div_pow_eq_iff (x e b : ℕ) :
    x / 2 ^ e = b ↔ b * 2 ^ e ≤ x ∧ x < (b + 1) * 2 ^ e := by
  have hpos : 0 < 2 ^ e := by positivity
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self x _, ?_⟩
    rw [add_mul, one_mul]
    exact Nat.lt_div_mul_add hpos
  · rintro ⟨h1, h2⟩
    exact Nat.div_eq_of_lt_le h1 h2

end GKEvenNet
