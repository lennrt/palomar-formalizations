/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Author: Lennart Rudolph
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import Mathlib.Tactic

/-!
# Fixed-width bit reversal

`rev n k` reverses the low `n` binary digits of `k`.  The two facts the net
proof needs are the splitting identity `rev_split` (reversal of a concatenation
is the swapped concatenation of the reversals) and injectivity on `[0, 2^n)`,
which follows from the involution `rev_rev`.
-/

namespace GKEvenNet

/-- Reverse the low `n` binary digits of `k`: bit `i` of `k` becomes bit `n-1-i`. -/
def rev : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, k => 2 ^ n * (k % 2) + rev n (k / 2)

@[simp] theorem rev_zero_left (k : ℕ) : rev 0 k = 0 := rfl

theorem rev_succ (n k : ℕ) : rev (n + 1) k = 2 ^ n * (k % 2) + rev n (k / 2) := rfl

@[simp] theorem rev_zero_right (n : ℕ) : rev n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rev_succ, ih]

theorem rev_lt (n k : ℕ) : rev n k < 2 ^ n := by
  induction n generalizing k with
  | zero => simp [rev]
  | succ n ih =>
    rw [rev_succ, pow_succ]
    have h1 := ih (k / 2)
    have h2 : k % 2 < 2 := Nat.mod_lt _ (by norm_num)
    nlinarith

/-- Reversal of a concatenation: if `t < 2^a`, then reversing the `a + s` low bits of
`2^a * K + t` gives `2^s * rev a t + rev s K`. -/
theorem rev_split (a s K t : ℕ) (ht : t < 2 ^ a) :
    rev (a + s) (2 ^ a * K + t) = 2 ^ s * rev a t + rev s K := by
  induction a generalizing t with
  | zero =>
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    simp
  | succ a ih =>
    have e : a + 1 + s = (a + s) + 1 := by omega
    rw [e, rev_succ]
    have hmod : (2 ^ (a + 1) * K + t) % 2 = t % 2 := by
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc, Nat.mul_add_mod]
    have hdiv : (2 ^ (a + 1) * K + t) / 2 = 2 ^ a * K + t / 2 := by
      rw [pow_succ, mul_comm (2 ^ a) 2, mul_assoc, Nat.mul_add_div (by norm_num)]
    have ht2 : t / 2 < 2 ^ a := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [pow_succ] at ht
      exact ht
    rw [hmod, hdiv, ih (t / 2) ht2, rev_succ]
    ring

/-- Reversal is an involution on `[0, 2^n)`. -/
theorem rev_rev (n : ℕ) : ∀ k, k < 2 ^ n → rev n (rev n k) = k := by
  induction n with
  | zero =>
    intro k hk
    have : k = 0 := by simpa using hk
    subst this
    rfl
  | succ n ih =>
    intro k hk
    rw [rev_succ n k]
    rw [rev_split n 1 (k % 2) (rev n (k / 2)) (rev_lt n _)]
    have hk2 : k / 2 < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]
      rw [pow_succ] at hk
      exact hk
    rw [ih (k / 2) hk2]
    have : rev 1 (k % 2) = k % 2 := by
      simp [rev_succ]
    rw [this]
    omega

/-- Reversal is injective on `[0, 2^n)`. -/
theorem rev_inj {n k k' : ℕ} (hk : k < 2 ^ n) (hk' : k' < 2 ^ n)
    (h : rev n k = rev n k') : k = k' := by
  have := congrArg (rev n) h
  rwa [rev_rev n k hk, rev_rev n k' hk'] at this

/-- `rev (i + 1) 1 = 2 ^ i`. -/
theorem rev_one (i : ℕ) : rev (i + 1) 1 = 2 ^ i := by
  simp [rev_succ]

/-- The reversal of a single set bit: `rev (i + 1 + j) (2 ^ i) = 2 ^ j`. -/
theorem rev_pow (i j : ℕ) : rev (i + (j + 1)) (2 ^ i) = 2 ^ j := by
  have h := rev_split i (j + 1) 1 0 (by positivity)
  rw [mul_one, add_zero] at h
  rw [h, rev_one]
  simp

end GKEvenNet
