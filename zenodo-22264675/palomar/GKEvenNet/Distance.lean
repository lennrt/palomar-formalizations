/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Author: Lennart Rudolph
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import GKEvenNet.Net

/-!
# The row-shifted tiling metric

The source tiles the plane with copies of the point set in which each tile row is
shifted by `N / 4` relative to the row below, so the translation lattice is
`Λ = ⟨(N, 0), (N / 4, N)⟩`.  For two points `p = (x, y)` and `p' = (x', y')` the
squared tiling distance is

  `min_{A, B ∈ ℤ} (x' - x + A N + B N / 4)² + (y' - y + B N)²`.

`shiftedSq` computes this minimum in natural-number arithmetic for points with
coordinates in `[0, N)` and `y < y'`, by taking the centered residue of the
horizontal difference for `B ∈ {0, -1, 1}`.  `shiftedSq_le_latVal` and
`shiftedSq_attained` prove that this is the exact lattice minimum.

`witness_sq` evaluates one explicit pair for every even `m ≥ 8` and gives the
upper bound `241 · 2 ^ (m - 8)`; `lowerCheck_m8` is a kernel-checked exhaustive
lower bound at `m = 8`.
-/

namespace GKEvenNet

/-- Centered absolute residue of `u` modulo `N`: the distance from `u` to `N ℤ`. -/
def cres (N u : ℕ) : ℕ := min (u % N) (N - u % N)

/-- Squared tiling distance for `y < y'` (all coordinates below `N`), as the minimum of the
three lattice candidates `B = 0`, `B = -1`, `B = 1`. -/
def shiftedSq (N x y x' y' : ℕ) : ℕ :=
  min (cres N (x' + N - x) ^ 2 + (y' - y) ^ 2)
    (min (cres N (x' + N - x + 3 * (N / 4)) ^ 2 + (N - (y' - y)) ^ 2)
      (cres N (x' + N - x + N / 4) ^ 2 + (y' - y + N) ^ 2))

/-- Squared length of the difference vector `(dx, dy)` after translation by the lattice
vector `A (N, 0) + B (N / 4, N)`. -/
def latVal (N : ℕ) (dx dy A B : ℤ) : ℤ :=
  (dx + A * N + B * ((N / 4 : ℕ) : ℤ)) ^ 2 + (dy + B * N) ^ 2

/-! ### The centered residue is the distance to the lattice `N ℤ` -/

theorem cres_le_half (N u : ℕ) (hN : 0 < N) : cres N u ≤ N / 2 := by
  unfold cres
  have := Nat.mod_lt u hN
  omega

theorem min_le_abs (N ρ : ℕ) (hρ : ρ < N) (A : ℤ) :
    ((min ρ (N - ρ) : ℕ) : ℤ) ≤ |(ρ : ℤ) + A * N| := by
  have hm1 : ((min ρ (N - ρ) : ℕ) : ℤ) ≤ ρ := by exact_mod_cast min_le_left _ _
  have hm2 : ((min ρ (N - ρ) : ℕ) : ℤ) ≤ (N : ℤ) - ρ := by
    have h' : ((min ρ (N - ρ) : ℕ) : ℤ) ≤ ((N - ρ : ℕ) : ℤ) := by
      exact_mod_cast min_le_right ρ (N - ρ)
    rwa [Nat.cast_sub hρ.le] at h'
  have hNpos : (0 : ℤ) ≤ N := by positivity
  rcases lt_trichotomy A 0 with h | h | h
  · have h1 : A ≤ -1 := by omega
    have h2 : A * N ≤ -1 * N := mul_le_mul_of_nonneg_right h1 hNpos
    have hρ' : (ρ : ℤ) < N := by exact_mod_cast hρ
    rw [abs_of_neg (by linarith)]
    linarith
  · rw [h, zero_mul, add_zero, abs_of_nonneg (by positivity)]
    exact hm1
  · have h1 : 1 ≤ A := by omega
    have h2 : 1 * N ≤ A * N := mul_le_mul_of_nonneg_right h1 hNpos
    rw [abs_of_nonneg (by positivity)]
    linarith

theorem cres_sq_le (N u : ℕ) (hN : 0 < N) (A : ℤ) :
    ((cres N u : ℕ) : ℤ) ^ 2 ≤ ((u : ℤ) + A * N) ^ 2 := by
  have hu : (u : ℤ) = (N : ℤ) * ((u / N : ℕ) : ℤ) + ((u % N : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod u N).symm
  have hρ : u % N < N := Nat.mod_lt _ hN
  have hw : (u : ℤ) + A * N = ((u % N : ℕ) : ℤ) + (((u / N : ℕ) : ℤ) + A) * N := by
    rw [hu]; ring
  rw [hw]
  have key := min_le_abs N (u % N) hρ (((u / N : ℕ) : ℤ) + A)
  have h0 : (0 : ℤ) ≤ ((cres N u : ℕ) : ℤ) := by positivity
  calc ((cres N u : ℕ) : ℤ) ^ 2
      ≤ |((u % N : ℕ) : ℤ) + (((u / N : ℕ) : ℤ) + A) * N| ^ 2 :=
        pow_le_pow_left₀ h0 key 2
    _ = (((u % N : ℕ) : ℤ) + (((u / N : ℕ) : ℤ) + A) * N) ^ 2 := sq_abs _

theorem cres_sq_exists (N u : ℕ) (hN : 0 < N) :
    ∃ A : ℤ, ((cres N u : ℕ) : ℤ) ^ 2 = ((u : ℤ) + A * N) ^ 2 := by
  have hu : (u : ℤ) = (N : ℤ) * ((u / N : ℕ) : ℤ) + ((u % N : ℕ) : ℤ) := by
    exact_mod_cast (Nat.div_add_mod u N).symm
  have hρ : u % N < N := Nat.mod_lt _ hN
  unfold cres
  rcases le_total (u % N) (N - u % N) with h | h
  · refine ⟨-((u / N : ℕ) : ℤ), ?_⟩
    rw [min_eq_left h, hu]
    ring
  · refine ⟨-((u / N : ℕ) : ℤ) - 1, ?_⟩
    rw [min_eq_right h, hu]
    push_cast [Nat.cast_sub hρ.le]
    ring

/-! ### `shiftedSq` is the exact lattice minimum -/

theorem shiftedSq_le_c0 (T x y x' y' : ℕ) :
    shiftedSq (4 * T) x y x' y' ≤ cres (4 * T) (x' + 4 * T - x) ^ 2 + (y' - y) ^ 2 := by
  have hdiv : 4 * T / 4 = T := by omega
  unfold shiftedSq; rw [hdiv]; exact min_le_left _ _

theorem shiftedSq_le_cm (T x y x' y' : ℕ) :
    shiftedSq (4 * T) x y x' y'
      ≤ cres (4 * T) (x' + 4 * T - x + 3 * T) ^ 2 + (4 * T - (y' - y)) ^ 2 := by
  have hdiv : 4 * T / 4 = T := by omega
  unfold shiftedSq; rw [hdiv]; exact (min_le_right _ _).trans (min_le_left _ _)

theorem shiftedSq_le_cp (T x y x' y' : ℕ) :
    shiftedSq (4 * T) x y x' y'
      ≤ cres (4 * T) (x' + 4 * T - x + T) ^ 2 + (y' - y + 4 * T) ^ 2 := by
  have hdiv : 4 * T / 4 = T := by omega
  unfold shiftedSq; rw [hdiv]; exact (min_le_right _ _).trans (min_le_right _ _)

/-- For `|B| ≥ 2` the vertical component alone is at least `4 T + 1`, while the candidate
minimum is at most `8 T ^ 2`. -/
theorem far_case (T x y x' y' : ℕ) (hT : 0 < T)
    (hy' : y' < 4 * T) (hyy : y < y') (A B : ℤ)
    (hB : B ≤ -2 ∨ 2 ≤ B) :
    ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
      ≤ ((x' : ℤ) - x + A * (4 * T) + B * T) ^ 2 + ((y' : ℤ) - y + B * (4 * T)) ^ 2 := by
  have hN : 0 < 4 * T := by omega
  have hsmall : shiftedSq (4 * T) x y x' y' ≤ 8 * T ^ 2 := by
    have hc0 := cres_le_half (4 * T) (x' + 4 * T - x) hN
    have hcm := cres_le_half (4 * T) (x' + 4 * T - x + 3 * T) hN
    have h2 : 4 * T / 2 = 2 * T := by omega
    rw [h2] at hc0 hcm
    have hc0' : cres (4 * T) (x' + 4 * T - x) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left hc0 2
    have hcm' : cres (4 * T) (x' + 4 * T - x + 3 * T) ^ 2 ≤ (2 * T) ^ 2 :=
      Nat.pow_le_pow_left hcm 2
    rcases le_or_gt (y' - y) (2 * T) with hd | hd
    · have hd' : (y' - y) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left hd 2
      refine (shiftedSq_le_c0 T x y x' y').trans ?_
      nlinarith
    · have hd2 : 4 * T - (y' - y) ≤ 2 * T := by omega
      have hd' : (4 * T - (y' - y)) ^ 2 ≤ (2 * T) ^ 2 := Nat.pow_le_pow_left hd2 2
      refine (shiftedSq_le_cm T x y x' y').trans ?_
      nlinarith
  have hsmall' : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ) ≤ 8 * (T : ℤ) ^ 2 := by
    exact_mod_cast hsmall
  have hvert : 4 * (T : ℤ) + 1 ≤ |(y' : ℤ) - y + B * (4 * T)| := by
    have hy1 : (1 : ℤ) ≤ (y' : ℤ) - y := by
      have : (y : ℤ) < y' := by exact_mod_cast hyy
      linarith
    have hy2 : (y' : ℤ) - y ≤ 4 * (T : ℤ) - 1 := by
      have : (y' : ℤ) < 4 * (T : ℤ) := by exact_mod_cast hy'
      linarith
    have hTz : (0 : ℤ) ≤ 4 * (T : ℤ) := by positivity
    rcases hB with h | h
    · have h2 : B * (4 * (T : ℤ)) ≤ -2 * (4 * (T : ℤ)) := mul_le_mul_of_nonneg_right h hTz
      rw [abs_of_neg (by linarith)]
      linarith
    · have h2 : 2 * (4 * (T : ℤ)) ≤ B * (4 * (T : ℤ)) := mul_le_mul_of_nonneg_right h hTz
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hsq : (4 * (T : ℤ) + 1) ^ 2 ≤ ((y' : ℤ) - y + B * (4 * T)) ^ 2 := by
    calc (4 * (T : ℤ) + 1) ^ 2 ≤ |(y' : ℤ) - y + B * (4 * T)| ^ 2 :=
          pow_le_pow_left₀ (by positivity) hvert 2
      _ = _ := sq_abs _
  have hT' : (1 : ℤ) ≤ T := by exact_mod_cast hT
  nlinarith [sq_nonneg ((x' : ℤ) - x + A * (4 * T) + B * T)]

/-- `shiftedSq` is a lower bound for every lattice translate. -/
theorem shiftedSq_le_latVal (T x y x' y' : ℕ) (hT : 0 < T)
    (hx : x < 4 * T) (hy' : y' < 4 * T) (hyy : y < y') (A B : ℤ) :
    ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
      ≤ latVal (4 * T) ((x' : ℤ) - x) ((y' : ℤ) - y) A B := by
  have hN : 0 < 4 * T := by omega
  have hdiv : 4 * T / 4 = T := by omega
  have hxx : x ≤ x' + 4 * T := by omega
  unfold latVal
  rw [hdiv]
  push_cast
  rcases lt_trichotomy B 0 with hB | hB | hB
  · rcases eq_or_lt_of_le (show B ≤ -1 by omega) with hB1 | hB2
    · subst hB1
      have h1 : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
          ≤ ((cres (4 * T) (x' + 4 * T - x + 3 * T) : ℕ) : ℤ) ^ 2
            + (4 * (T : ℤ) - ((y' : ℤ) - y)) ^ 2 := by
        have h' : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
            ≤ ((cres (4 * T) (x' + 4 * T - x + 3 * T) ^ 2 + (4 * T - (y' - y)) ^ 2 : ℕ) : ℤ) := by
          exact_mod_cast shiftedSq_le_cm T x y x' y'
        push_cast [hyy.le, show y' - y ≤ 4 * T by omega] at h'
        exact h'
      have h2 := cres_sq_le (4 * T) (x' + 4 * T - x + 3 * T) hN (A - 2)
      have e : ((x' + 4 * T - x + 3 * T : ℕ) : ℤ) + (A - 2) * ((4 * T : ℕ) : ℤ)
          = (x' : ℤ) - x + A * (4 * T) + (-1) * T := by
        push_cast [hxx]; ring
      rw [e] at h2
      calc ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
          ≤ ((cres (4 * T) (x' + 4 * T - x + 3 * T) : ℕ) : ℤ) ^ 2
            + (4 * (T : ℤ) - ((y' : ℤ) - y)) ^ 2 := h1
        _ ≤ ((x' : ℤ) - x + A * (4 * T) + (-1) * T) ^ 2 + (4 * (T : ℤ) - ((y' : ℤ) - y)) ^ 2 :=
            add_le_add h2 le_rfl
        _ = _ := by ring
    · exact far_case T x y x' y' hT hy' hyy A B (Or.inl (by omega))
  · subst hB
    have h1 : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
        ≤ ((cres (4 * T) (x' + 4 * T - x) : ℕ) : ℤ) ^ 2 + ((y' : ℤ) - y) ^ 2 := by
      have h' : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
          ≤ ((cres (4 * T) (x' + 4 * T - x) ^ 2 + (y' - y) ^ 2 : ℕ) : ℤ) := by
        exact_mod_cast shiftedSq_le_c0 T x y x' y'
      push_cast [hyy.le] at h'
      exact h'
    have h2 := cres_sq_le (4 * T) (x' + 4 * T - x) hN (A - 1)
    have e : ((x' + 4 * T - x : ℕ) : ℤ) + (A - 1) * ((4 * T : ℕ) : ℤ)
        = (x' : ℤ) - x + A * (4 * T) + 0 * T := by
      push_cast [hxx]; ring
    rw [e] at h2
    calc ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
        ≤ ((cres (4 * T) (x' + 4 * T - x) : ℕ) : ℤ) ^ 2 + ((y' : ℤ) - y) ^ 2 := h1
      _ ≤ ((x' : ℤ) - x + A * (4 * T) + 0 * T) ^ 2 + ((y' : ℤ) - y) ^ 2 :=
          add_le_add h2 le_rfl
      _ = _ := by ring
  · rcases eq_or_lt_of_le (show 1 ≤ B by omega) with hB1 | hB2
    · subst hB1
      have h1 : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
          ≤ ((cres (4 * T) (x' + 4 * T - x + T) : ℕ) : ℤ) ^ 2
            + ((y' : ℤ) - y + 4 * T) ^ 2 := by
        have h' : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
            ≤ ((cres (4 * T) (x' + 4 * T - x + T) ^ 2 + (y' - y + 4 * T) ^ 2 : ℕ) : ℤ) := by
          exact_mod_cast shiftedSq_le_cp T x y x' y'
        push_cast [hyy.le] at h'
        exact h'
      have h2 := cres_sq_le (4 * T) (x' + 4 * T - x + T) hN (A - 1)
      have e : ((x' + 4 * T - x + T : ℕ) : ℤ) + (A - 1) * ((4 * T : ℕ) : ℤ)
          = (x' : ℤ) - x + A * (4 * T) + 1 * T := by
        push_cast [hxx]; ring
      rw [e] at h2
      calc ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
          ≤ ((cres (4 * T) (x' + 4 * T - x + T) : ℕ) : ℤ) ^ 2 + ((y' : ℤ) - y + 4 * T) ^ 2 := h1
        _ ≤ ((x' : ℤ) - x + A * (4 * T) + 1 * T) ^ 2 + ((y' : ℤ) - y + 4 * T) ^ 2 :=
            add_le_add h2 le_rfl
        _ = _ := by ring
    · exact far_case T x y x' y' hT hy' hyy A B (Or.inr (by omega))

/-- The candidate minimum is attained by some lattice translate. -/
theorem shiftedSq_attained (T x y x' y' : ℕ) (hT : 0 < T)
    (hx : x < 4 * T) (hyy : y < y') (hy' : y' < 4 * T) :
    ∃ A B : ℤ, ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ)
      = latVal (4 * T) ((x' : ℤ) - x) ((y' : ℤ) - y) A B := by
  have hN : 0 < 4 * T := by omega
  have hdiv : 4 * T / 4 = T := by omega
  have hxx : x ≤ x' + 4 * T := by omega
  unfold latVal shiftedSq
  rw [hdiv]
  rcases min_choice (cres (4 * T) (x' + 4 * T - x) ^ 2 + (y' - y) ^ 2)
      (min (cres (4 * T) (x' + 4 * T - x + 3 * T) ^ 2 + (4 * T - (y' - y)) ^ 2)
        (cres (4 * T) (x' + 4 * T - x + T) ^ 2 + (y' - y + 4 * T) ^ 2)) with h | h
  · rw [h]
    obtain ⟨A, hA⟩ := cres_sq_exists (4 * T) (x' + 4 * T - x) hN
    refine ⟨A + 1, 0, ?_⟩
    push_cast [hxx, hyy.le] at hA ⊢
    rw [hA]; ring
  · rw [h]
    rcases min_choice (cres (4 * T) (x' + 4 * T - x + 3 * T) ^ 2 + (4 * T - (y' - y)) ^ 2)
        (cres (4 * T) (x' + 4 * T - x + T) ^ 2 + (y' - y + 4 * T) ^ 2) with h2 | h2
    · rw [h2]
      obtain ⟨A, hA⟩ := cres_sq_exists (4 * T) (x' + 4 * T - x + 3 * T) hN
      refine ⟨A + 2, -1, ?_⟩
      push_cast [hxx, hyy.le, show y' - y ≤ 4 * T by omega] at hA ⊢
      rw [hA]; ring
    · rw [h2]
      obtain ⟨A, hA⟩ := cres_sq_exists (4 * T) (x' + 4 * T - x + T) hN
      refine ⟨A + 1, 1, ?_⟩
      push_cast [hxx, hyy.le] at hA ⊢
      rw [hA]; ring

/-- `shiftedSq` equals `b` exactly when `b` is the minimum of the lattice value over all
`(A, B) ∈ ℤ²`: every translate is at least `b` and some translate attains `b`. -/
theorem shiftedSq_eq_iff (T x y x' y' : ℕ) (hT : 0 < T)
    (hx : x < 4 * T) (hy' : y' < 4 * T) (hyy : y < y') (b : ℕ) :
    shiftedSq (4 * T) x y x' y' = b ↔
      (∀ A B : ℤ, (b : ℤ) ≤ latVal (4 * T) ((x' : ℤ) - x) ((y' : ℤ) - y) A B) ∧
      (∃ A B : ℤ, latVal (4 * T) ((x' : ℤ) - x) ((y' : ℤ) - y) A B = b) := by
  constructor
  · rintro rfl
    refine ⟨fun A B => shiftedSq_le_latVal T x y x' y' hT hx hy' hyy A B, ?_⟩
    obtain ⟨A, B, h⟩ := shiftedSq_attained T x y x' y' hT hx hyy hy'
    exact ⟨A, B, h.symm⟩
  · rintro ⟨hle, A, B, hAB⟩
    have h1 : ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ) ≤ b := by
      rw [← hAB]
      exact shiftedSq_le_latVal T x y x' y' hT hx hy' hyy A B
    obtain ⟨A', B', h2⟩ := shiftedSq_attained T x y x' y' hT hx hyy hy'
    have h3 : (b : ℤ) ≤ ((shiftedSq (4 * T) x y x' y' : ℕ) : ℤ) := by
      rw [h2]
      exact hle A' B'
    exact_mod_cast le_antisymm h1 h3

end GKEvenNet
