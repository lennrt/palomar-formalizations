module

public import ShellResearch.FiniteSample

/-! Integer back-substitution is stable under coordinate-dependent half-pivot errors. -/
@[expose] public section

namespace ShellResearch
open Finset

/-- Generic descending integer back-substitution, with no accumulation of errors.
`rounded` expresses any fixed nearest-integer rule. All coefficients and samples are real;
only the unknown and reconstructed coordinates are integers. -/
theorem rounded_triangular_recovery {n : ℕ} (A : Fin n → Fin n → ℝ)
    (c z : Fin n → ℤ) (μhat : Fin n → ℝ)
    (diag : ∀ k, z k ≠ c k → 0 < A k k)
    (below : ∀ i k, z k ≠ c k → i < k → A i k = 0)
    (accurate : ∀ k, z k ≠ c k → |μhat k - ∑ i, (c i : ℝ) * A i k| < A k k / 2)
    (rounded : ∀ k, z k ≠ c k →
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * A i k) / A k k -
        (z k : ℝ)| ≤ 1 / 2) : z = c := by
  classical
  by_contra hne
  have hset : (univ.filter fun k => z k ≠ c k).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact ⟨k, by simpa using hk⟩
  let k := (univ.filter fun k => z k ≠ c k).max' hset
  have hk : z k ≠ c k := by
    have := max'_mem _ hset
    simpa [k] using this
  have higher : ∀ i, k < i → z i = c i := by
    intro i hi
    by_contra hz
    have hle : i ≤ k := le_max' _ i (by simp [hz])
    exact absurd hi (not_lt.mpr hle)
  have sumEq : (∑ i, (c i : ℝ) * A i k) =
      (c k : ℝ) * A k k + ∑ i ∈ univ.filter (fun i => k < i), (c i : ℝ) * A i k := by
    calc
      _ = ∑ i : Fin n,
          ((if i = k then (c k : ℝ) * A k k else 0) +
           (if k < i then (c i : ℝ) * A i k else 0)) := by
        apply sum_congr rfl
        intro i _
        rcases lt_trichotomy i k with hlt | heq | hgt
        · simp [below i k hk hlt, ne_of_lt hlt, not_lt.mpr hlt.le]
        · subst i; simp
        · simp [ne_of_gt hgt, hgt]
      _ = _ := by simp [sum_add_distrib, sum_filter]
  have higherSum : (∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * A i k) =
      ∑ i ∈ univ.filter (fun i => k < i), (c i : ℝ) * A i k := by
    apply sum_congr rfl
    intro i hi
    rw [higher i (by simpa using hi)]
  let v := (μhat k - ∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * A i k) / A k k
  have heq : v - (c k : ℝ) = (μhat k - ∑ i, (c i : ℝ) * A i k) / A k k := by
    dsimp [v]
    rw [higherSum, sumEq]
    field_simp [ne_of_gt (diag k hk)]
    ring
  have hv : |v - (c k : ℝ)| < 1 / 2 :=
    pivot_rounding_margin (diag k hk) heq (accurate k hk)
  have hz := integer_identified_by_half_gap (c k) (z k) v hv (rounded k hk)
  exact hk hz.symm

/-- The same argument applies to square recovery at the deepest nonzero coordinate. -/
theorem rounded_square_recovery (d : ℤ) (r : ℤ) (estimate scale : ℝ)
    (hs : 0 < scale) (herr : |estimate - (d : ℝ) ^ 2 * scale| < scale / 2)
    (hround : |estimate / scale - (r : ℝ)| ≤ 1 / 2) : r = d ^ 2 := by
  have hmargin : |estimate / scale - ((d ^ 2 : ℤ) : ℝ)| < 1 / 2 := by
    apply pivot_rounding_margin (noise := estimate - (d : ℝ) ^ 2 * scale) hs
    · push_cast
      field_simp [ne_of_gt hs]
    · exact herr
  exact (integer_identified_by_half_gap (d ^ 2) r (estimate / scale) hmargin hround).symm

/-- Corrected covariance error in the model has the precise margin used by diagonal
thresholding and by integer recovery. This turns separate Bernstein good-event estimates
into the hypothesis required by those deterministic operations. -/
theorem weighted_good_event_to_covariance_margin {n : ℕ}
    (t : ℝ) (s : Fin n → ℝ) (C Zbar e : Fin n → ℝ) (f : ℝ)
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : ∀ k, 0 < s k)
    (hz : ∀ k, |Zbar k - C k| ≤ t * s k / 5)
    (he : ∀ k, |e k| ≤ t * s k / 5) (hf : |f| ≤ t / 5) :
    ∀ k, |2 * ((Zbar k - e k * f) - C k)| < t * s k / 2 := by
  intro k
  have h := (corrected_covariance_error ht ht1 (hs k) (hz k) (he k) hf).2
  have heq : (Zbar k - e k * f) - C k = (Zbar k - C k) - e k * f := by ring
  rw [heq]
  exact h

end ShellResearch
