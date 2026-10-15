module

public import ShellResearch.Deterministic

/-! Deterministic correctness for the actual shell-model descending reconstruction. -/
@[expose] public section

namespace ShellResearch
open Finset LossyShell
variable {n : ℕ}

/-- The weighted good-event tolerance is smaller than half of every mean pivot. -/
theorem weighted_error_lt_mean_pivot {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (k : Fin n) : p ^ n * (1 - p ^ (k.val + 1)) / 5 < p ^ (k.val + 1) / 2 := by
  have ht := pow_le_pow_of_le_one hp.le hp1.le (show k.val + 1 ≤ n by omega)
  have hpos := pow_pos hp (k.val + 1)
  have htpos := pow_pos hp n
  nlinarith [mul_pos htpos hpos]

/-- The mean equations, with the folded integer vector made explicit. -/
theorem mean_eq_fold (p : ℝ) (a b : Population n) (k : Fin n) :
    twoLegMean p a b k = ∑ i, ((a i + b i : ℕ) : ℝ) * landProb p i k.val := by
  rw [twoLegMean_eq]
  unfold legMean
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro i _
  push_cast
  ring

/-- The empirical descending mean recurrence recovers the entire fold exactly.
This uses the concrete loss-channel mean, and allows any nearest-integer tie rule. -/
theorem fold_recovery {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : Population n) (cHat : Fin n → ℤ) (μhat : Fin n → ℝ)
    (haccurate : ∀ k, |μhat k - twoLegMean p a b k| ≤ p ^ n * (1 - p ^ (k.val + 1)) / 5)
    (hrounded : ∀ k,
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (cHat i : ℝ) * landProb p i k.val) /
        p ^ (k.val + 1) - (cHat k : ℝ)| ≤ 1 / 2) :
    cHat = fun i => ((a i + b i : ℕ) : ℤ) := by
  apply rounded_triangular_recovery (A := fun i k => landProb p i k.val)
  · intro k _; rw [landProb_self]; positivity
  · intro i k _ hik; exact landProb_eq_zero_of_lt p hik
  · intro k _
    rw [landProb_self]
    have hμ := haccurate k
    rw [mean_eq_fold] at hμ
    simpa only [Int.cast_natCast] using
      lt_of_le_of_lt hμ (weighted_error_lt_mean_pivot hp hp1 k)
  · intro k _
    simpa only [landProb_self] using hrounded k

/-- `p^n` is a uniform lower bound for every diagonal survival factor. -/
theorem uniform_pivot_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (k : Fin n) :
    p ^ n ≤ p ^ (k.val + 1) :=
  pow_le_pow_of_le_one hp.le hp1.le (by omega)

/-- The full covariance-column recurrence recovers the oriented integer difference vector.
The chosen deepest index and its positive square root may have been found by the diagonal
stage; their statistical correctness is supplied separately by `deepest_threshold` and
`rounded_square_recovery`. -/
theorem difference_recovery {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (d z : Fin n → ℤ) (m : Fin n) (column : Fin n → ℝ)
    (hm : 0 < d m) (htop : ∀ i, m < i → d i = 0)
    (hzm : z m = d m) (hztop : ∀ i, m < i → z i = 0)
    (haccurate : ∀ k, k < m →
      |column k - Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ)) k.val m.val| <
        p ^ n * (1 - p ^ (k.val + 1)) / 2)
    (hrounded : ∀ k, k < m →
      |(column k / ((z m : ℝ) * p ^ (m.val + 1)) +
        ∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * landProb p i k.val) /
        (1 - p ^ (k.val + 1)) - (z k : ℝ)| ≤ 1 / 2) : z = d := by
  classical
  let A : Fin n → Fin n → ℝ := fun i k =>
    (if i = k then 1 else 0) - landProb p i k.val
  have hdiag : ∀ k, A k k = 1 - p ^ (k.val + 1) := by
    intro k; simp [A, landProb_self]
  have hsmall : ∀ k, z k ≠ d k → k < m := by
    intro k hk
    rcases lt_trichotomy k m with hlt | heq | hgt
    · exact hlt
    · subst k; exact absurd hzm hk
    · exact absurd (by rw [hztop k hgt, htop k hgt]) hk
  have hdm : 1 ≤ (d m : ℝ) := by exact_mod_cast hm
  have hdmpos : 0 < (d m : ℝ) := by linarith
  have hpM : 0 < p ^ (m.val + 1) := pow_pos hp _
  have hden : 0 < (d m : ℝ) * p ^ (m.val + 1) := mul_pos hdmpos hpM
  have hbound : p ^ n ≤ (d m : ℝ) * p ^ (m.val + 1) := by
    calc _ ≤ p ^ (m.val + 1) := uniform_pivot_le hp hp1 m
         _ ≤ _ := by nlinarith
  have hsum : ∀ k, (∑ i, (d i : ℝ) * A i k) =
      (d k : ℝ) - ∑ i, (d i : ℝ) * landProb p i k.val := by
    intro k
    simp [A, mul_sub, sum_sub_distrib, mul_ite]
  apply rounded_triangular_recovery A d z
    (fun k => column k / ((d m : ℝ) * p ^ (m.val + 1)))
  · intro k _
    rw [hdiag]
    exact sub_pos.mpr (pow_lt_one₀ hp.le hp1 (by omega))
  · intro i k _ hik
    simp [A, ne_of_lt hik, landProb_eq_zero_of_lt p hik]
  · intro k hk
    have hkm := hsmall k hk
    have hform := Qform_col_top p (d := fun i => (d i : ℝ))
      (m := m) (by intro i hi; simp [htop i hi]) hkm
    have hs : 0 < 1 - p ^ (k.val + 1) :=
      sub_pos.mpr (pow_lt_one₀ hp.le hp1 (by omega))
    rw [hsum, hdiag]
    have heq : column k / ((d m : ℝ) * p ^ (m.val + 1)) -
        ((d k : ℝ) - ∑ i, (d i : ℝ) * landProb p i k.val) =
      (column k - Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ)) k.val m.val) /
        ((d m : ℝ) * p ^ (m.val + 1)) := by
      rw [hform]
      field_simp
    rw [heq, abs_div, abs_of_pos hden]
    apply (div_lt_iff₀ hden).2
    have hh := haccurate k hkm
    have hh2 := mul_le_mul_of_nonneg_right hbound hs.le
    nlinarith
  · intro k hk
    have hh := hrounded k (hsmall k hk)
    rw [hzm] at hh
    rw [hdiag]
    have hoff : (∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * A i k) =
        -(∑ i ∈ univ.filter (fun i => k < i), (z i : ℝ) * landProb p i k.val) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i hi
      have hik : k < i := by simpa using hi
      simp [A, ne_of_gt hik]
    rw [hoff, sub_neg_eq_add]
    exact hh

/-- The diagonal stage locates the true deepest coordinate and recovers its positive
integer square root. Thresholds vary with depth. -/
theorem diagonal_stage {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (d z : Fin n → ℤ) (m selected : Fin n) (diagonal : Fin n → ℝ)
    (hm : 0 < d m) (htop : ∀ i, m < i → d i = 0)
    (haccurate : ∀ k,
      |diagonal k - Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ)) k.val k.val| <
        p ^ n * (1 - p ^ (k.val + 1)) / 2)
    (hcross : p ^ n * (1 - p ^ (selected.val + 1)) / 2 < diagonal selected)
    (hmax : ∀ k, p ^ n * (1 - p ^ (k.val + 1)) / 2 < diagonal k → k ≤ selected)
    (hzpos : 0 < z selected)
    (hroot : |diagonal selected / (p ^ (selected.val + 1) *
      (1 - p ^ (selected.val + 1))) - ((z selected : ℝ) ^ 2)| ≤ 1 / 2) :
    selected = m ∧ z m = d m := by
  have ht : 0 < p ^ n := pow_pos hp _
  have hs : ∀ k : Fin n, 0 < 1 - p ^ (k.val + 1) := by
    intro k; exact sub_pos.mpr (pow_lt_one₀ hp.le hp1 (by omega))
  have hQtop := Qform_diag_top p (d := fun i => (d i : ℝ))
    (m := m) (by intro i hi; simp [htop i hi])
  have hdm : (1 : ℝ) ≤ d m := by exact_mod_cast hm
  have htopgap : p ^ n * (1 - p ^ (m.val + 1)) ≤
      Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ)) m.val m.val := by
    rw [hQtop]
    have hpm := uniform_pivot_le hp hp1 m
    have hprod := mul_le_mul_of_nonneg_right hpm (hs m).le
    have hfactor : 1 ≤ (d m : ℝ) ^ 2 := by nlinarith
    have hpiv : 0 ≤ p ^ (m.val + 1) * (1 - p ^ (m.val + 1)) :=
      le_of_lt (mul_pos (pow_pos hp _) (hs m))
    nlinarith [mul_le_mul_of_nonneg_right hfactor hpiv]
  have hthreshold := deepest_threshold
    (fun k => Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ)) k.val k.val)
    diagonal (fun k => p ^ n * (1 - p ^ (k.val + 1))) m
    (fun k => mul_pos ht (hs k)) haccurate
    (by intro k hk; exact Qform_diag_beyond p (by intro i hi; simp [htop i hi]) hk)
    htopgap
  have hsel : selected = m := by
    apply le_antisymm
    · by_contra hh
      have hgt : m < selected := lt_of_not_ge hh
      have := hthreshold.2 selected hgt
      linarith
    · exact hmax m hthreshold.1
  refine ⟨hsel, ?_⟩
  subst selected
  have hpiv : 0 < p ^ (m.val + 1) * (1 - p ^ (m.val + 1)) :=
    mul_pos (pow_pos hp _) (hs m)
  have herr : |diagonal m - (d m : ℝ) ^ 2 *
      (p ^ (m.val + 1) * (1 - p ^ (m.val + 1)))| <
        (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) / 2 := by
    have hacc := haccurate m
    rw [hQtop] at hacc
    have hpm := mul_le_mul_of_nonneg_right (uniform_pivot_le hp hp1 m) (hs m).le
    linarith
  have hround : |diagonal m / (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) -
      (((z m) ^ 2 : ℤ) : ℝ)| ≤ 1 / 2 := by exact_mod_cast hroot
  have hsq := rounded_square_recovery (d m) ((z m) ^ 2) (diagonal m)
    (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) hpiv herr hround
  nlinarith

/-- All deterministic reconstruction stages for an oriented nonzero imbalance.
`phi` is the empirically corrected covariance array. Its weighted accuracy is the
conclusion of the separately checked covariance-error lemma on the concentration event.
The orientation `a m > b m` is without loss of generality because the output is unordered. -/
theorem deterministic_nonzero_pipeline {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : Population n) (cHat dHat : Fin n → ℤ) (μhat : Fin n → ℝ)
    (phi : Fin n → Fin n → ℝ) (m selected : Fin n)
    (hm : 0 < (a m : ℤ) - b m)
    (htop : ∀ i, m < i → (a i : ℤ) - b i = 0)
    (hmean : ∀ k, |μhat k - twoLegMean p a b k| ≤
      p ^ n * (1 - p ^ (k.val + 1)) / 5)
    (hfoldRound : ∀ k,
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (cHat i : ℝ) * landProb p i k.val) /
        p ^ (k.val + 1) - (cHat k : ℝ)| ≤ 1 / 2)
    (hdiag : ∀ k, |phi k k - Qform p (fun i => (((a i : ℤ) - b i : ℤ) : ℝ))
      (fun i => (((a i : ℤ) - b i : ℤ) : ℝ)) k.val k.val| <
        p ^ n * (1 - p ^ (k.val + 1)) / 2)
    (hcross : p ^ n * (1 - p ^ (selected.val + 1)) / 2 < phi selected selected)
    (hmax : ∀ k, p ^ n * (1 - p ^ (k.val + 1)) / 2 < phi k k → k ≤ selected)
    (hzpos : 0 < dHat selected)
    (hroot : |phi selected selected / (p ^ (selected.val + 1) *
      (1 - p ^ (selected.val + 1))) - (dHat selected : ℝ) ^ 2| ≤ 1 / 2)
    (hzabove : ∀ i, selected < i → dHat i = 0)
    (hcolumn : ∀ k, k < selected → |phi k selected -
      Qform p (fun i => (((a i : ℤ) - b i : ℤ) : ℝ))
        (fun i => (((a i : ℤ) - b i : ℤ) : ℝ)) k.val selected.val| <
          p ^ n * (1 - p ^ (k.val + 1)) / 2)
    (hdiffRound : ∀ k, k < selected →
      |(phi k selected / ((dHat selected : ℝ) * p ^ (selected.val + 1)) +
        ∑ i ∈ univ.filter (fun i => k < i), (dHat i : ℝ) * landProb p i k.val) /
        (1 - p ^ (k.val + 1)) - (dHat k : ℝ)| ≤ 1 / 2) :
    cHat = (fun i => ((a i + b i : ℕ) : ℤ)) ∧ selected = m ∧
      dHat = (fun i => (a i : ℤ) - b i) := by
  have hfold := fold_recovery hp hp1 a b cHat μhat hmean hfoldRound
  have hdiagStage := diagonal_stage hp hp1 (fun i => (a i : ℤ) - b i)
    dHat m selected (fun k => phi k k) hm htop hdiag hcross hmax hzpos hroot
  refine ⟨hfold, hdiagStage.1, ?_⟩
  have hsel := hdiagStage.1
  subst selected
  exact difference_recovery hp hp1 (fun i => (a i : ℤ) - b i) dHat m
    (fun k => phi k m) hm htop hdiagStage.2 hzabove hcolumn hdiffRound

/-- The final fold/difference output equals the original ordered pair after the orientation
has been fixed. Thus the unordered pair is correct independently of that orientation. -/
theorem population_from_fold_difference (a b c d : ℤ)
    (hc : c = a + b) (hd : d = a - b) : (c + d) / 2 = a ∧ (c - d) / 2 = b := by
  subst c d
  constructor <;> omega

/-- On the good event, rounding the deepest diagonal necessarily gives a positive
perfect square. This establishes that the algorithm's square-root fallback is not used. -/
theorem rounded_diagonal_has_positive_root {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (d : Fin n → ℤ) (m : Fin n) (estimate : ℝ) (rounded : ℤ)
    (hm : 0 < d m) (htop : ∀ i, m < i → d i = 0)
    (haccurate : |estimate - Qform p (fun i => (d i : ℝ)) (fun i => (d i : ℝ))
      m.val m.val| < p ^ n * (1 - p ^ (m.val + 1)) / 2)
    (hround : |estimate / (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) -
      (rounded : ℝ)| ≤ 1 / 2) : rounded = (d m) ^ 2 ∧ ∃ u : ℤ, 0 < u ∧ u ^ 2 = rounded := by
  have hs : 0 < 1 - p ^ (m.val + 1) :=
    sub_pos.mpr (pow_lt_one₀ hp.le hp1 (by omega))
  have hpiv : 0 < p ^ (m.val + 1) * (1 - p ^ (m.val + 1)) :=
    mul_pos (pow_pos hp _) hs
  have htopEq := Qform_diag_top p (d := fun i => (d i : ℝ))
    (m := m) (by intro i hi; simp [htop i hi])
  rw [htopEq] at haccurate
  have hbound := mul_le_mul_of_nonneg_right (uniform_pivot_le hp hp1 m) hs.le
  have hresult := rounded_square_recovery (d m) rounded estimate
    (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) hpiv (by linarith) hround
  exact ⟨hresult, d m, hm, hresult.symm⟩

/-- The zero-imbalance branch recovers both equal legs and crosses no diagonal threshold. -/
theorem deterministic_symmetric_pipeline {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a : Population n) (cHat : Fin n → ℤ) (μhat diagonal : Fin n → ℝ)
    (hmean : ∀ k, |μhat k - twoLegMean p a a k| ≤
      p ^ n * (1 - p ^ (k.val + 1)) / 5)
    (hfoldRound : ∀ k,
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (cHat i : ℝ) * landProb p i k.val) /
        p ^ (k.val + 1) - (cHat k : ℝ)| ≤ 1 / 2)
    (hdiag : ∀ k, |diagonal k| < p ^ n * (1 - p ^ (k.val + 1)) / 2) :
    (∀ k, cHat k / 2 = (a k : ℤ)) ∧
      ∀ k, ¬ (p ^ n * (1 - p ^ (k.val + 1)) / 2 < diagonal k) := by
  have hc := fold_recovery hp hp1 a a cHat μhat hmean hfoldRound
  constructor
  · intro k
    have hck := congrFun hc k
    push_cast at hck
    omega
  · intro k
    have hh := (abs_lt.mp (hdiag k)).2
    linarith

/-- Every unequal pair admits one of the two orientations used by the nonzero pipeline. -/
theorem exists_deepest_orientation (a b : Population n) (hne : a ≠ b) :
    ∃ m : Fin n, (a m < b m ∨ b m < a m) ∧ ∀ i, m < i → a i = b i := by
  classical
  have hset : (univ.filter fun k => a k ≠ b k).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
    exact ⟨k, by simpa using hk⟩
  let m := (univ.filter fun k => a k ≠ b k).max' hset
  have hm : a m ≠ b m := by
    have := max'_mem _ hset
    simpa [m] using this
  refine ⟨m, lt_or_gt_of_ne hm, ?_⟩
  intro i hi
  by_contra hh
  have hle : i ≤ m := le_max' _ i (by simp [hh])
  exact absurd hi (not_lt.mpr hle)

end ShellResearch
