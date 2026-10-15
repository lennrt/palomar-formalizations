module

public import LossyShell.Main
public import Mathlib.Tactic

/-!
# Weighted error control for rare-failure shell tomography

This file adds finite-sample deterministic lemmas to the imported exact-recovery library.
The concentration inequality itself is external; it is not assumed as a Lean axiom.
Indices are zero-based, so the depth of `k : Fin n` is `k.val + 1`.
-/

@[expose] public section

namespace ShellResearch
open Finset LossyShell

variable {n : ℕ}

/-- When the prefix through `k` survives, its report bin is exactly the noiseless bin. -/
theorem legReport_eq_of_prefix_alive (x : Population n) (ω : Pattern n) (k : Fin n)
    (h : ∀ j, j ≤ k → ω j = true) : legReport x ω k.val = x k := by
  have hrank := (aliveRank_eq_succ_iff ω k).mpr h
  unfold legReport
  rw [sum_eq_single k]
  · simp [h k le_rfl, hrank]
  · intro i _ hik
    apply ite_eq_right
    rintro ⟨hi, hri⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · have := aliveRank_le ω i
      have : i.val < k.val := hlt
      omega
    · have := aliveRank_lt_of_lt hgt hi
      omega
  · simp

/-- The centered report is supported on the event that at least one prefix has a failure. -/
theorem twoLegReport_eq_of_prefix_alive (a b : Population n) (ω₁ ω₂ : Pattern n)
    (k : Fin n) (h₁ : ∀ j, j ≤ k → ω₁ j = true)
    (h₂ : ∀ j, j ≤ k → ω₂ j = true) : twoLegReport a b ω₁ ω₂ k = a k + b k := by
  simp [twoLegReport, legReport_eq_of_prefix_alive a ω₁ k h₁,
    legReport_eq_of_prefix_alive b ω₂ k h₂]

/-- Each surviving hop gets at most one contribution from a leg. -/
theorem legReport_le_bound (x : Population n) (ω : Pattern n) (k h : ℕ)
    (hx : ∀ i, x i ≤ h) : legReport x ω k ≤ h := by
  classical
  by_cases he : ∃ i, ω i = true ∧ aliveRank ω i = k + 1
  · obtain ⟨i, hi, hir⟩ := he
    unfold legReport
    rw [sum_eq_single i]
    · simp [hi, hir, hx i]
    · intro j _ hji
      apply ite_eq_right
      rintro ⟨hj, hjr⟩
      rcases lt_or_gt_of_ne hji with hlt | hgt
      · have := aliveRank_lt_of_lt hlt hi; omega
      · have := aliveRank_lt_of_lt hgt hj; omega
    · simp
  · unfold legReport
    have hz : ∀ i, ¬ (ω i = true ∧ aliveRank ω i = k + 1) := by
      simpa only [not_exists] using he
    simp [hz]

/-- Product weights are nonnegative for a genuine survival probability. -/
theorem patternWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (ω : Pattern n) :
    0 ≤ patternWeight p ω := by
  unfold patternWeight
  apply prod_nonneg
  intro i _
  split_ifs <;> linarith

/-- Finite expectation over independent relay masks on the two legs. -/
noncomputable def expect (p : ℝ) (f : Pattern n → Pattern n → ℝ) : ℝ :=
  ∑ ω₁, ∑ ω₂, patternWeight p ω₁ * patternWeight p ω₂ * f ω₁ ω₂

/-- An event indicator for a failure on either of the prefixes through `k`. -/
noncomputable def prefixFailure (k : Fin n) (ω₁ ω₂ : Pattern n) : ℝ :=
  if (∀ j, j ≤ k → ω₁ j = true) ∧ (∀ j, j ≤ k → ω₂ j = true) then 0 else 1

/-- The exact probability of at least one prefix failure is `1 - p^(2(k+1))`. -/
theorem expect_prefixFailure (p : ℝ) (k : Fin n) :
    expect p (prefixFailure k) = 1 - (p ^ (k.val + 1)) ^ 2 := by
  classical
  have hpoint : ∀ ω₁ ω₂ : Pattern n,
      prefixFailure k ω₁ ω₂ = 1 -
      (if ∀ j, j ≤ k → ω₁ j = true then 1 else 0) *
      (if ∀ j, j ≤ k → ω₂ j = true then 1 else 0) := by
    intro ω₁ ω₂
    unfold prefixFailure
    split_ifs <;> simp_all
  simp_rw [expect, hpoint, mul_sub, mul_one, sum_sub_distrib]
  have hone : (∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n,
      patternWeight p ω₁ * patternWeight p ω₂) = 1 := by
    simp_rw [← mul_sum, sum_patternWeight, mul_one]
    exact sum_patternWeight p
  rw [hone]
  have hterm : ∀ ω₁ ω₂ : Pattern n,
      patternWeight p ω₁ * patternWeight p ω₂ *
      ((if ∀ j, j ≤ k → ω₁ j = true then 1 else 0) *
      (if ∀ j, j ≤ k → ω₂ j = true then 1 else 0)) =
      (if ∀ j, j ≤ k → ω₁ j = true then patternWeight p ω₁ else 0) *
      (if ∀ j, j ≤ k → ω₂ j = true then patternWeight p ω₂ else 0) := by
    intro ω₁ ω₂; split_ifs <;> ring
  simp_rw [hterm]
  rw [← sum_mul_sum, sum_weight_prefix_alive, pow_two]

/-- Union bound with the exact prefix probability, without counting individual relays. -/
theorem expect_prefixFailure_le (p : ℝ) (k : Fin n) :
    expect p (prefixFailure k) ≤ 2 * (1 - p ^ (k.val + 1)) := by
  rw [expect_prefixFailure]
  nlinarith [sq_nonneg (1 - p ^ (k.val + 1))]

/-- A finite weighted second moment is small if its variable vanishes off a rare event. -/
theorem rare_second_moment {Ω : Type*} [Fintype Ω] (w X I : Ω → ℝ) (D s : ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hpoint : ∀ ω, X ω ^ 2 ≤ D ^ 2 * I ω)
    (hrare : ∑ ω, w ω * I ω ≤ s) :
    ∑ ω, w ω * X ω ^ 2 ≤ D ^ 2 * s := by
  calc
    _ ≤ ∑ ω, w ω * (D ^ 2 * I ω) := sum_le_sum fun ω _ =>
      mul_le_mul_of_nonneg_left (hpoint ω) (hw ω)
    _ = D ^ 2 * ∑ ω, w ω * I ω := by rw [mul_sum]; congr 1; funext ω; ring
    _ ≤ D ^ 2 * s := mul_le_mul_of_nonneg_left hrare (sq_nonneg D)

/-- The report lies in `[0,2h]` and hence differs from its noiseless fold by at most `2h`. -/
theorem report_sub_fold_abs_le (a b : Population n) (ω₁ ω₂ : Pattern n) (k : Fin n)
    (h : ℕ) (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) :
    |(twoLegReport a b ω₁ ω₂ k : ℝ) - (a k + b k : ℕ)| ≤ 2 * (h : ℝ) := by
  have hr : twoLegReport a b ω₁ ω₂ k ≤ 2 * h := by
    unfold twoLegReport
    have := legReport_le_bound a ω₁ k.val h ha
    have := legReport_le_bound b ω₂ k.val h hb
    omega
  have hc : a k + b k ≤ 2 * h := by have := ha k; have := hb k; omega
  have hr' : (twoLegReport a b ω₁ ω₂ k : ℝ) ≤ 2 * h := by exact_mod_cast hr
  have hc' : ((a k + b k : ℕ) : ℝ) ≤ 2 * h := by exact_mod_cast hc
  have hr0 : 0 ≤ (twoLegReport a b ω₁ ω₂ k : ℝ) := by positivity
  have hc0 : 0 ≤ ((a k + b k : ℕ) : ℝ) := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Concrete shell-model rare-event second moment, with the depth-dependent factor. -/
theorem fold_centered_second_moment_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Population n) (k : Fin n) (h : ℕ)
    (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) :
    expect p (fun ω₁ ω₂ => ((twoLegReport a b ω₁ ω₂ k : ℝ) -
      (a k + b k : ℕ)) ^ 2) ≤ 2 * (2 * (h : ℝ)) ^ 2 * (1 - p ^ (k.val + 1)) := by
  classical
  have hpt : ∀ ω₁ ω₂,
      ((twoLegReport a b ω₁ ω₂ k : ℝ) - (a k + b k : ℕ)) ^ 2 ≤
        (2 * (h : ℝ)) ^ 2 * prefixFailure k ω₁ ω₂ := by
    intro ω₁ ω₂
    unfold prefixFailure
    split_ifs with hgood
    · rw [twoLegReport_eq_of_prefix_alive a b ω₁ ω₂ k hgood.1 hgood.2]
      simp
    · rw [mul_one]
      exact sq_le_sq.mpr (by simpa using report_sub_fold_abs_le a b ω₁ ω₂ k h ha hb)
  calc
    _ ≤ (2 * (h : ℝ)) ^ 2 * expect p (prefixFailure k) := by
      unfold expect
      rw [mul_sum]
      apply sum_le_sum
      intro ω₁ _
      rw [mul_sum]
      apply sum_le_sum
      intro ω₂ _
      calc
        _ ≤ (patternWeight p ω₁ * patternWeight p ω₂) *
            ((2 * (h : ℝ)) ^ 2 * prefixFailure k ω₁ ω₂) :=
          mul_le_mul_of_nonneg_left (hpt ω₁ ω₂)
            (mul_nonneg (patternWeight_nonneg hp hp1 ω₁) (patternWeight_nonneg hp hp1 ω₂))
        _ = _ := by ring
    _ ≤ (2 * (h : ℝ)) ^ 2 * (2 * (1 - p ^ (k.val + 1))) :=
      mul_le_mul_of_nonneg_left (expect_prefixFailure_le p k) (sq_nonneg _)
    _ = _ := by ring

/-- Variance is bounded by the second moment about any fixed center.
This is a finite-sum identity with normalized weights, not a probability axiom. -/
theorem variance_le_second_moment_about {Ω : Type*} [Fintype Ω]
    (w X : Ω → ℝ) (c : ℝ) (hw : ∑ ω, w ω = 1) :
    (∑ ω, w ω * (X ω - ∑ v, w v * X v) ^ 2) ≤
      ∑ ω, w ω * (X ω - c) ^ 2 := by
  let μ := ∑ ω, w ω * X ω
  have hid : ∀ ω, w ω * (X ω - μ) ^ 2 =
      w ω * (X ω - c) ^ 2 - 2 * (μ - c) * (w ω * X ω) +
        (μ ^ 2 - c ^ 2) * w ω := by intro ω; ring
  change (∑ ω, w ω * (X ω - μ) ^ 2) ≤ _
  simp_rw [hid, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hw, mul_one]
  change _ - 2 * (μ - c) * μ + (μ ^ 2 - c ^ 2) ≤ _
  nlinarith [sq_nonneg (μ - c)]

/-- Mean and covariance estimates do not need separately estimated raw moments. -/
theorem finite_empirical_covariance_identity {Ω : Type*} [Fintype Ω]
    (w X Y : Ω → ℝ) (a b : ℝ) (hw : ∑ ω, w ω = 1) :
    (∑ ω, w ω * (X ω - a) * (Y ω - b)) -
      ((∑ ω, w ω * X ω) - a) * ((∑ ω, w ω * Y ω) - b) =
      (∑ ω, w ω * X ω * Y ω) -
        (∑ ω, w ω * X ω) * (∑ ω, w ω * Y ω) := by
  have hpt : ∀ ω, w ω * (X ω - a) * (Y ω - b) =
      w ω * X ω * Y ω - b * (w ω * X ω) - a * (w ω * Y ω) + a * b * w ω := by
    intro ω; ring
  simp_rw [hpt, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hw]
  ring

/-- Pointwise centered-product bound used to transfer a variance bound to covariance. -/
theorem centered_product_square_le {x y D : ℝ} (hy : |y| ≤ D) :
    (x * y) ^ 2 ≤ D ^ 2 * x ^ 2 := by
  have hD : 0 ≤ D := le_trans (abs_nonneg y) hy
  have hsq : y ^ 2 ≤ D ^ 2 := (sq_le_sq).2 (by simpa [abs_of_nonneg hD] using hy)
  nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg x)]

/-- The mask weights are normalized. -/
theorem expect_one (p : ℝ) : expect p (fun (_ _ : Pattern n) => 1) = 1 := by
  unfold expect
  simp_rw [mul_one, ← mul_sum, sum_patternWeight, mul_one]
  exact sum_patternWeight p

theorem expect_const (p c : ℝ) : expect p (fun (_ _ : Pattern n) => c) = c := by
  unfold expect
  simp_rw [← sum_mul, ← mul_sum, sum_patternWeight]
  simp [sum_patternWeight]

theorem expect_const_mul (p c : ℝ) (f : Pattern n → Pattern n → ℝ) :
    expect p (fun ω₁ ω₂ => c * f ω₁ ω₂) = c * expect p f := by
  unfold expect
  simp_rw [mul_sum]
  apply sum_congr rfl; intro ω₁ _
  apply sum_congr rfl; intro ω₂ _
  ring

theorem expect_mono {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f g : Pattern n → Pattern n → ℝ} (hfg : ∀ ω₁ ω₂, f ω₁ ω₂ ≤ g ω₁ ω₂) :
    expect p f ≤ expect p g := by
  unfold expect
  apply sum_le_sum; intro ω₁ _
  apply sum_le_sum; intro ω₂ _
  exact mul_le_mul_of_nonneg_left (hfg ω₁ ω₂)
    (mul_nonneg (patternWeight_nonneg hp hp1 ω₁) (patternWeight_nonneg hp hp1 ω₂))

/-- Direct variance estimate for the observed shell bin. -/
theorem report_variance_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Population n) (k : Fin n) (h : ℕ)
    (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) :
    expect p (fun ω₁ ω₂ => ((twoLegReport a b ω₁ ω₂ k : ℝ) -
      twoLegMean p a b k) ^ 2) ≤ 2 * (2 * (h : ℝ)) ^ 2 * (1 - p ^ (k.val + 1)) := by
  have hw : (∑ ω : Pattern n × Pattern n, patternWeight p ω.1 * patternWeight p ω.2) = 1 := by
    simpa only [expect, Fintype.sum_prod_type, mul_one] using (expect_one (n := n) p)
  have hv := variance_le_second_moment_about
    (fun ω : Pattern n × Pattern n => patternWeight p ω.1 * patternWeight p ω.2)
    (fun ω : Pattern n × Pattern n => (twoLegReport a b ω.1 ω.2 k : ℝ))
    ((a k + b k : ℕ) : ℝ) hw
  have hv' : expect p (fun ω₁ ω₂ => ((twoLegReport a b ω₁ ω₂ k : ℝ) -
      twoLegMean p a b k) ^ 2) ≤ expect p (fun ω₁ ω₂ =>
      ((twoLegReport a b ω₁ ω₂ k : ℝ) - (a k + b k : ℕ)) ^ 2) := by
    simpa only [expect, twoLegMean, Fintype.sum_prod_type] using hv
  exact hv'.trans (fold_centered_second_moment_le hp hp1 a b k h ha hb)

/-- Centering an observed shell bin at its true mean retains the same range bound. -/
theorem report_sub_mean_abs_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Population n) (k : Fin n) (h : ℕ)
    (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) (ω₁ ω₂ : Pattern n) :
    |(twoLegReport a b ω₁ ω₂ k : ℝ) - twoLegMean p a b k| ≤ 2 * (h : ℝ) := by
  have hr : ∀ ω₁ ω₂, (twoLegReport a b ω₁ ω₂ k : ℝ) ≤ 2 * h := by
    intro ω₁ ω₂
    have h1 := legReport_le_bound a ω₁ k.val h ha
    have h2 := legReport_le_bound b ω₂ k.val h hb
    have : twoLegReport a b ω₁ ω₂ k ≤ 2 * h := by unfold twoLegReport; omega
    exact_mod_cast this
  have hμ0 : 0 ≤ twoLegMean p a b k := by
    have hh := expect_mono hp hp1 (f := fun _ _ => 0)
      (g := fun ω₁ ω₂ => (twoLegReport a b ω₁ ω₂ k : ℝ)) (by intros; positivity)
    rw [expect_const] at hh
    exact hh
  have hμ1 : twoLegMean p a b k ≤ 2 * (h : ℝ) := by
    have hh := expect_mono hp hp1 hr
    rw [expect_const] at hh
    exact hh
  have hr0 : 0 ≤ (twoLegReport a b ω₁ ω₂ k : ℝ) := by positivity
  exact abs_le.mpr ⟨by linarith, by linarith [hr ω₁ ω₂]⟩

/-- Second moment of the true-centered product: the quantity controlling its Bernstein
variance has the shallow-bin rare-event factor, rather than a constant range-only bound. -/
theorem centered_product_second_moment_le {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Population n) (k l : Fin n) (h : ℕ)
    (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) :
    expect p (fun ω₁ ω₂ =>
      (((twoLegReport a b ω₁ ω₂ k : ℝ) - twoLegMean p a b k) *
       ((twoLegReport a b ω₁ ω₂ l : ℝ) - twoLegMean p a b l)) ^ 2) ≤
      2 * (2 * (h : ℝ)) ^ 4 * (1 - p ^ (k.val + 1)) := by
  calc
    _ ≤ expect p (fun ω₁ ω₂ => (2 * (h : ℝ)) ^ 2 *
        ((twoLegReport a b ω₁ ω₂ k : ℝ) - twoLegMean p a b k) ^ 2) := by
      apply expect_mono hp hp1
      intro ω₁ ω₂
      exact centered_product_square_le (report_sub_mean_abs_le hp hp1 a b l h ha hb ω₁ ω₂)
    _ = (2 * (h : ℝ)) ^ 2 * expect p (fun ω₁ ω₂ =>
        ((twoLegReport a b ω₁ ω₂ k : ℝ) - twoLegMean p a b k) ^ 2) :=
      expect_const_mul _ _ _
    _ ≤ (2 * (h : ℝ)) ^ 2 * (2 * (2 * (h : ℝ)) ^ 2 * (1 - p ^ (k.val + 1))) :=
      mul_le_mul_of_nonneg_left (report_variance_le hp hp1 a b k h ha hb) (sq_nonneg _)
    _ = _ := by ring

/-- The empirical covariance identity, independent of how its centering is implemented. -/
theorem empirical_covariance_identity (raw meanK meanM empiricalMeanK empiricalMeanM : ℝ) :
    raw - empiricalMeanK * empiricalMeanM =
    (raw - meanK * empiricalMeanM - meanM * empiricalMeanK + meanK * meanM) -
      (empiricalMeanK - meanK) * (empiricalMeanM - meanM) := by ring

/-- Key new weighted error estimate. The lower-depth tolerance is `t*s/5`.
The other tolerance is at most `t/5`, so the empirical covariance correction costs
at most a further `t*s/25`. The strict half-pivot margin is retained. -/
theorem corrected_covariance_error {t s z e f : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s)
    (hz : |z| ≤ t * s / 5) (he : |e| ≤ t * s / 5) (hf : |f| ≤ t / 5) :
    |2 * (z - e * f)| ≤ (12 / 25 : ℝ) * t * s ∧
      |2 * (z - e * f)| < t * s / 2 := by
  have hts : 0 ≤ t * s := le_of_lt (mul_pos ht hs)
  have hef : |e * f| ≤ t * s / 25 := by
    rw [abs_mul]
    calc
      |e| * |f| ≤ (t * s / 5) * (t / 5) :=
        mul_le_mul he hf (abs_nonneg f) (by positivity)
      _ ≤ t * s / 25 := by nlinarith [mul_le_mul_of_nonneg_left ht1 hts]
  have hmain : |2 * (z - e * f)| ≤ (12 / 25 : ℝ) * t * s := by
    calc
      _ = 2 * |z - e * f| := by rw [abs_mul]; norm_num
      _ ≤ 2 * (|z| + |e * f|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
      _ ≤ (12 / 25 : ℝ) * t * s := by linarith
  exact ⟨hmain, lt_of_le_of_lt hmain (by nlinarith [mul_pos ht hs])⟩

/-- Concrete bridge from centered empirical moments to the corrected covariance used
by the shell decoder. The observations may be arbitrary vectors; on the stated good event
they obey exactly the channel-specific weighted error margin. -/
theorem sample_good_event_to_corrected_covariance
    {Ω : Type*} [Fintype Ω] (w : Ω → ℝ) (R : Ω → Fin n → ℝ)
    (hw : ∑ ω, w ω = 1) (p : ℝ) (a b : Population n) (k l : Fin n)
    {t s : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hs : 0 < s)
    (hz : |(∑ ω, w ω * (R ω k - twoLegMean p a b k) *
      (R ω l - twoLegMean p a b l)) - twoLegCovariance p a b k l| ≤ t * s / 5)
    (he : |(∑ ω, w ω * R ω k) - twoLegMean p a b k| ≤ t * s / 5)
    (hf : |(∑ ω, w ω * R ω l) - twoLegMean p a b l| ≤ t / 5) :
    |(2 * ((∑ ω, w ω * R ω k * R ω l) -
        (∑ ω, w ω * R ω k) * (∑ ω, w ω * R ω l)) -
      Qform p (fun i => (a i : ℝ) + b i) (fun i => (a i : ℝ) + b i) k.val l.val) -
      Qform p (fun i => (a i : ℝ) - b i) (fun i => (a i : ℝ) - b i) k.val l.val| <
        t * s / 2 := by
  have hmargin := (corrected_covariance_error ht ht1 hs hz he hf).2
  have hid := finite_empirical_covariance_identity w (fun ω => R ω k) (fun ω => R ω l)
    (twoLegMean p a b k) (twoLegMean p a b l) hw
  have hpop := imbalanceCovariance_eq p a b k l
  unfold imbalanceCovariance at hpop
  have halgebra :
      (2 * ((∑ ω, w ω * R ω k * R ω l) -
        (∑ ω, w ω * R ω k) * (∑ ω, w ω * R ω l)) -
      Qform p (fun i => (a i : ℝ) + b i) (fun i => (a i : ℝ) + b i) k.val l.val) -
      Qform p (fun i => (a i : ℝ) - b i) (fun i => (a i : ℝ) - b i) k.val l.val =
      2 * (((∑ ω, w ω * (R ω k - twoLegMean p a b k) *
        (R ω l - twoLegMean p a b l)) - twoLegCovariance p a b k l) -
        ((∑ ω, w ω * R ω k) - twoLegMean p a b k) *
        ((∑ ω, w ω * R ω l) - twoLegMean p a b l)) := by
    linarith [hid, hpop]
  rw [halgebra]
  exact hmargin

/-- Perturbing a pivot equation by less than half its pivot preserves its nearest integer. -/
theorem integer_identified_by_half_gap (j k : ℤ) (x : ℝ)
    (hj : |x - (j : ℝ)| < 1 / 2) (hk : |x - (k : ℝ)| ≤ 1 / 2) : j = k := by
  have hdist : |(j : ℝ) - k| < 1 := by
    calc
      _ ≤ |(j : ℝ) - x| + |x - k| := abs_sub_le _ _ _
      _ < 1 := by rw [abs_sub_comm (j : ℝ) x]; linarith
  have hz : |j - k| < 1 := by exact_mod_cast hdist
  have hz2 := abs_lt.mp hz
  have : j - k = 0 := by omega
  omega

/-- A positive pivot turns a scaled observation error into a half-integer rounding margin. -/
theorem pivot_rounding_margin {estimate truth pivot noise : ℝ}
    (hp : 0 < pivot) (heq : estimate - truth = noise / pivot)
    (herr : |noise| < pivot / 2) : |estimate - truth| < 1 / 2 := by
  rw [heq, abs_div, abs_of_pos hp]
  exact (div_lt_iff₀ hp).2 (by linarith)

/-- Variable diagonal thresholds detect the deepest nonzero imbalance exactly.
No error assumption is needed on shallower entries: choosing the greatest crossing
makes their behavior irrelevant. -/
theorem deepest_threshold {ι : Type*} [LinearOrder ι] (q est scale : ι → ℝ) (m : ι)
    (_hscale : ∀ k, 0 < scale k) (herr : ∀ k, |est k - q k| < scale k / 2)
    (hbeyond : ∀ k, m < k → q k = 0) (htop : scale m ≤ q m) :
    scale m / 2 < est m ∧ ∀ k, m < k → est k < scale k / 2 := by
  constructor
  · have := (abs_lt.mp (herr m)).1; linarith
  · intro k hk
    have := (abs_lt.mp (herr k)).2
    rw [hbeyond k hk] at this
    linarith

/-- If the imbalance is identically zero, no variable threshold is crossed. -/
theorem zero_threshold {ι : Type*} (est scale : ι → ℝ)
    (herr : ∀ k, |est k| < scale k / 2) : ∀ k, est k < scale k / 2 := by
  intro k; exact (abs_lt.mp (herr k)).2

end ShellResearch
