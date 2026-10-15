module
public import LossyShell
public import ShellResearch
public import ShellSampling

/-!
# Lossy distance-shell tomography on paths

Lennart Rudolph, *Lossy Distance-Shell Tomography on Paths: Recovery from Mean
and Covariance*, DOI: 10.5281/zenodo.23252713. Version 2.0.0 source record:
https://zenodo.org/records/23304384.

An interior sensor observes sums of anonymous counts on its two legs. A failed
relay is bypassed and its own targets are silent. Every relay independently
survives with known probability `p`. Unlike the noiseless folded counts, the
report covariance reveals the spatial dependence induced by shared prefixes.

The ten proved interfaces below apply the included substantive proof library.
The main full and sparse recovery theorems allow empty legs, zeros, and arbitrary
natural multiplicities, and recover only up to global exchange of the two legs.
Supporting variance, deterministic rounding and randomized-testing results are
selected with their exact hypotheses. They do not assert the manuscript's full
finite-sample probability guarantee, unknown-rate calibration, general-tree
results, spider obstruction, or imported trace-complexity bounds.
-/
@[expose] public section

namespace PalomarResults.LossyShell
open _root_.LossyShell ShellResearch ShellSampling Finset
variable {n : ℕ}

/-- An endpoint report is the deletion trace padded by zeros; knowing the surviving horizon recovers the trace, including silent relays. -/
theorem endpoint_trace_equivalence (x : Population n) (ω : Pattern n) :
    (∀ k, legReport x ω k = (trace x ω).getD k 0) ∧
    trace x ω = (List.range (aliveCount ω)).map (legReport x ω) := by
  exact ⟨fun k => _root_.LossyShell.legReport_eq_trace_getD x ω k,
    _root_.LossyShell.trace_eq_map_legReport x ω⟩

/-- At zero survival every report is zero; at full survival only the fold is visible. These endpoints explain the open-interval hypothesis of recovery. -/
theorem probability_endpoints (a b : Population n) (h : Fin n → ℕ) :
    twoLegLaw (0 : ℝ) a b h = (if 0 = h then 1 else 0) ∧
    twoLegLaw (1 : ℝ) a b h = (if a + b = h then 1 else 0) := by
  exact ⟨_root_.LossyShell.twoLegLaw_zero a b h, _root_.LossyShell.twoLegLaw_one a b h⟩

/-- The mean preserves exactly the noiseless folded information. This is the two-leg specialization of the manuscript tree statement. -/
theorem mean_eq_iff_fold_eq {p : ℝ} (hp : 0 < p) {a b a' b' : Population n} :
    twoLegMean p a b = twoLegMean p a' b' ↔ a + b = a' + b' := by
  exact ⟨_root_.LossyShell.fold_eq_of_twoLegMean_eq hp,
    _root_.LossyShell.twoLegMean_eq_of_fold_eq p⟩

/-- The central recovery theorem: finite expectations of the actual lossy report identify the two integer populations up to exchange. -/
theorem legs_eq_of_mean_covariance {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hcov : twoLegCovariance p a b = twoLegCovariance p a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  exact _root_.LossyShell.legs_eq_of_mean_covariance hp0 hp1 hmean hcov

/-- Only the covariance diagonal and the column at the last nonzero corrected diagonal are needed; the fold correction is computed from the recovered mean. -/
theorem legs_eq_of_mean_covariance_sparse {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hdiag : ∀ k : Fin n, twoLegCovariance p a b k k = twoLegCovariance p a' b' k k)
    (hcol : ∀ m : Fin n, imbalanceCovariance p a b m m ≠ 0 →
      (∀ j : Fin n, m < j → imbalanceCovariance p a b j j = 0) →
      ∀ k : Fin n, k < m → twoLegCovariance p a b k m = twoLegCovariance p a' b' k m) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  exact _root_.LossyShell.legs_eq_of_mean_covariance_sparse hp0 hp1 hmean hdiag hcol

/-- The complete report law has precisely the unavoidable global exchange ambiguity, for every survival probability strictly between zero and one. -/
theorem twoLegLaw_eq_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n} :
    twoLegLaw p a b = twoLegLaw p a' b' ↔
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  exact _root_.LossyShell.twoLegLaw_eq_iff hp0 hp1

/-- Variance and centered-product second moments retain a depth-dependent failure factor; these are components of the sample analysis, without a concentration-probability claim. -/
theorem variance_sensitive_bounds {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (a b : Population n) (k l : Fin n) (h : ℕ)
    (ha : ∀ i, a i ≤ h) (hb : ∀ i, b i ≤ h) :
    (expect p (fun ω₁ ω₂ => ((twoLegReport a b ω₁ ω₂ k : ℝ) -
      twoLegMean p a b k) ^ 2) ≤ 2 * (2 * (h : ℝ)) ^ 2 * (1 - p ^ (k.val + 1))) ∧
    (expect p (fun ω₁ ω₂ =>
      (((twoLegReport a b ω₁ ω₂ k : ℝ) - twoLegMean p a b k) *
       ((twoLegReport a b ω₁ ω₂ l : ℝ) - twoLegMean p a b l)) ^ 2) ≤
      2 * (2 * (h : ℝ)) ^ 4 * (1 - p ^ (k.val + 1))) := by
  exact ⟨ShellResearch.report_variance_le hp hp1 a b k h ha hb,
    ShellResearch.centered_product_second_moment_le hp hp1 a b k l h ha hb⟩

/-- Descending nearest-integer mean reconstruction is exact under the stated entrywise errors; the algorithm uses actual channel landing coefficients. -/
theorem fold_recovery {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : Population n) (cHat : Fin n → ℤ) (μhat : Fin n → ℝ)
    (haccurate : ∀ k, |μhat k - twoLegMean p a b k| ≤ p ^ n * (1 - p ^ (k.val + 1)) / 5)
    (hrounded : ∀ k,
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (cHat i : ℝ) * landProb p i k.val) /
        p ^ (k.val + 1) - (cHat k : ℝ)| ≤ 1 / 2) :
    cHat = fun i => ((a i + b i : ℕ) : ℤ) := by
  exact ShellResearch.fold_recovery hp hp1 a b cHat μhat haccurate hrounded

/-- The oriented difference recurrence is exact under column errors, conditional on the correctly identified deepest entry and its magnitude. -/
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
  exact ShellResearch.difference_recovery hp hp1 d z m column hm htop hzm hztop haccurate hrounded

/-- Every randomized test on the actual length-n reports at p = 2n/(2n+1), with both error probabilities at most δ, requires at least (n/2) log(1/(2δ)) rounds. The coefficient is half the paper's sharper bound. -/
theorem all_length_designed_lower_bound (n : ℕ) (hn : 2 ≤ n) {δ : ℝ}
    (N : ℕ) (test : (Fin N → Fin n → ℕ) → ℝ)
    (ht0 : ∀ y, 0 ≤ test y) (ht1 : ∀ y, test y ≤ 1)
    (hA : (∑ w : Fin N → MaskPair n,
      iidWeight (roundWeight (designedRate n)) N w *
        test (fun i => longReportA n (w i))) ≤ δ)
    (hB : (∑ w : Fin N → MaskPair n,
      iidWeight (roundWeight (designedRate n)) N w *
        (1-test (fun i => longReportB n (w i)))) ≤ δ) :
    ((n:ℝ)/2)*Real.log (1/(2*δ)) ≤ (N:ℝ) := by
  exact ShellSampling.all_length_designed_lower_bound n hn N test ht0 ht1 hA hB

end PalomarResults.LossyShell
