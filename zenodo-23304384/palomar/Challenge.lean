module
public import Mathlib

/-!
# Lossy distance-shell tomography on paths

Lennart Rudolph, *Lossy Distance-Shell Tomography on Paths: Recovery from Mean
and Covariance*, DOI: 10.5281/zenodo.23252713. Version 2.0.0 source record:
https://zenodo.org/records/23304384.

An interior sensor observes sums of anonymous counts on its two legs. A failed
relay is bypassed and its own targets are silent. Every relay independently
survives with known probability `p`. Unlike the noiseless folded counts, the
report covariance reveals the spatial dependence induced by shared prefixes.

The independent Challenge states ten endpoints using concrete finite mask sums.
The main full and sparse recovery theorems allow empty legs, zeros, and arbitrary
natural multiplicities, and recover only up to global exchange of the two legs.
Supporting variance, deterministic rounding and randomized-testing results are
selected with their exact hypotheses. They do not assert the manuscript's full
finite-sample probability guarantee, unknown-rate calibration, general-tree
results, spider obstruction, or imported trace-complexity bounds.
-/
@[expose] public section

namespace LossyShell

/-- A population on a leg of `n` relays: `x i` targets sit on the relay at true hop distance
`i + 1` from the sensor. -/
abbrev Population (n : ℕ) := Fin n → ℕ

/-- A failure pattern: `ω i = true` exactly when the relay at true hop distance `i + 1` survives
the round. -/
abbrev Pattern (n : ℕ) := Fin n → Bool

/-- The number of surviving relays whose true hop distance is at most `i + 1`. When relay `i`
survives, this is its hop distance from the sensor after failed relays are bypassed. -/
def aliveRank {n : ℕ} (ω : Pattern n) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => j ≤ i ∧ ω j = true).card

/-- The number of surviving relays on the leg (the sensor's current horizon). -/
def aliveCount {n : ℕ} (ω : Pattern n) : ℕ :=
  (Finset.univ.filter fun j : Fin n => ω j = true).card

/-- The hop-count report contributed by one leg: entry `k` counts the targets that sit on
surviving relays at hop distance `k + 1`. Targets on failed relays are silent. -/
def legReport {n : ℕ} (x : Population n) (ω : Pattern n) (k : ℕ) : ℕ :=
  ∑ i, if ω i = true ∧ aliveRank ω i = k + 1 then x i else 0

/-- The probability of a failure pattern when every relay survives independently with
probability `p`. -/
def patternWeight {K : Type*} [CommRing K] {n : ℕ} (p : K) (ω : Pattern n) : K :=
  ∏ i, if ω i = true then p else 1 - p

/-- The deletion-channel trace of a population: the counts on surviving relays, in order. -/
def trace {n : ℕ} (x : Population n) (ω : Pattern n) : List ℕ :=
  ((List.finRange n).filter fun i => ω i).map x

/-- The report of an interior sensor whose two legs carry the populations `a` and `b`, with
failure patterns `ω₁` and `ω₂` on the two legs. Entry `k` counts targets at hop distance
`k + 1` on either side. -/
def twoLegReport {n : ℕ} (a b : Population n) (ω₁ ω₂ : Pattern n) (k : Fin n) : ℕ :=
  legReport a ω₁ k.val + legReport b ω₂ k.val

/-- The law of the interior sensor's lossy report: the probability that the report equals `h`
when every relay on both legs survives independently with probability `p`. -/
def twoLegLaw {K : Type*} [CommRing K] {n : ℕ} (p : K) (a b : Population n)
    (h : Fin n → ℕ) : K :=
  ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n,
    if twoLegReport a b ω₁ ω₂ = h then patternWeight p ω₁ * patternWeight p ω₂ else 0

/-- The mean of entry `k` of the interior sensor's lossy report. -/
def twoLegMean {K : Type*} [CommRing K] {n : ℕ} (p : K) (a b : Population n) (k : Fin n) : K :=
  ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n,
    patternWeight p ω₁ * patternWeight p ω₂ * (twoLegReport a b ω₁ ω₂ k : K)

/-- The mixed second moment of entries `k` and `l` of the interior sensor's lossy report. -/
def twoLegSecondMoment {K : Type*} [CommRing K] {n : ℕ} (p : K) (a b : Population n)
    (k l : Fin n) : K :=
  ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n,
    patternWeight p ω₁ * patternWeight p ω₂ *
      ((twoLegReport a b ω₁ ω₂ k : K) * (twoLegReport a b ω₁ ω₂ l : K))

/-- The covariance of report entries `k` and `l`: their mixed second moment minus the product
of their means. This is the covariance of the observed two-leg report, including both legs. -/
def twoLegCovariance {K : Type*} [CommRing K] {n : ℕ} (p : K) (a b : Population n)
    (k l : Fin n) : K :=
  twoLegSecondMoment p a b k l - twoLegMean p a b k * twoLegMean p a b l


variable {n : ℕ} {K : Type*} [CommRing K]

def landProb (p : K) (i : Fin n) (k : ℕ) : K :=
  ∑ ω : Pattern n, if ω i = true ∧ aliveRank ω i = k + 1 then patternWeight p ω else 0

def pairProb (p : K) (i j : Fin n) (k l : ℕ) : K :=
  ∑ ω : Pattern n,
    if (ω i = true ∧ aliveRank ω i = k + 1) ∧ (ω j = true ∧ aliveRank ω j = l + 1) then
      patternWeight p ω else 0

def Qform (p : K) (u v : Fin n → K) (k l : ℕ) : K :=
  ∑ i, ∑ j, u i * v j * (pairProb p i j k l - landProb p i k * landProb p j l)

def imbalanceCovariance (p : K) (a b : Population n) (k l : Fin n) : K :=
  2 * twoLegCovariance p a b k l -
    Qform p (fun i => (a i : K) + b i) (fun i => (a i : K) + b i) k.val l.val

end LossyShell

namespace ShellResearch
open LossyShell
variable {n : ℕ}

noncomputable def expect (p : ℝ) (f : Pattern n → Pattern n → ℝ) : ℝ :=
  ∑ ω₁, ∑ ω₂, patternWeight p ω₁ * patternWeight p ω₂ * f ω₁ ω₂

end ShellResearch

namespace ShellSampling
open LossyShell

def iidWeight {Ω : Type*} (P : Ω → ℝ) (N : ℕ) (w : Fin N → Ω) : ℝ :=
  ∏ i, P (w i)

noncomputable def designedRate (n : ℕ) : ℝ :=
  (((2 : ℕ) : ℝ) * (n : ℝ)) / (((2 : ℕ) : ℝ) * (n : ℝ) + 1)

/-- The same-side binary candidate: one target at each of depths one and two. -/
def nearPair (n : ℕ) : Population n := fun i => if i.val < 2 then 1 else 0

/-- First leg of the split-side candidate. -/
def nearLeft (n : ℕ) : Population n := fun i => if i.val = 0 then 1 else 0

/-- Second leg of the split-side candidate. -/
def nearRight (n : ℕ) : Population n := fun i => if i.val = 1 then 1 else 0

abbrev MaskPair (n : ℕ) := Pattern n × Pattern n

def roundWeight {n : ℕ} (p : ℝ) (w : MaskPair n) : ℝ :=
  patternWeight p w.1 * patternWeight p w.2

def longReportA (n : ℕ) (w : MaskPair n) : Fin n → ℕ :=
  twoLegReport (nearPair n) 0 w.1 w.2

def longReportB (n : ℕ) (w : MaskPair n) : Fin n → ℕ :=
  twoLegReport (nearLeft n) (nearRight n) w.1 w.2

end ShellSampling

namespace PalomarResults.LossyShell
open _root_.LossyShell ShellResearch ShellSampling Finset
variable {n : ℕ}

/-- An endpoint report is the deletion trace padded by zeros; knowing the surviving horizon recovers the trace, including silent relays. -/
theorem endpoint_trace_equivalence (x : Population n) (ω : Pattern n) :
    (∀ k, legReport x ω k = (trace x ω).getD k 0) ∧
    trace x ω = (List.range (aliveCount ω)).map (legReport x ω) := by
  sorry

/-- At zero survival every report is zero; at full survival only the fold is visible. These endpoints explain the open-interval hypothesis of recovery. -/
theorem probability_endpoints (a b : Population n) (h : Fin n → ℕ) :
    twoLegLaw (0 : ℝ) a b h = (if 0 = h then 1 else 0) ∧
    twoLegLaw (1 : ℝ) a b h = (if a + b = h then 1 else 0) := by
  sorry

/-- The mean preserves exactly the noiseless folded information. This is the two-leg specialization of the manuscript tree statement. -/
theorem mean_eq_iff_fold_eq {p : ℝ} (hp : 0 < p) {a b a' b' : Population n} :
    twoLegMean p a b = twoLegMean p a' b' ↔ a + b = a' + b' := by
  sorry

/-- The central recovery theorem: finite expectations of the actual lossy report identify the two integer populations up to exchange. -/
theorem legs_eq_of_mean_covariance {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hcov : twoLegCovariance p a b = twoLegCovariance p a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  sorry

/-- Only the covariance diagonal and the column at the last nonzero corrected diagonal are needed; the fold correction is computed from the recovered mean. -/
theorem legs_eq_of_mean_covariance_sparse {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hdiag : ∀ k : Fin n, twoLegCovariance p a b k k = twoLegCovariance p a' b' k k)
    (hcol : ∀ m : Fin n, imbalanceCovariance p a b m m ≠ 0 →
      (∀ j : Fin n, m < j → imbalanceCovariance p a b j j = 0) →
      ∀ k : Fin n, k < m → twoLegCovariance p a b k m = twoLegCovariance p a' b' k m) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  sorry

/-- The complete report law has precisely the unavoidable global exchange ambiguity, for every survival probability strictly between zero and one. -/
theorem twoLegLaw_eq_iff {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n} :
    twoLegLaw p a b = twoLegLaw p a' b' ↔
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  sorry

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
  sorry

/-- Descending nearest-integer mean reconstruction is exact under the stated entrywise errors; the algorithm uses actual channel landing coefficients. -/
theorem fold_recovery {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (a b : Population n) (cHat : Fin n → ℤ) (μhat : Fin n → ℝ)
    (haccurate : ∀ k, |μhat k - twoLegMean p a b k| ≤ p ^ n * (1 - p ^ (k.val + 1)) / 5)
    (hrounded : ∀ k,
      |(μhat k - ∑ i ∈ univ.filter (fun i => k < i), (cHat i : ℝ) * landProb p i k.val) /
        p ^ (k.val + 1) - (cHat k : ℝ)| ≤ 1 / 2) :
    cHat = fun i => ((a i + b i : ℕ) : ℤ) := by
  sorry

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
  sorry

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
  sorry

end PalomarResults.LossyShell
