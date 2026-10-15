module

public import LossyShell.Main
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A concrete testing lower bound for two populations in the actual relay-deletion model.
The finite laws are derived from all sixteen relay masks. Tests may be randomized. -/
@[expose] public section

namespace ShellSampling
open Finset LossyShell

abbrev Outcome := Fin 5

def reportOf : Outcome → Fin 2 → ℕ :=
  ![![0, 0], ![1, 0], ![2, 0], ![0, 1], ![1, 1]]

def hardLawA (p : ℝ) (o : Outcome) : ℝ :=
  twoLegLaw p (![1, 1] : Population 2) ![0, 0] (reportOf o)

def hardLawB (p : ℝ) (o : Outcome) : ℝ :=
  twoLegLaw p (![1, 0] : Population 2) ![0, 1] (reportOf o)

private theorem patterns_two : (univ : Finset (Pattern 2)) =
    {![false, false], ![false, true], ![true, false], ![true, true]} := by decide

private theorem univ_two : (univ : Finset (Fin 2)) = {0, 1} := by decide

/-- These five reports include every report of either concrete population. -/
theorem hard_reports_supported :
    (∀ a b : Pattern 2, ∃ o : Outcome,
      twoLegReport (![1, 1] : Population 2) ![0, 0] a b = reportOf o) ∧
    (∀ a b : Pattern 2, ∃ o : Outcome,
      twoLegReport (![1, 0] : Population 2) ![0, 1] a b = reportOf o) := by decide

/-- Exact probabilities, calculated from the deletion masks rather than assumed. -/
theorem hardLawA_exact (p : ℝ) : hardLawA p =
    ![(1-p)^2, 2*p*(1-p), 0, 0, p^2] := by
  funext o
  fin_cases o <;>
    simp [hardLawA, twoLegLaw, patterns_two, twoLegReport, legReport,
      aliveRank, univ_two, patternWeight, reportOf, funext_iff, Finset.filter_insert, Finset.filter_singleton] <;> ring

/-- Exact probabilities for the second population. -/
theorem hardLawB_exact (p : ℝ) : hardLawB p =
    ![(1-p)^2, p*(1-p)*(2-p), p^2*(1-p), p^2*(1-p), p^3] := by
  funext o
  fin_cases o <;>
    simp [hardLawB, twoLegLaw, patterns_two, twoLegReport, legReport,
      aliveRank, univ_two, patternWeight, reportOf, funext_iff, Finset.filter_insert, Finset.filter_singleton] <;> ring

/-- Pointwise common subdistribution. -/
def hardCommon (p : ℝ) : Outcome → ℝ :=
  ![(1-p)^2, p*(1-p)*(2-p), 0, 0, p^3]

theorem hardCommon_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o : Outcome) :
    0 ≤ hardCommon p o := by
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have h2 : 0 ≤ 2-p := by linarith
  fin_cases o <;> simp [hardCommon] <;> positivity

theorem hardCommon_le_A {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o : Outcome) :
    hardCommon p o ≤ hardLawA p o := by
  rw [hardLawA_exact]
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hprod : 0 ≤ p^2*(1-p) := mul_nonneg (sq_nonneg p) hq
  fin_cases o <;> simp [hardCommon] <;> nlinarith

theorem hardCommon_le_B {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o : Outcome) :
    hardCommon p o ≤ hardLawB p o := by
  rw [hardLawB_exact]
  have hq : 0 ≤ 1-p := sub_nonneg.mpr hp1
  fin_cases o <;> simp [hardCommon] <;> positivity

theorem hardCommon_mass (p : ℝ) :
    ∑ o, hardCommon p o = 1 - 2*p^2*(1-p) := by
  simp [hardCommon, Fin.sum_univ_succ]
  ring


/-- The report coding loses no information. -/
theorem reportOf_injective : Function.Injective reportOf := by decide

theorem hardLawA_sum (p : ℝ) : ∑ o, hardLawA p o = 1 := by
  rw [hardLawA_exact]
  simp [Fin.sum_univ_succ]
  ring

theorem hardLawB_sum (p : ℝ) : ∑ o, hardLawB p o = 1 := by
  rw [hardLawB_exact]
  simp [Fin.sum_univ_succ]
  ring

theorem hardLawA_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o : Outcome) :
    0 ≤ hardLawA p o :=
  le_trans (hardCommon_nonneg hp0 hp1 o) (hardCommon_le_A hp0 hp1 o)

theorem hardLawB_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (o : Outcome) :
    0 ≤ hardLawB p o :=
  le_trans (hardCommon_nonneg hp0 hp1 o) (hardCommon_le_B hp0 hp1 o)

/-- Half the ℓ¹ difference is the exact one-round total variation distance. -/
theorem hard_pair_total_variation {p : ℝ} (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (∑ o, |hardLawA p o - hardLawB p o|) / 2 = 2*p^2*(1-p) := by
  have hq : 0 ≤ p^2*(1-p) := mul_nonneg (sq_nonneg p) (sub_nonneg.mpr hp1)
  have hd : (fun o => hardLawA p o - hardLawB p o) =
      ![0, p^2*(1-p), -(p^2*(1-p)), -(p^2*(1-p)), p^2*(1-p)] := by
    funext o
    rw [hardLawA_exact, hardLawB_exact]
    fin_cases o <;> simp <;> ring
  change (∑ o, |(fun o => hardLawA p o - hardLawB p o) o|) / 2 = _
  rw [hd]
  simp [Fin.sum_univ_succ, abs_of_nonneg hq, abs_neg]
  ring

/-- Product weights for N independent rounds. -/
def iidWeight {Ω : Type*} (P : Ω → ℝ) (N : ℕ) (w : Fin N → Ω) : ℝ :=
  ∏ i, P (w i)

/-- Generic common-subdistribution bound, including arbitrary randomized tests.
`test w` is the probability of answering B. -/
theorem testing_common_bound {Ω : Type*} [Fintype Ω]
    (P Q C : Ω → ℝ) (hC : ∀ x, 0 ≤ C x)
    (hCP : ∀ x, C x ≤ P x) (hCQ : ∀ x, C x ≤ Q x)
    (N : ℕ) (test : (Fin N → Ω) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1) :
    (∑ x, C x)^N ≤
      (∑ w, iidWeight P N w * test w) +
      (∑ w, iidWeight Q N w * (1-test w)) := by
  have hprodP (w : Fin N → Ω) : iidWeight C N w ≤ iidWeight P N w := by
    exact Finset.prod_le_prod₀ (fun i _ => hC (w i)) (fun i _ => hCP (w i))
  have hprodQ (w : Fin N → Ω) : iidWeight C N w ≤ iidWeight Q N w := by
    exact Finset.prod_le_prod₀ (fun i _ => hC (w i)) (fun i _ => hCQ (w i))
  have hmass : (∑ w : Fin N → Ω, iidWeight C N w) = (∑ x, C x)^N := by
    unfold iidWeight
    rw [← Fintype.prod_sum]
    simp
  rw [← hmass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have h1 := mul_le_mul_of_nonneg_right (hprodP w) (ht0 w)
  have h2 := mul_le_mul_of_nonneg_right (hprodQ w) (sub_nonneg.mpr (ht1 w))
  nlinarith

/-- Any randomized decision rule incurs this sum of the two error probabilities. -/
theorem hard_pair_testing_lower_bound {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1) :
    (1 - 2*p^2*(1-p))^N ≤
      (∑ w, iidWeight (hardLawA p) N w * test w) +
      (∑ w, iidWeight (hardLawB p) N w * (1-test w)) := by
  rw [← hardCommon_mass]
  exact testing_common_bound _ _ _ (hardCommon_nonneg hp0 hp1)
    (hardCommon_le_A hp0 hp1) (hardCommon_le_B hp0 hp1) N test ht0 ht1

/-- Uniform error at most δ on the two populations forces this exact necessary condition. -/
theorem hard_pair_required_common_mass {p δ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1)
    (hA : (∑ w, iidWeight (hardLawA p) N w * test w) ≤ δ)
    (hB : (∑ w, iidWeight (hardLawB p) N w * (1-test w)) ≤ δ) :
    (1 - 2*p^2*(1-p))^N ≤ 2*δ := by
  have h := hard_pair_testing_lower_bound hp0 hp1 N test ht0 ht1
  linarith

/-- At least one of the two populations has this much probability of error. -/
theorem hard_pair_max_error {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1) :
    (1 - 2*p^2*(1-p))^N / 2 ≤
      max (∑ w, iidWeight (hardLawA p) N w * test w)
          (∑ w, iidWeight (hardLawB p) N w * (1-test w)) := by
  have h := hard_pair_testing_lower_bound hp0 hp1 N test ht0 ht1
  have hA := le_max_left (∑ w, iidWeight (hardLawA p) N w * test w)
    (∑ w, iidWeight (hardLawB p) N w * (1-test w))
  have hB := le_max_right (∑ w, iidWeight (hardLawA p) N w * test w)
    (∑ w, iidWeight (hardLawB p) N w * (1-test w))
  linarith

/-- The common mass is uniformly bounded away from zero. -/
theorem hardCommon_mass_ge {p : ℝ} (hp0 : 0 ≤ p) :
    (19:ℝ)/27 ≤ 1 - 2*p^2*(1-p) := by
  have h := mul_nonneg (sq_nonneg (3*p-2)) (show 0 ≤ 3*p+1 by linarith)
  nlinarith

/-- Exact necessary round count, with its logarithmic confidence dependence. -/
theorem hard_pair_log_round_lower_bound {p δ : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1)
    (hA : (∑ w, iidWeight (hardLawA p) N w * test w) ≤ δ)
    (hB : (∑ w, iidWeight (hardLawB p) N w * (1-test w)) ≤ δ) :
    Real.log (1/(2*δ)) / (-Real.log (1-2*p^2*(1-p))) ≤ (N:ℝ) := by
  have hcpos : 0 < 1-2*p^2*(1-p) := by
    have := hardCommon_mass_ge hp0.le
    linarith
  have hclt : 1-2*p^2*(1-p) < 1 := by
    have : 0 < 2*p^2*(1-p) := by positivity
    linarith
  have hlog := Real.log_le_log (pow_pos hcpos N)
    (hard_pair_required_common_mass hp0.le hp1.le N test ht0 ht1 hA hB)
  rw [Real.log_pow] at hlog
  rw [div_le_iff₀ (neg_pos.mpr (Real.log_neg hcpos hclt)), one_div, Real.log_inv]
  nlinarith

/-- A simpler necessary bound exposing the inverse failure-rate scale. -/
theorem hard_pair_inverse_failure_lower_bound {p δ : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1)
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1)
    (hA : (∑ w, iidWeight (hardLawA p) N w * test w) ≤ δ)
    (hB : (∑ w, iidWeight (hardLawB p) N w * (1-test w)) ≤ δ) :
    Real.log (1/(2*δ)) / (4*(1-p)) ≤ (N:ℝ) := by
  let c := 1-2*p^2*(1-p)
  have hc : (1:ℝ)/2 ≤ c := by
    have := hardCommon_mass_ge hp0.le
    dsimp [c]
    linarith
  have hcpos : 0 < c := by linarith
  have hlog := Real.log_le_log (pow_pos hcpos N)
    (hard_pair_required_common_mass hp0.le hp1.le N test ht0 ht1 hA hB)
  rw [Real.log_pow] at hlog
  have hinv := Real.one_sub_inv_le_log_of_pos hcpos
  have hp2 : p^2 ≤ 1 := by nlinarith
  have htv : 2*p^2*(1-p) ≤ 2*(1-p) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp2) (sub_nonneg.mpr hp1.le)]
  have hinvbound : c⁻¹ - 1 ≤ 4*(1-p) := by
    apply (le_of_mul_le_mul_right ?_ hcpos)
    rw [sub_mul, inv_mul_cancel₀ (ne_of_gt hcpos), one_mul]
    have := mul_le_mul_of_nonneg_left hc (show 0 ≤ 4*(1-p) by positivity)
    dsimp [c] at *
    nlinarith
  have hneglog : -Real.log c ≤ 4*(1-p) := by linarith
  have hscale := mul_le_mul_of_nonneg_left hneglog (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  rw [div_le_iff₀ (show 0 < 4*(1-p) by positivity), one_div, Real.log_inv]
  change (N:ℝ) * Real.log c ≤ Real.log (2*δ) at hlog
  nlinarith

/-- Rational survival rate used by the linear-round design. -/
noncomputable def designedRate (n : ℕ) : ℝ :=
  (((2 : ℕ) : ℝ) * (n : ℝ)) / (((2 : ℕ) : ℝ) * (n : ℝ) + 1)

/-- At the designed survival rate, uniform δ error needs at least
`n * log (1/(2δ))` rounds, with no asymptotic constants. -/
theorem hard_pair_designed_lower_bound (n : ℕ) (hn : 0 < n) {δ : ℝ}
    (N : ℕ) (test : (Fin N → Outcome) → ℝ)
    (ht0 : ∀ w, 0 ≤ test w) (ht1 : ∀ w, test w ≤ 1)
    (hA : (∑ w, iidWeight (hardLawA (designedRate n)) N w * test w) ≤ δ)
    (hB : (∑ w, iidWeight (hardLawB (designedRate n)) N w * (1-test w)) ≤ δ) :
    (n:ℝ)*Real.log (1/(2*δ)) ≤ (N:ℝ) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnR
  let p := designedRate n
  let c := 1-2*p^2*(1-p)
  have hp0 : 0 < p := by dsimp [p, designedRate]; positivity
  have hp1 : p < 1 := by
    dsimp [p, designedRate]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hcpos : 0 < c := by
    have := hardCommon_mass_ge hp0.le
    dsimp [c]
    linarith
  have hcp : p^2 ≤ c := by
    have h := mul_nonneg (sq_nonneg (1-p)) (show 0 ≤ 1+2*p by linarith)
    dsimp [c]
    nlinarith
  have hlogcp := Real.log_le_log (pow_pos hp0 2) hcp
  rw [Real.log_pow] at hlogcp
  norm_num at hlogcp
  have hlogp := Real.log_le_sub_one_of_pos (inv_pos.mpr hp0)
  rw [Real.log_inv] at hlogp
  have hinv : p⁻¹-1 = 1/(2*(n:ℝ)) := by
    dsimp [p, designedRate]
    rw [inv_div]
    field_simp
    ring
  rw [hinv] at hlogp
  have hratio : (2:ℝ)*(1/(2*(n:ℝ))) = 1/(n:ℝ) := by field_simp
  have hlogc : -Real.log c ≤ 1/(n:ℝ) := by nlinarith
  have hlog := Real.log_le_log (pow_pos hcpos N)
    (hard_pair_required_common_mass hp0.le hp1.le N test ht0 ht1 hA hB)
  rw [Real.log_pow] at hlog
  change (N:ℝ)*Real.log c ≤ Real.log (2*δ) at hlog
  have hmul := mul_le_mul_of_nonneg_left hlogc (Nat.cast_nonneg N : (0:ℝ) ≤ N)
  have hbound : -Real.log (2*δ) ≤ (N:ℝ)/(n:ℝ) := by
    calc -Real.log (2*δ) ≤ (N:ℝ)*(-Real.log c) := by nlinarith [hlog]
         _ ≤ (N:ℝ)*(1/(n:ℝ)) := hmul
         _ = (N:ℝ)/(n:ℝ) := by ring
  have hfinal := (le_div_iff₀ hnR).mp hbound
  rw [one_div, Real.log_inv]
  nlinarith

end ShellSampling
