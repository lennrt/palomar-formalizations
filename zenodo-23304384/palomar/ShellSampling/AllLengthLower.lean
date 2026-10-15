module

public import ShellSampling.LowerBound
public import ShellResearch.FiniteSample

/-! A lower bound for actual length-n populations, without an unformalized padding step.
The same mask experiment couples two distinct binary populations. Four surviving initial
relays force their complete reports to coincide. Independent repetition and arbitrary
randomized tests then give the common-event bound. -/
@[expose] public section

namespace ShellSampling
open Finset LossyShell

/-- A generic common-event lower bound for deterministic observations of a finite experiment.
The test may use all N observations jointly and may randomize. -/
theorem common_event_testing_lower_bound {Ω Y : Type*} [Fintype Ω]
    (W : Ω → ℝ) (hW : ∀ x, 0 ≤ W x) (F G : Ω → Y)
    (E : Ω → Prop) [DecidablePred E] (hFG : ∀ x, E x → F x = G x)
    (N : ℕ) (test : (Fin N → Y) → ℝ)
    (ht0 : ∀ y, 0 ≤ test y) (ht1 : ∀ y, test y ≤ 1) :
    (∑ x, if E x then W x else 0)^N ≤
      (∑ w : Fin N → Ω, iidWeight W N w * test (fun i => F (w i))) +
      (∑ w : Fin N → Ω, iidWeight W N w * (1-test (fun i => G (w i)))) := by
  classical
  let C : Ω → ℝ := fun x => if E x then W x else 0
  have hmass : (∑ w : Fin N → Ω, iidWeight C N w) = (∑ x, C x)^N := by
    unfold iidWeight
    rw [← Fintype.prod_sum]
    simp
  change (∑ x, C x)^N ≤ _
  rw [← hmass, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w _
  have hprod : iidWeight C N w = if ∀ i, E (w i) then iidWeight W N w else 0 := by
    unfold iidWeight C
    rw [Fintype.prod_ite_zero]
    split_ifs <;> rfl
  have hnonneg : 0 ≤ iidWeight W N w := Finset.prod_nonneg (fun i _ => hW (w i))
  by_cases hgood : ∀ i, E (w i)
  · have heq : (fun i => F (w i)) = (fun i => G (w i)) :=
      funext (fun i => hFG (w i) (hgood i))
    rw [hprod, ite_eq_left hgood, heq]
    nlinarith
  · rw [hprod, ite_eq_right hgood]
    exact add_nonneg (mul_nonneg hnonneg (ht0 _))
      (mul_nonneg hnonneg (sub_nonneg.mpr (ht1 _)))

/-- Population with one target at each of depths one and two. -/
def nearPair (n : ℕ) : Population n := fun i => if i.val < 2 then 1 else 0
/-- Population with one target only at depth one. -/
def nearLeft (n : ℕ) : Population n := fun i => if i.val = 0 then 1 else 0
/-- Population with one target only at depth two. -/
def nearRight (n : ℕ) : Population n := fun i => if i.val = 1 then 1 else 0

abbrev MaskPair (n : ℕ) := Pattern n × Pattern n

def roundWeight {n : ℕ} (p : ℝ) (w : MaskPair n) : ℝ :=
  patternWeight p w.1 * patternWeight p w.2

def longReportA (n : ℕ) (w : MaskPair n) : Fin n → ℕ :=
  twoLegReport (nearPair n) 0 w.1 w.2

def longReportB (n : ℕ) (w : MaskPair n) : Fin n → ℕ :=
  twoLegReport (nearLeft n) (nearRight n) w.1 w.2

def firstTwoAlive {n : ℕ} (w : Pattern n) : Prop :=
  ∀ i, i.val < 2 → w i = true

instance {n : ℕ} (w : Pattern n) : Decidable (firstTwoAlive w) := by
  unfold firstTwoAlive
  infer_instance

def goodPair {n : ℕ} (w : MaskPair n) : Prop := firstTwoAlive w.1 ∧ firstTwoAlive w.2

instance {n : ℕ} (w : MaskPair n) : Decidable (goodPair w) := by
  unfold goodPair
  infer_instance

/-- Both candidates are binary populations. -/
theorem near_populations_binary (n : ℕ) :
    (∀ i, nearPair n i ≤ 1) ∧ (∀ i, nearLeft n i ≤ 1) ∧ (∀ i, nearRight n i ≤ 1) := by
  simp only [nearPair, nearLeft, nearRight]
  constructor
  · intro i; split_ifs <;> omega
  constructor <;> intro i <;> split_ifs <;> omega

/-- The candidates are distinct even after allowing exchange of the two legs. -/
theorem near_populations_distinct {n : ℕ} (hn : 2 ≤ n) :
    ¬ ((nearPair n = nearLeft n ∧ (0 : Population n) = nearRight n) ∨
       (nearPair n = nearRight n ∧ (0 : Population n) = nearLeft n)) := by
  intro h
  rcases h with ⟨h, _⟩ | ⟨h, _⟩
  · have he := congrFun h (⟨1, by omega⟩ : Fin n)
    simp [nearPair, nearLeft] at he
  · have he := congrFun h (⟨0, by omega⟩ : Fin n)
    simp [nearPair, nearRight] at he

/-- A population supported before depth m cannot be heard at a later hop. -/
theorem legReport_zero_after_support {n m : ℕ} (x : Population n) (w : Pattern n)
    (hx : ∀ i, m ≤ i.val → x i = 0) (k : ℕ) (hk : m ≤ k) :
    legReport x w k = 0 := by
  unfold legReport
  apply sum_eq_zero
  intro i _
  split_ifs with hi
  · have hr := aliveRank_le w i
    exact hx i (by omega)
  · rfl

private theorem near_folds (n : ℕ) (k : Fin n) :
    nearPair n k + (0 : Population n) k = nearLeft n k + nearRight n k := by
  simp only [nearPair, nearLeft, nearRight, Pi.zero_apply, add_zero]
  split_ifs <;> omega

/-- Survival of the four initial relays forces equality of the *whole* length-n reports. -/
theorem longReports_eq_on_good {n : ℕ} (w : MaskPair n) (hw : goodPair w) :
    longReportA n w = longReportB n w := by
  funext k
  by_cases hk : k.val < 2
  · have h1 : ∀ j, j ≤ k → w.1 j = true := by
      intro j hj
      exact hw.1 j (by have : j.val ≤ k.val := hj; omega)
    have h2 : ∀ j, j ≤ k → w.2 j = true := by
      intro j hj
      exact hw.2 j (by have : j.val ≤ k.val := hj; omega)
    simp only [longReportA, longReportB,
      ShellResearch.twoLegReport_eq_of_prefix_alive _ _ _ _ k h1 h2]
    exact near_folds n k
  · have hk' : 2 ≤ k.val := by omega
    have hA : legReport (nearPair n) w.1 k.val = 0 :=
      legReport_zero_after_support _ _
        (fun i hi => by simp [nearPair, show ¬i.val < 2 by omega]) _ hk'
    have hL : legReport (nearLeft n) w.1 k.val = 0 :=
      legReport_zero_after_support _ _
        (fun i hi => by simp [nearLeft, show ¬i.val = 0 by omega]) _ hk'
    have hR : legReport (nearRight n) w.2 k.val = 0 :=
      legReport_zero_after_support _ _
        (fun i hi => by simp [nearRight, show ¬i.val = 1 by omega]) _ hk'
    simp only [longReportA, longReportB, twoLegReport, hA, hL, hR]
    simp [legReport]

/-- Four prescribed surviving relays have probability p^4; the remaining masks sum out. -/
theorem goodPair_mass {n : ℕ} (hn : 2 ≤ n) (p : ℝ) :
    (∑ w : MaskPair n, if goodPair w then roundWeight p w else 0) = p^4 := by
  classical
  have hevent (w : Pattern n) : firstTwoAlive w ↔
      ∀ j, j ≤ (⟨1, by omega⟩ : Fin n) → w j = true := by
    constructor
    · intro h j hj
      exact h j (by have : j.val ≤ 1 := hj; omega)
    · intro h j hj
      exact h j (by change j.val ≤ 1; omega)
  have hsum : (∑ w : Pattern n, if firstTwoAlive w then patternWeight p w else 0) = p^2 := by
    simp_rw [hevent]
    rw [sum_weight_prefix_alive]
  rw [Fintype.sum_prod_type]
  have hpoint (a b : Pattern n) :
      (if goodPair (a,b) then roundWeight p (a,b) else 0) =
        (if firstTwoAlive a then patternWeight p a else 0) *
        (if firstTwoAlive b then patternWeight p b else 0) := by
    unfold goodPair roundWeight
    by_cases ha : firstTwoAlive a <;> by_cases hb : firstTwoAlive b <;> simp [ha, hb]
  simp_rw [hpoint]
  rw [← sum_mul_sum, hsum]
  ring

theorem roundWeight_nonneg {n : ℕ} {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (w : MaskPair n) : 0 ≤ roundWeight p w :=
  mul_nonneg (ShellResearch.patternWeight_nonneg hp0 hp1 w.1)
    (ShellResearch.patternWeight_nonneg hp0 hp1 w.2)

theorem roundWeight_sum {n : ℕ} (p : ℝ) : ∑ w : MaskPair n, roundWeight p w = 1 := by
  simp [roundWeight, Fintype.sum_prod_type, ← mul_sum, sum_patternWeight]

/-- A fully concrete lower bound for tests of the actual padded length-n populations. -/
theorem all_length_testing_lower_bound {n : ℕ} (hn : 2 ≤ n)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ)
    (test : (Fin N → Fin n → ℕ) → ℝ)
    (ht0 : ∀ y, 0 ≤ test y) (ht1 : ∀ y, test y ≤ 1) :
    p^(4*N) ≤
      (∑ w : Fin N → MaskPair n,
        iidWeight (roundWeight p) N w * test (fun i => longReportA n (w i))) +
      (∑ w : Fin N → MaskPair n,
        iidWeight (roundWeight p) N w * (1-test (fun i => longReportB n (w i)))) := by
  classical
  have h := common_event_testing_lower_bound (roundWeight p)
    (roundWeight_nonneg hp0 hp1) (longReportA n) (longReportB n) goodPair
    (fun w hw => longReports_eq_on_good w hw) N test ht0 ht1
  rw [goodPair_mass hn p, ← pow_mul] at h
  exact h

/-- Fully formal all-length lower bound at the designed survival rate.
The constant is weaker than the exact two-outcome-law calculation, but this declaration
includes the actual n-length populations and every relay mask explicitly. -/
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
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hnne : (n:ℝ) ≠ 0 := ne_of_gt hnR
  let p := designedRate n
  have hp0 : 0 < p := by dsimp [p, designedRate]; positivity
  have hp1 : p < 1 := by
    dsimp [p, designedRate]
    apply (div_lt_one (by positivity)).mpr
    linarith
  have hbound := all_length_testing_lower_bound hn hp0.le hp1.le N test ht0 ht1
  have hpows : p^(4*N) ≤ 2*δ := by linarith
  have hlog := Real.log_le_log (pow_pos hp0 (4*N)) hpows
  rw [Real.log_pow, Nat.cast_mul] at hlog
  norm_num at hlog
  have hlogp := Real.log_le_sub_one_of_pos (inv_pos.mpr hp0)
  rw [Real.log_inv] at hlogp
  have hinv : p⁻¹-1 = 1/(2*(n:ℝ)) := by
    dsimp [p, designedRate]
    rw [inv_div]
    field_simp
    ring
  rw [hinv] at hlogp
  have hscale := mul_le_mul_of_nonneg_left hlogp (show (0:ℝ) ≤ 4*(N:ℝ) by positivity)
  have hnum : -Real.log (2*δ) ≤ (2*(N:ℝ))/(n:ℝ) := by
    calc -Real.log (2*δ) ≤ (4*(N:ℝ))*(-Real.log p) := by nlinarith [hlog]
         _ ≤ (4*(N:ℝ))*(1/(2*(n:ℝ))) := hscale
         _ = (2*(N:ℝ))/(n:ℝ) := by ring
  have hfinal := (le_div_iff₀ hnR).mp hnum
  rw [one_div, Real.log_inv]
  nlinarith

end ShellSampling
