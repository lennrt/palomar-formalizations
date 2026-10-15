module

public import LossyShell.Recovery
public import LossyShell.Trace
public import Mathlib.Data.Fin.VecNotation

/-!
# Main theorems for the interior sensor on a path

* `twoLegReport_noiseless`: without failures the interior sensor sees only the fold `a + b`.
* `twoLegLaw_one`: at survival probability `1` the report law is the point mass at the fold.
* `twoLegMean_eq_of_fold_eq`, `fold_eq_of_twoLegMean_eq`: for every `p > 0`, the mean report
  carries exactly the information of the noiseless report.
* `legs_eq_of_moments`: for `0 < p < 1`, the mean and the second moments determine the two legs
  up to exchanging them.
* `legs_eq_of_mean_covariance`: the same recovery theorem stated directly for covariance.
* `twoLegLaw_eq_iff`: equality of lossy report laws is exactly equality up to exchanging legs.
-/

@[expose] public section

namespace LossyShell

open Finset

variable {n : ℕ}

/-! ### Exchanging the legs -/

/-- Swapping both the populations and their failure patterns preserves every report. -/
lemma twoLegReport_swap (a b : Population n) (ω₁ ω₂ : Pattern n) :
    twoLegReport a b ω₁ ω₂ = twoLegReport b a ω₂ ω₁ := by
  funext k
  exact Nat.add_comm _ _

/-- The report law cannot distinguish the two legs: their independent patterns have the
same survival probability, so exchanging them preserves every report probability. -/
lemma twoLegLaw_swap {K : Type*} [CommRing K] (p : K) (a b : Population n) :
    twoLegLaw p a b = twoLegLaw p b a := by
  funext h
  unfold twoLegLaw
  rw [sum_comm]
  apply sum_congr rfl
  intro ω₂ _
  apply sum_congr rfl
  intro ω₁ _
  rw [twoLegReport_swap a b ω₁ ω₂, mul_comm]

/-! ### Noiseless reports -/

lemma legReport_all_true (x : Population n) (k : Fin n) :
    legReport x (fun _ => true) k.val = x k := by
  unfold legReport
  rw [sum_eq_single k]
  · simp [aliveRank_all_true]
  · intro i _ hik
    rw [ite_eq_right]
    rintro ⟨_, h⟩
    rw [aliveRank_all_true] at h
    exact hik (Fin.ext (by omega))
  · simp

/-- Without failures, the interior sensor reports the folded population `a + b`. -/
theorem twoLegReport_noiseless (a b : Population n) :
    twoLegReport a b (fun _ => true) (fun _ => true) = a + b := by
  funext k
  simp [twoLegReport, legReport_all_true]

variable {K : Type*}

lemma patternWeight_one [CommRing K] (ω : Pattern n) :
    patternWeight (1 : K) ω = if ω = (fun _ => true) then 1 else 0 := by
  unfold patternWeight
  simp only [sub_self]
  rw [Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

/-- At survival probability one, the law is the point mass at the folded population. -/
theorem twoLegLaw_one [CommRing K] (a b : Population n) (h : Fin n → ℕ) :
    twoLegLaw (1 : K) a b h = if a + b = h then 1 else 0 := by
  unfold twoLegLaw
  simp_rw [patternWeight_one]
  rw [sum_eq_single (fun _ => true)]
  · rw [sum_eq_single (fun _ => true)]
    · simp [twoLegReport_noiseless]
    · intro ω₂ _ hω₂; simp [hω₂]
    · simp
  · intro ω₁ _ hω₁
    apply sum_eq_zero
    intro ω₂ _
    simp [hω₁]
  · simp

/-! ### Complete relay failure -/

/-- If every relay fails, every target is silent. -/
lemma twoLegReport_all_false (a b : Population n) :
    twoLegReport a b (fun _ => false) (fun _ => false) = 0 := by
  funext k
  simp [twoLegReport, legReport]

lemma patternWeight_zero [CommRing K] (ω : Pattern n) :
    patternWeight (0 : K) ω = if ω = (fun _ => false) then 1 else 0 := by
  unfold patternWeight
  simp only [sub_zero]
  have h : (fun i => if ω i = true then (0 : K) else 1) =
      (fun i => if ω i = false then 1 else 0) := by
    funext i
    cases ω i <;> simp
  rw [h, Fintype.prod_boole]
  simp only [funext_iff]
  split_ifs <;> rfl

/-- At survival probability zero, all populations have the point mass at the zero report.
This makes the exclusion of `p = 0` from the recovery theorem explicit. -/
theorem twoLegLaw_zero [CommRing K] (a b : Population n) (h : Fin n → ℕ) :
    twoLegLaw (0 : K) a b h = if 0 = h then 1 else 0 := by
  unfold twoLegLaw
  simp_rw [patternWeight_zero]
  rw [sum_eq_single (fun _ => false)]
  · rw [sum_eq_single (fun _ => false)]
    · simp [twoLegReport_all_false]
    · intro ω₂ _ hω₂; simp [hω₂]
    · simp
  · intro ω₁ _ hω₁
    apply sum_eq_zero
    intro ω₂ _
    simp [hω₁]
  · simp

/-- The mean report vanishes when no relay survives. -/
theorem twoLegMean_zero [CommRing K] (a b : Population n) :
    twoLegMean (0 : K) a b = 0 := by
  funext k
  simp [twoLegMean, patternWeight_zero, twoLegReport_all_false]

/-- The covariance vanishes when no relay survives. -/
theorem twoLegCovariance_zero [CommRing K] (a b : Population n) :
    twoLegCovariance (0 : K) a b = 0 := by
  funext k l
  simp [twoLegCovariance, twoLegMean_zero, twoLegSecondMoment,
    patternWeight_zero, twoLegReport_all_false]

/-! ### Means -/

lemma twoLegMean_eq_fold [CommRing K] (p : K) (a b : Population n) (k : Fin n) :
    twoLegMean p a b k = ∑ i, (((a + b) i : ℕ) : K) * landProb p i k.val := by
  rw [twoLegMean_eq]
  unfold legMean
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  push_cast [Pi.add_apply]
  ring

/-- For every survival probability, the mean report depends only on the fold `a + b`. -/
theorem twoLegMean_eq_of_fold_eq [CommRing K] (p : K) {a b a' b' : Population n}
    (h : a + b = a' + b') : twoLegMean p a b = twoLegMean p a' b' := by
  funext k
  rw [twoLegMean_eq_fold, twoLegMean_eq_fold, h]

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For every positive survival probability, the mean report determines the fold `a + b`. -/
theorem fold_eq_of_twoLegMean_eq {p : K} (hp : 0 < p) {a b a' b' : Population n}
    (h : twoLegMean p a b = twoLegMean p a' b') : a + b = a' + b' := by
  have hK := fold_eq_of_legMean_eq hp (fun i => (((a + b) i : ℕ) : K))
    (fun i => (((a' + b') i : ℕ) : K)) (fun k => by
      rw [← twoLegMean_eq_fold, ← twoLegMean_eq_fold, h])
  funext i
  exact_mod_cast congrFun hK i

/-! ### The first two moments determine the legs -/

/-- **Failures break folded trades.** If `0 < p < 1`, the mean and the second moments of the
interior sensor's lossy report determine the two legs up to exchanging them. -/
theorem legs_eq_of_moments {p : K} (hp0 : 0 < p) (hp1 : p < 1) {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hsecond : twoLegSecondMoment p a b = twoLegSecondMoment p a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  -- The mean first recovers the sum of the populations (the noiseless fold).
  have hfold := fold_eq_of_twoLegMean_eq hp0 hmean
  have hsum : (fun i => (a i : K)) + (fun i => (b i : K)) =
      (fun i => (a' i : K)) + (fun i => (b' i : K)) := by
    funext i
    have := congrFun hfold i
    simp only [Pi.add_apply] at this ⊢
    exact_mod_cast this
  have hcov : ∀ k l : Fin n,
      Qform p (fun i => (a i : K)) (fun i => (a i : K)) k.val l.val +
          Qform p (fun i => (b i : K)) (fun i => (b i : K)) k.val l.val =
        Qform p (fun i => (a' i : K)) (fun i => (a' i : K)) k.val l.val +
          Qform p (fun i => (b' i : K)) (fun i => (b' i : K)) k.val l.val := by
    intro k l
    rw [← twoLeg_covariance, ← twoLeg_covariance, hmean, congrFun (congrFun hsecond k) l]
  -- Polarization isolates the covariance form of the difference of the populations.
  have hdiff : ∀ k l : Fin n,
      Qform p ((fun i => (a i : K)) - (fun i => (b i : K)))
          ((fun i => (a i : K)) - (fun i => (b i : K))) k.val l.val =
        Qform p ((fun i => (a' i : K)) - (fun i => (b' i : K)))
          ((fun i => (a' i : K)) - (fun i => (b' i : K))) k.val l.val := by
    intro k l
    have h1 := Qform_parallelogram p (fun i => (a i : K)) (fun i => (b i : K)) k.val l.val
    have h2 := Qform_parallelogram p (fun i => (a' i : K)) (fun i => (b' i : K)) k.val l.val
    rw [hsum, hcov k l] at h1
    linear_combination h1 - h2
  -- The difference is determined up to sign, which is precisely the exchange of legs.
  rcases eq_or_eq_neg_of_Qform hp0 hp1 hdiff with h | h
  · left
    have key : ∀ i, (a i : K) = a' i ∧ (b i : K) = b' i := by
      intro i
      have e1 := congrFun hsum i
      have e2 := congrFun h i
      simp only [Pi.add_apply, Pi.sub_apply] at e1 e2
      exact ⟨by linear_combination (e1 + e2) / 2, by linear_combination (e1 - e2) / 2⟩
    exact ⟨funext fun i => by exact_mod_cast (key i).1, funext fun i => by exact_mod_cast (key i).2⟩
  · right
    have key : ∀ i, (a i : K) = b' i ∧ (b i : K) = a' i := by
      intro i
      have e1 := congrFun hsum i
      have e2 := congrFun h i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at e1 e2
      exact ⟨by linear_combination (e1 + e2) / 2, by linear_combination (e1 - e2) / 2⟩
    exact ⟨funext fun i => by exact_mod_cast (key i).1, funext fun i => by exact_mod_cast (key i).2⟩

/-- For `0 < p < 1`, equality of the report means and covariance arrays determines the two
leg populations up to exchange. Equal means turn covariance equality into second-moment
equality, so this is the observable-covariance formulation of `legs_eq_of_moments`. -/
theorem legs_eq_of_mean_covariance {p : K} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hcov : twoLegCovariance p a b = twoLegCovariance p a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  apply legs_eq_of_moments hp0 hp1 hmean
  funext k l
  have hkl := congrFun (congrFun hcov k) l
  simp only [twoLegCovariance, hmean] at hkl
  exact sub_left_inj.mp hkl

/-! ### Sparse observable covariance recovery -/

/-- The mean, every covariance diagonal entry, and one adaptively selected covariance column
suffice for recovery. The selected column is the greatest nonzero diagonal of
`imbalanceCovariance`, which is computed from the mean-recovered fold and observed covariance.
If all these corrected diagonals vanish, no column is needed. The statement includes `n = 0`.
For `n ≥ 1`, at most `n` diagonal and `n - 1` off-diagonal entries are used. -/
theorem legs_eq_of_mean_covariance_sparse {p : K} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n}
    (hmean : twoLegMean p a b = twoLegMean p a' b')
    (hdiag : ∀ k : Fin n, twoLegCovariance p a b k k = twoLegCovariance p a' b' k k)
    (hcol : ∀ m : Fin n, imbalanceCovariance p a b m m ≠ 0 →
      (∀ j : Fin n, m < j → imbalanceCovariance p a b j j = 0) →
      ∀ k : Fin n, k < m → twoLegCovariance p a b k m = twoLegCovariance p a' b' k m) :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  have hfold := fold_eq_of_twoLegMean_eq hp0 hmean
  have hsum : (fun i => (a i : K) + b i) = (fun i => (a' i : K) + b' i) := by
    funext i
    have := congrFun hfold i
    simp only [Pi.add_apply] at this
    exact_mod_cast this
  have himbalance : ∀ k l : Fin n,
      twoLegCovariance p a b k l = twoLegCovariance p a' b' k l →
      imbalanceCovariance p a b k l = imbalanceCovariance p a' b' k l := by
    intro k l hkl
    simp only [imbalanceCovariance, hsum, hkl]
  have hdiff : (fun i => (a i : K) - b i) = (fun i => (a' i : K) - b' i) ∨
      (fun i => (a i : K) - b i) = -(fun i => (a' i : K) - b' i) := by
    apply eq_or_eq_neg_of_Qform_sparse hp0 hp1
    · intro k
      rw [← imbalanceCovariance_eq, ← imbalanceCovariance_eq]
      exact himbalance k k (hdiag k)
    · intro m hm hzero k hk
      rw [← imbalanceCovariance_eq, ← imbalanceCovariance_eq]
      apply himbalance k m
      apply hcol m
      · simpa only [imbalanceCovariance_eq] using hm
      · simpa only [imbalanceCovariance_eq] using hzero
      · exact hk
  apply legs_eq_of_mean_covariance hp0 hp1 hmean
  funext k l
  have hcorrected : imbalanceCovariance p a b k l = imbalanceCovariance p a' b' k l := by
    rw [imbalanceCovariance_eq, imbalanceCovariance_eq]
    rcases hdiff with h | h
    · rw [h]
    · rw [h, Qform_neg]
  simp only [imbalanceCovariance, hsum] at hcorrected
  linear_combination hcorrected / 2

/-! ### From the law to the moments -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
lemma expectation_eq_sum_law (p : K) (a b : Population n) (S : Finset (Fin n → ℕ))
    (hS : ∀ ω₁ ω₂, twoLegReport a b ω₁ ω₂ ∈ S) (F : (Fin n → ℕ) → K) :
    ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n,
        patternWeight p ω₁ * patternWeight p ω₂ * F (twoLegReport a b ω₁ ω₂) =
      ∑ h ∈ S, twoLegLaw p a b h * F h := by
  unfold twoLegLaw
  simp_rw [sum_mul, ite_mul, zero_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro ω₁ _
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro ω₂ _
  rw [sum_ite_eq, ite_eq_left (hS ω₁ ω₂)]

/-- **The lossy law determines the legs** up to exchanging them, whenever `0 < p < 1`. -/
theorem legs_eq_of_twoLegLaw {p : K} (hp0 : 0 < p) (hp1 : p < 1) {a b a' b' : Population n}
    (h : twoLegLaw p a b = twoLegLaw p a' b') :
    (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  classical
  let S : Finset (Fin n → ℕ) :=
    (univ : Finset (Pattern n × Pattern n)).image (fun ω => twoLegReport a b ω.1 ω.2) ∪
      (univ : Finset (Pattern n × Pattern n)).image (fun ω => twoLegReport a' b' ω.1 ω.2)
  have hS : ∀ ω₁ ω₂, twoLegReport a b ω₁ ω₂ ∈ S := fun ω₁ ω₂ =>
    mem_union_left _ (mem_image_of_mem _ (mem_univ (ω₁, ω₂)))
  have hS' : ∀ ω₁ ω₂, twoLegReport a' b' ω₁ ω₂ ∈ S := fun ω₁ ω₂ =>
    mem_union_right _ (mem_image_of_mem _ (mem_univ (ω₁, ω₂)))
  apply legs_eq_of_moments hp0 hp1
  · funext k
    unfold twoLegMean
    rw [expectation_eq_sum_law p a b S hS (fun r => (r k : K)),
      expectation_eq_sum_law p a' b' S hS' (fun r => (r k : K)), h]
  · funext k l
    unfold twoLegSecondMoment
    rw [expectation_eq_sum_law p a b S hS (fun r => (r k : K) * (r l : K)),
      expectation_eq_sum_law p a' b' S hS' (fun r => (r k : K) * (r l : K)), h]

/-- For `0 < p < 1`, two populations have the same report law exactly when their two legs
agree up to exchange. The forward direction is recovery; the reverse direction records the
unavoidable reflection symmetry of the observation model. -/
theorem twoLegLaw_eq_iff {p : K} (hp0 : 0 < p) (hp1 : p < 1)
    {a b a' b' : Population n} :
    twoLegLaw p a b = twoLegLaw p a' b' ↔
      (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
  constructor
  · exact legs_eq_of_twoLegLaw hp0 hp1
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact twoLegLaw_swap p _ _

/-- Indistinguishability at one nondegenerate survival probability is precisely reflection
symmetry, so it persists at every other parameter, including the probability endpoints. -/
theorem twoLegLaw_eq_of_twoLegLaw_eq {p : K} (hp0 : 0 < p) (hp1 : p < 1) (q : K)
    {a b a' b' : Population n} (h : twoLegLaw p a b = twoLegLaw p a' b') :
    twoLegLaw q a b = twoLegLaw q a' b' := by
  rcases legs_eq_of_twoLegLaw hp0 hp1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact twoLegLaw_swap q _ _

/-- The equivalence classes of report laws do not depend on which survival probability in
`(0, 1)` is used. This is an exact identifiability statement, not a conditioning bound. -/
theorem twoLegLaw_eq_iff_at_probabilities {p q : K} (hp0 : 0 < p) (hp1 : p < 1)
    (hq0 : 0 < q) (hq1 : q < 1) {a b a' b' : Population n} :
    twoLegLaw p a b = twoLegLaw p a' b' ↔ twoLegLaw q a b = twoLegLaw q a' b' := by
  exact ⟨twoLegLaw_eq_of_twoLegLaw_eq hp0 hp1 q, twoLegLaw_eq_of_twoLegLaw_eq hq0 hq1 p⟩

/-- **An explicit trade broken by failures.** Without failures, targets at distances `1` and `2`
on one side are indistinguishable from targets at distance `1` on one side and `2` on the other;
with failures at any rate strictly between `0` and `1`, the two report laws differ. -/
theorem failures_break_trade :
    twoLegReport (![1, 1] : Population 2) ![0, 0] (fun _ => true) (fun _ => true) =
        twoLegReport (![1, 0] : Population 2) ![0, 1] (fun _ => true) (fun _ => true) ∧
      twoLegLaw (1 : K) (![1, 1] : Population 2) ![0, 0] =
        twoLegLaw (1 : K) (![1, 0] : Population 2) ![0, 1] ∧
      ∀ p : K, 0 < p → p < 1 →
        twoLegLaw p (![1, 1] : Population 2) ![0, 0] ≠ twoLegLaw p ![1, 0] ![0, 1] := by
  have hfold : (![1, 1] : Population 2) + ![0, 0] = ![1, 0] + ![0, 1] := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · rw [twoLegReport_noiseless, twoLegReport_noiseless, hfold]
  · funext h
    rw [twoLegLaw_one, twoLegLaw_one, hfold]
  · intro p hp0 hp1 hlaw
    rcases legs_eq_of_twoLegLaw hp0 hp1 hlaw with ⟨h1, _⟩ | ⟨h1, _⟩
    · have := congrFun h1 1
      simp at this
    · have := congrFun h1 0
      simp at this

end LossyShell
