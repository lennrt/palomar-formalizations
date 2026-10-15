module

public import LossyShell.Landing

/-!
# First and second moments of lossy reports

For one leg, the mean of report entry `k` is `∑ i, x i * landProb p i k`, and the mixed second
moment of entries `k, l` is `∑ i, ∑ j, x i * x j * pairProb p i j k l`. For a sensor between two
independent legs the means add, and the covariance is the sum of the two legs' covariance forms
`Qform p u u`.
-/

@[expose] public section

namespace LossyShell

open Finset

variable {n : ℕ} {K : Type*} [CommRing K]

lemma legReport_cast (x : Population n) (ω : Pattern n) (k : ℕ) :
    (legReport x ω k : K) =
      ∑ i, (x i : K) * (if ω i = true ∧ aliveRank ω i = k + 1 then 1 else 0) := by
  unfold legReport
  push_cast
  apply sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- Mean of one leg's report entry. -/
lemma sum_weight_legReport (p : K) (x : Population n) (k : ℕ) :
    ∑ ω : Pattern n, patternWeight p ω * (legReport x ω k : K) =
      ∑ i, (x i : K) * landProb p i k := by
  simp_rw [legReport_cast, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  unfold landProb
  rw [mul_sum]
  apply sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Mixed second moment of one leg's report entries. -/
lemma sum_weight_legReport_mul (p : K) (x : Population n) (k l : ℕ) :
    ∑ ω : Pattern n, patternWeight p ω * ((legReport x ω k : K) * (legReport x ω l : K)) =
      ∑ i, ∑ j, (x i : K) * x j * pairProb p i j k l := by
  simp_rw [legReport_cast, sum_mul_sum, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  unfold pairProb
  rw [mul_sum]
  apply sum_congr rfl
  intro ω _
  by_cases h1 : ω i = true ∧ aliveRank ω i = k + 1 <;>
    by_cases h2 : ω j = true ∧ aliveRank ω j = l + 1 <;>
    simp [h1, h2, mul_comm]

lemma twoLegReport_cast (a b : Population n) (ω₁ ω₂ : Pattern n) (k : Fin n) :
    (twoLegReport a b ω₁ ω₂ k : K) = (legReport a ω₁ k.val : K) + (legReport b ω₂ k.val : K) := by
  simp only [twoLegReport, Nat.cast_add]

/-- The mean of one leg, as a vector over report entries. -/
def legMean (p : K) (x : Population n) (k : ℕ) : K := ∑ i, (x i : K) * landProb p i k

/-- The second-moment array of one leg. -/
def legSecond (p : K) (x : Population n) (k l : ℕ) : K :=
  ∑ i, ∑ j, (x i : K) * x j * pairProb p i j k l

/-- Independence of the legs, in expectation: averaging a function of one leg's pattern over
both patterns averages it over that leg alone. -/
lemma sum_sum_weight_left (p : K) (f : Pattern n → K) :
    ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n, patternWeight p ω₁ * patternWeight p ω₂ * f ω₁ =
      ∑ ω₁ : Pattern n, patternWeight p ω₁ * f ω₁ := by
  apply sum_congr rfl
  intro ω₁ _
  calc ∑ ω₂ : Pattern n, patternWeight p ω₁ * patternWeight p ω₂ * f ω₁
      = (patternWeight p ω₁ * f ω₁) * ∑ ω₂ : Pattern n, patternWeight p ω₂ := by
        rw [mul_sum]; apply sum_congr rfl; intro ω₂ _; ring
    _ = patternWeight p ω₁ * f ω₁ := by rw [sum_patternWeight, mul_one]

lemma sum_sum_weight_right (p : K) (f : Pattern n → K) :
    ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n, patternWeight p ω₁ * patternWeight p ω₂ * f ω₂ =
      ∑ ω₂ : Pattern n, patternWeight p ω₂ * f ω₂ := by
  rw [sum_comm]
  calc ∑ ω₂ : Pattern n, ∑ ω₁ : Pattern n, patternWeight p ω₁ * patternWeight p ω₂ * f ω₂
      = ∑ ω₂ : Pattern n, ∑ ω₁ : Pattern n, patternWeight p ω₂ * patternWeight p ω₁ * f ω₂ := by
        apply sum_congr rfl; intro ω₂ _; apply sum_congr rfl; intro ω₁ _; ring
    _ = _ := sum_sum_weight_left p f

lemma sum_sum_weight_both (p : K) (f g : Pattern n → K) :
    ∑ ω₁ : Pattern n, ∑ ω₂ : Pattern n, patternWeight p ω₁ * patternWeight p ω₂ * (f ω₁ * g ω₂) =
      (∑ ω₁ : Pattern n, patternWeight p ω₁ * f ω₁) *
        ∑ ω₂ : Pattern n, patternWeight p ω₂ * g ω₂ := by
  rw [sum_mul_sum]
  apply sum_congr rfl; intro ω₁ _; apply sum_congr rfl; intro ω₂ _; ring

lemma twoLegMean_eq (p : K) (a b : Population n) (k : Fin n) :
    twoLegMean p a b k = legMean p a k.val + legMean p b k.val := by
  unfold twoLegMean legMean
  simp_rw [twoLegReport_cast, mul_add, sum_add_distrib]
  rw [sum_sum_weight_left p (fun ω₁ => (legReport a ω₁ k.val : K)),
    sum_sum_weight_right p (fun ω₂ => (legReport b ω₂ k.val : K)),
    sum_weight_legReport, sum_weight_legReport]

lemma twoLegSecondMoment_eq (p : K) (a b : Population n) (k l : Fin n) :
    twoLegSecondMoment p a b k l =
      legSecond p a k.val l.val + legMean p a k.val * legMean p b l.val +
        legMean p b k.val * legMean p a l.val + legSecond p b k.val l.val := by
  unfold twoLegSecondMoment
  simp_rw [twoLegReport_cast]
  have hexp : ∀ ω₁ ω₂ : Pattern n,
      patternWeight p ω₁ * patternWeight p ω₂ *
        (((legReport a ω₁ k.val : K) + legReport b ω₂ k.val) *
          ((legReport a ω₁ l.val : K) + legReport b ω₂ l.val)) =
      patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport a ω₁ k.val : K) * legReport a ω₁ l.val) +
        patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport a ω₁ k.val : K) * legReport b ω₂ l.val) +
        patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport b ω₂ k.val : K) * legReport a ω₁ l.val) +
        patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport b ω₂ k.val : K) * legReport b ω₂ l.val) := by
    intro ω₁ ω₂; ring
  simp_rw [hexp, sum_add_distrib]
  have hBA : ∀ ω₁ ω₂ : Pattern n,
      patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport b ω₂ k.val : K) * legReport a ω₁ l.val) =
        patternWeight p ω₁ * patternWeight p ω₂ *
          ((legReport a ω₁ l.val : K) * legReport b ω₂ k.val) := by
    intro ω₁ ω₂; ring
  simp_rw [hBA]
  rw [sum_sum_weight_left p (fun ω₁ => (legReport a ω₁ k.val : K) * legReport a ω₁ l.val),
    sum_sum_weight_right p (fun ω₂ => (legReport b ω₂ k.val : K) * legReport b ω₂ l.val),
    sum_sum_weight_both p (fun ω₁ => (legReport a ω₁ k.val : K))
      (fun ω₂ => (legReport b ω₂ l.val : K)),
    sum_sum_weight_both p (fun ω₁ => (legReport a ω₁ l.val : K))
      (fun ω₂ => (legReport b ω₂ k.val : K)),
    sum_weight_legReport_mul, sum_weight_legReport_mul,
    sum_weight_legReport, sum_weight_legReport, sum_weight_legReport, sum_weight_legReport]
  unfold legSecond legMean
  ring

/-- The covariance form of one leg, extended bilinearly to arbitrary vectors. -/
def Qform (p : K) (u v : Fin n → K) (k l : ℕ) : K :=
  ∑ i, ∑ j, u i * v j * (pairProb p i j k l - landProb p i k * landProb p j l)

lemma Qform_cast_eq (p : K) (x : Population n) (k l : ℕ) :
    Qform p (fun i => (x i : K)) (fun i => (x i : K)) k l =
      legSecond p x k l - legMean p x k * legMean p x l := by
  unfold Qform legSecond legMean
  rw [sum_mul_sum]
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro i _
  rw [← sum_sub_distrib]
  apply sum_congr rfl; intro j _
  ring

/-- The covariance of the interior sensor's report is the sum of the legs' covariance forms. -/
lemma twoLeg_covariance (p : K) (a b : Population n) (k l : Fin n) :
    twoLegSecondMoment p a b k l - twoLegMean p a b k * twoLegMean p a b l =
      Qform p (fun i => (a i : K)) (fun i => (a i : K)) k.val l.val +
        Qform p (fun i => (b i : K)) (fun i => (b i : K)) k.val l.val := by
  rw [twoLegSecondMoment_eq, twoLegMean_eq, twoLegMean_eq, Qform_cast_eq, Qform_cast_eq]
  ring

/-- The observed covariance array is the sum of the two independent leg covariance forms. -/
lemma twoLegCovariance_eq (p : K) (a b : Population n) (k l : Fin n) :
    twoLegCovariance p a b k l =
      Qform p (fun i => (a i : K)) (fun i => (a i : K)) k.val l.val +
        Qform p (fun i => (b i : K)) (fun i => (b i : K)) k.val l.val := by
  exact twoLeg_covariance p a b k l

/-- Polarization: the forms of `a + b` and `a - b` add up to twice the forms of `a` and `b`. -/
lemma Qform_parallelogram (p : K) (u v : Fin n → K) (k l : ℕ) :
    Qform p (u + v) (u + v) k l + Qform p (u - v) (u - v) k l =
      2 * (Qform p u u k l + Qform p v v k l) := by
  unfold Qform
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [← sum_add_distrib, mul_add, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro i _
  rw [← sum_add_distrib, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro j _
  ring

lemma Qform_neg (p : K) (u : Fin n → K) (k l : ℕ) : Qform p (-u) (-u) k l = Qform p u u k l := by
  unfold Qform
  simp only [Pi.neg_apply, neg_mul_neg]


/-- The observable covariance after subtracting the covariance form of the recovered fold.
Polarization identifies it with the covariance form of the difference between the legs. -/
def imbalanceCovariance (p : K) (a b : Population n) (k l : Fin n) : K :=
  2 * twoLegCovariance p a b k l -
    Qform p (fun i => (a i : K) + b i) (fun i => (a i : K) + b i) k.val l.val

/-- The corrected observed covariance is exactly the covariance form of the leg imbalance. -/
lemma imbalanceCovariance_eq (p : K) (a b : Population n) (k l : Fin n) :
    imbalanceCovariance p a b k l =
      Qform p (fun i => (a i : K) - b i) (fun i => (a i : K) - b i) k.val l.val := by
  unfold imbalanceCovariance
  rw [twoLegCovariance_eq, sub_eq_iff_eq_add]
  have h := Qform_parallelogram p (fun i => (a i : K)) (fun i => (b i : K)) k.val l.val
  exact h.symm.trans (add_comm _ _)

end LossyShell
