module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fin.VecNotation

/-!
# Lossy hop-count shell reports along a path

A sensor counts, at every hop distance, the anonymous targets it can hear. Relays fail
independently; a failed relay is bypassed (its neighbours are spliced together, so every
surviving relay further out moves one hop closer) and the targets sitting on it fall silent.

Positions on a leg are indexed by `Fin n`: index `i` is the relay at true hop distance `i + 1`.
Report entries are indexed by `k : ℕ`: entry `k` counts targets at hop distance `k + 1`.

These definitions are repeated verbatim in `Challenge.lean`.
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

end LossyShell
