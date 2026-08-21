/-
Paper: An Explicit Obstruction to Uniform Two-Word π-Representability
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21986230
Preprint published: 2026-08-18. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# Scoped formal companion for the G2 explicit-obstruction note

This file checks the two interfaces most prone to silent errors:

* the token-order inversion bridge is stated for two genuine strict linear
  orders and for distinct fibres;
* the finite arithmetic and pigeonhole endpoint of the 20-bit obstruction.

It does **not** claim to formalize word lists, stars and bars, the full
permutation-graph compaction characterization, or the paper's main theorem.
Those limitations are stated identically in the paper and README.
-/

namespace G2Companion

/-- The occurrence tokens for `k` occurrences of every vertex. -/
abbrev Token (V : Type*) (k : Nat) := V × Fin k

/-- Two distinct tokens are adjacent in the inversion graph when the two
linear orders orient them oppositely.  The disjunction makes symmetry explicit. -/
def inversionAdj {α : Type*} (L₁ L₂ : LinearOrder α) (p q : α) : Prop :=
  (L₁.lt p q ∧ L₂.lt q p) ∨ (L₁.lt q p ∧ L₂.lt p q)

theorem inversionAdj_symm {α : Type*} (L₁ L₂ : LinearOrder α) (p q : α) :
    inversionAdj L₁ L₂ p q ↔ inversionAdj L₁ L₂ q p := by
  simp only [inversionAdj, or_comm]

theorem inversionAdj_loopless {α : Type*} (L₁ L₂ : LinearOrder α) (p : α) :
    ¬ inversionAdj L₁ L₂ p p := by
  simp [inversionAdj, @lt_irrefl α L₁.toPreorder p]

/-- The genuine simple inversion graph of two linear orders. -/
def inversionGraph {α : Type*} (L₁ L₂ : LinearOrder α) : SimpleGraph α where
  Adj := inversionAdj L₁ L₂
  symm := fun p q => (inversionAdj_symm L₁ L₂ p q).mp
  loopless := ⟨inversionAdj_loopless L₁ L₂⟩

/-- For distinct tokens, absence of an inversion is exactly agreement of the
forward comparison in the two linear orders. -/
theorem not_inversionAdj_iff_lt_agree {α : Type*}
    (L₁ L₂ : LinearOrder α) {p q : α} (hpq : p ≠ q) :
    ¬ inversionAdj L₁ L₂ p q ↔ (L₁.lt p q ↔ L₂.lt p q) := by
  constructor
  · intro hNo
    constructor
    · intro h₁
      rcases @lt_trichotomy α L₂ p q with h₂ | heq | h₂
      · exact h₂
      · exact (hpq heq).elim
      · exact (hNo (Or.inl ⟨h₁, h₂⟩)).elim
    · intro h₂
      rcases @lt_trichotomy α L₁ p q with h₁ | heq | h₁
      · exact h₁
      · exact (hpq heq).elim
      · exact (hNo (Or.inr ⟨h₁, h₂⟩)).elim
  · intro hAgree hInv
    rcases hInv with hInv | hInv
    · have h₂pq : L₂.lt p q := hAgree.mp hInv.1
      exact (@lt_asymm α L₂.toPreorder p q h₂pq hInv.2).elim
    · have h₁pq : L₁.lt p q := hAgree.mpr hInv.2
      exact (@lt_asymm α L₁.toPreorder p q h₁pq hInv.1).elim

/-- All cross-token comparisons between two fibres agree. -/
def FibreAgreement {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (Token V k)) (x y : V) : Prop :=
  ∀ i j : Fin k, L₁.lt (x, i) (y, j) ↔ L₂.lt (x, i) (y, j)

/-- Some inversion-graph edge joins the two fibres. -/
def QuotientEdge {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (Token V k)) (x y : V) : Prop :=
  ∃ i j : Fin k, inversionAdj L₁ L₂ (x, i) (y, j)

/-- Formal comparison/inversion bridge at the token-order level.  The
distinctness hypothesis is essential and mirrors the corrected paper theorem. -/
theorem fibreAgreement_iff_not_quotientEdge {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (Token V k)) {x y : V} (hxy : x ≠ y) :
    FibreAgreement L₁ L₂ x y ↔ ¬ QuotientEdge L₁ L₂ x y := by
  constructor
  · intro hAgree hEdge
    rcases hEdge with ⟨i, j, hInv⟩
    have hToken : (x, i) ≠ (y, j) := by
      intro h
      exact hxy (congrArg Prod.fst h)
    have hNo := (not_inversionAdj_iff_lt_agree L₁ L₂ hToken).2 (hAgree i j)
    exact hNo hInv
  · intro hNoEdge i j
    have hToken : (x, i) ≠ (y, j) := by
      intro h
      exact hxy (congrArg Prod.fst h)
    apply (not_inversionAdj_iff_lt_agree L₁ L₂ hToken).1
    intro hInv
    exact hNoEdge ⟨i, j, hInv⟩

/-- The occurrence indexing is compatible with one token order. -/
def FibreMonotone {V : Type*} {k : Nat}
    (L : LinearOrder (Token V k)) : Prop :=
  ∀ x i j, L.lt (x, i) (x, j) ↔ i < j

/-- When both orders use the same occurrence indexing, a fibre is independent
in their inversion graph. -/
theorem sameFibre_noInversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (Token V k))
    (h₁ : FibreMonotone L₁) (h₂ : FibreMonotone L₂)
    (x : V) (i j : Fin k) :
    ¬ inversionAdj L₁ L₂ (x, i) (x, j) := by
  intro hInv
  rcases hInv with hInv | hInv
  · have hij : i < j := (h₁ x i j).mp hInv.1
    have hji : j < i := (h₂ x j i).mp hInv.2
    exact (LT.lt.asymm hij hji).elim
  · have hji : j < i := (h₁ x j i).mp hInv.1
    have hij : i < j := (h₂ x i j).mp hInv.2
    exact (LT.lt.asymm hji hij).elim

/-! ## Exact obstruction arithmetic -/

theorem gapCodeCount_2_20 : Nat.choose 42 2 = 861 := by
  norm_num [Nat.choose_two_right]

theorem traceCapacity_2_20 : (Nat.choose 42 2) ^ 2 = 741321 := by
  norm_num [gapCodeCount_2_20]

theorem vcDimensionEndpoint_2_20 : (Nat.choose 42 2) ^ 2 + 20 < 2 ^ 20 := by
  norm_num [gapCodeCount_2_20]

theorem explicitWitness_overflows : 741321 < 741322 := by
  norm_num

theorem explicitWitness_fits : 741322 ≤ 2 ^ 20 := by
  norm_num

/-- The right-vertex index itself is its 20-bit code, viewed as an element of
`Fin (2^20)`. -/
def witnessBitCode (j : Fin 741322) : Fin (2 ^ 20) :=
  ⟨j.val, lt_of_lt_of_le j.isLt explicitWitness_fits⟩

theorem witnessBitCode_injective : Function.Injective witnessBitCode := by
  intro i j h
  apply Fin.ext
  have hv : (witnessBitCode i).val = (witnessBitCode j).val :=
    congrArg (fun z : Fin (2 ^ 20) => z.val) h
  exact hv

/-- No injection can assign 741322 distinct traces to only 741321 codes. -/
theorem no_trace_code_injection :
    ¬ ∃ f : Fin 741322 → Fin 741321, Function.Injective f := by
  rintro ⟨f, hf⟩
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hcard
  omega

#print axioms fibreAgreement_iff_not_quotientEdge
#print axioms sameFibre_noInversion
#print axioms gapCodeCount_2_20
#print axioms traceCapacity_2_20
#print axioms vcDimensionEndpoint_2_20
#print axioms explicitWitness_overflows
#print axioms explicitWitness_fits
#print axioms witnessBitCode_injective
#print axioms no_trace_code_injection

end G2Companion
