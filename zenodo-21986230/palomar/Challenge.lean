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
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

/-!
# Uniform two-word π-representability and the explicit obstruction

The definitions below are the standard word semantics from the paper.  The
trace theorem records its stars-and-bars bound in the equivalent form that
any finite outside family with pairwise distinct traces has bounded size.
-/

namespace PalomarG2

/-- Delete every letter other than `x` and `y`, i.e. the paper's `π_{x,y}`. -/
def twoLetterProjection {V : Type*} [DecidableEq V]
    (w : List V) (x y : V) : List V :=
  w.filter (fun z => z = x ∨ z = y)

/-- Every letter occurs exactly `k` times. -/
def KUniform {V : Type*} [DecidableEq V] (k : Nat) (w : List V) : Prop :=
  ∀ x, w.count x = k

/-- Two `k`-uniform words represent a graph when distinct vertices are
adjacent exactly when their two-letter projections agree. -/
structure TwoWordPiRepresentation {V : Type*} [DecidableEq V]
    (k : Nat) (G : SimpleGraph V) where
  word₁ : List V
  word₂ : List V
  uniform₁ : KUniform k word₁
  uniform₂ : KUniform k word₂
  adj_iff_projection_eq : ∀ {x y : V}, x ≠ y →
    (G.Adj x y ↔
      twoLetterProjection word₁ x y = twoLetterProjection word₂ x y)

def TwoWordPiRepresentable {V : Type*} [DecidableEq V]
    (k : Nat) (G : SimpleGraph V) : Prop :=
  Nonempty (TwoWordPiRepresentation k G)

/-- The open-neighborhood trace `N_G(x) ∩ A`. -/
noncomputable def neighborhoodTrace {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x : V) : Finset V := by
  classical
  exact A.filter (fun a => G.Adj x a)

/-- The paper's trace bound: a family outside `A` with pairwise distinct
neighborhood traces has at most `choose (k * (|A| + 1)) k ^ 2` members. -/
theorem neighborhood_trace_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : Nat}
    (r : TwoWordPiRepresentation k G) (A X : Finset V)
    (hout : ∀ x ∈ X, x ∉ A)
    (htraces : Set.InjOn (neighborhoodTrace G A) (X : Set V)) :
    X.card ≤ (Nat.choose (k * (A.card + 1)) k) ^ 2 := by
  sorry

abbrev B20Vertex := Fin 20 ⊕ Fin 741322

/-- The `i`th least-significant bit of `j` is one.  This is equivalent to the
paper's formula `⌊j / 2^i⌋ ≡ 1 (mod 2)`. -/
def b20Bit (i : Fin 20) (j : Fin 741322) : Prop :=
  j.val.testBit i.val = true

def b20Adj : B20Vertex → B20Vertex → Prop
  | Sum.inl i, Sum.inr j => b20Bit i j
  | Sum.inr j, Sum.inl i => b20Bit i j
  | _, _ => False

/-- The paper's bipartite bit-incidence graph on 20 left and 741322 right
vertices, with no edges inside either part. -/
def B20 : SimpleGraph B20Vertex where
  Adj := b20Adj
  symm := by
    intro x y h
    rcases x with i | j <;> rcases y with i' | j' <;>
      simpa [b20Adj] using h
  loopless := ⟨fun x => by
    rcases x with i | j <;> simp [b20Adj]⟩

/-- The explicit graph `B20` is not representable by two 2-uniform words. -/
theorem B20_not_twoWordPiRepresentable :
    ¬ TwoWordPiRepresentable 2 B20 := by
  sorry

/-- For distinct fibres, every cross-token comparison agrees in two linear
orders exactly when there is no cross-fibre inversion. -/
theorem fibre_agreement_iff_no_cross_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k)) {x y : V} (hxy : x ≠ y) :
    (∀ i j : Fin k, L₁.lt (x, i) (y, j) ↔ L₂.lt (x, i) (y, j)) ↔
      ¬ ∃ i j : Fin k,
        (L₁.lt (x, i) (y, j) ∧ L₂.lt (y, j) (x, i)) ∨
        (L₁.lt (y, j) (x, i) ∧ L₂.lt (x, i) (y, j)) := by
  sorry

/-- If occurrence indices increase in the same direction in both orders, no
two tokens in one fibre form an inversion. -/
theorem same_fibre_no_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k))
    (h₁ : ∀ x i j, L₁.lt (x, i) (x, j) ↔ i < j)
    (h₂ : ∀ x i j, L₂.lt (x, i) (x, j) ↔ i < j)
    (x : V) (i j : Fin k) :
    ¬ ((L₁.lt (x, i) (x, j) ∧ L₂.lt (x, j) (x, i)) ∨
       (L₁.lt (x, j) (x, i) ∧ L₂.lt (x, i) (x, j))) := by
  sorry

/-- The exact numerical endpoint used by the `k = 2`, `m = 20`
neighbourhood-trace bound. -/
theorem trace_capacity_endpoint : (Nat.choose 42 2) ^ 2 + 20 < 2 ^ 20 := by
  sorry

/-- There is no injective assignment of 741322 traces to 741321 codes. -/
theorem no_trace_code_injection :
    ¬ ∃ f : Fin 741322 → Fin 741321, Function.Injective f := by
  sorry

end PalomarG2
