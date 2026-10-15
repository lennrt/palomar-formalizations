module
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-! Proof-independent finite-view and orientation interfaces for
https://doi.org/10.5281/zenodo.23346565. Challenge repeats these definitions
and imports only Mathlib. The orientation property is an explicit theorem
premise; this module supplies neither an axiom nor an algorithm. -/

namespace LocalDecompression.OrientationOracle
open scoped BigOperators
structure NodeRecord where
  identifier : ℕ
  advice : Fin 2
  neighbors : Finset ℕ
  deriving DecidableEq

noncomputable def neighbors {V : Type*} [Fintype V]
    (G : SimpleGraph V) (v : V) : Finset V := by
  classical
  exact G.neighborFinset v

/-- A finite flooding process; the successor adds all neighbors. -/
noncomputable def floodBall {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ → V → Finset V
  | 0, v => {v}
  | t + 1, v => by
    classical
    exact floodBall G t v ∪ (floodBall G t v).biUnion (neighbors G)

noncomputable def record {V : Type*} [Fintype V]
    (G : SimpleGraph V) (id : V → ℕ) (advice : V → Fin 2) (v : V) : NodeRecord :=
  ⟨id v, advice v, (neighbors G v).image id⟩

/-- Records include the full neighbor-ID list at the fringe, so this view
requires at most t+1 communication rounds with canonical ID-ordered ports. -/
noncomputable def view {V : Type*} [Fintype V]
    (G : SimpleGraph V) (id : V → ℕ) (advice : V → Fin 2) (t : ℕ) (v : V) :
    Finset NodeRecord := (floodBall G t v).image (record G id advice)

/-- Public order, exact maximum degree, ID exponent; two ordered endpoint IDs;
then a finite view. No whole graph or actual root set is available to this rule. -/
abbrev Rule := ℕ → ℕ → ℕ → ℕ → ℕ → Finset NodeRecord → Fin 2

noncomputable def output {V : Type*} [Fintype V]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (advice : V → Fin 2) (u v : V) : Fin 2 :=
  F N D c (id u) (id v) (view G id advice t u)

/-- Canonical ownership uses the smaller-ID endpoint's output, making the
orientation consistent on every advice assignment, including invalid advice. -/
noncomputable def tailId {V : Type*} [Fintype V]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (advice : V → Fin 2) (u v : V) : ℕ :=
  if id u < id v then
    if output F N D c t G id advice u v = 0 then id u else id v
  else
    if output F N D c t G id advice v u = 0 then id v else id u

noncomputable def outdegree {V : Type*} [Fintype V]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (advice : V → Fin 2) (v : V) : ℕ :=
  ((neighbors G v).filter (fun w => tailId F N D c t G id advice v w = id v)).card

/-- The exact sufficient consequence of the external one-bit orientation
theorem. It is an explicit theorem premise, not an axiom or implementation.
The same total finite-view rule is used for all graphs and advice assignments. -/
def GoodOneBitOracle (F : Rule) (T : ℕ → ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (N D c : ℕ),
    Fintype.card V = N → G.maxDegree = D → 1 ≤ c →
    ∀ id : V → ℕ, Function.Injective id →
      (∀ v, 1 ≤ id v ∧ id v ≤ N ^ c) →
      ∃ advice : V → Fin 2, ∀ v,
        2 * outdegree F N D c (T D) G id advice v ≤ G.degree v + 1


end LocalDecompression.OrientationOracle

namespace LocalDecompression.FiniteView
variable {V : Type*} [Fintype V] [DecidableEq V]
/-- Equality of rooted induced physical views, on common vertex identifiers.
Labels are deliberately separate from the topology clause. This compares
possibly different physical graphs, without fixing their outside topology. -/
structure SameGraphView (G H : SimpleGraph V) (center : V) (radius : ℕ) : Prop where
  vertices : ∀ v, G.dist center v ≤ radius ↔ H.dist center v ≤ radius
  edges : ∀ u v, G.dist center u ≤ radius → G.dist center v ≤ radius →
    (G.Adj u v ↔ H.Adj u v)


end LocalDecompression.FiniteView

namespace PalomarDecompression
/-- Radius used for bounded marker selection. -/
def cellSelectionRadius (k : ℕ) : ℕ := 2 * (16 * (k + 1))

/-- Degree bound on the simple residual quotient, independent of graph order. -/
def quotientDegreeBound (k : ℕ) : ℕ := (2 * k - 1) * (2 * k) ^ cellSelectionRadius k

/-- A conservative physical radius for the total finite-view decoder. -/
def uniformRadius (k : ℕ) (T : ℕ → ℕ) : ℕ :=
  (3 * cellSelectionRadius k + 2) +
    (2 * cellSelectionRadius k + 1) * (T (quotientDegreeBound k) + 1) + 1
end PalomarDecompression
