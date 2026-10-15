module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-! Palomar statement surface. Intentional `sorry` declarations occur only
here, as the conventional unproved challenge goals. Solution never imports
this module; Comparator checks its same-name declarations separately.

Source: https://doi.org/10.5281/zenodo.23346565.
The principal result is uniformFiniteViewReconstruction: one decoder family
recovers edge bits at either endpoint and is local across changing topology
and marker patterns, conditional on an explicit finite-view orientation rule.
The external orientation algorithm and executable-machine semantics remain
outside this formalization. -/
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

namespace PalomarDecompression
open scoped BigOperators

/-- Actual undirected edges listed once in increasing endpoint order. -/
abbrev GraphEdge {V : Type*} [LinearOrder V] (G : SimpleGraph V) :=
  {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}

/-- Nearest root, breaking distance ties by the supplied injective identifiers. -/
def NearestRoot {V : Type*} (G : SimpleGraph V) (roots : Finset V)
    (id : V → ℕ) (c v : V) : Prop :=
  c ∈ roots ∧ ∀ q ∈ roots,
    G.dist c v < G.dist q v ∨ (G.dist c v = G.dist q v ∧ id c ≤ id q)

/-- The actual vertices assigned to a nearest-root cell. -/
noncomputable def rootCell {V : Type*} [Fintype V] (G : SimpleGraph V)
    (roots : Finset V) (id : V → ℕ) (c : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => NearestRoot G roots id c v)

/-- Zero is the recognizable root marker. All other symbols store digits. -/
def zeroMarkers {V : Type*} [Fintype V] {q : ℕ}
    (labels : V → Fin (q + 1)) : Finset V :=
  Finset.univ.filter (fun v => labels v = 0)

/-- The radius-truncated nearest-marker cell on an arbitrary label assignment.
A nonmarker has an empty cell; vertices with no marker within R belong to no
cell. No coverage or separation condition is part of this definition. -/
noncomputable def truncatedCell {V : Type*} [Fintype V] (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) {q : ℕ} (labels : V → Fin (q + 1)) (c : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v =>
    NearestRoot G (zeroMarkers labels) id c v ∧ G.dist c v ≤ R)

/-- The ternary storage inequality for subcubic cells. -/
theorem cubicCapacity (s : ℕ) (hs : 37 ≤ s) :
    2 ^ (1 + (3 * s + 1) / 2) ≤ 3 ^ (s - 1) := by
  sorry

/-- The explicit sufficient cell size for every odd degree 2k-1. -/
theorem oddDegreeCapacity (k s : ℕ) (hk : 2 ≤ k) (hs : 16 * (k + 1) + 1 ≤ s) :
    2 ^ (1 + ((2 * k - 1) * s + 1) / 2) ≤ (2 ^ k - 1) ^ (s - 1) := by
  sorry

/-- Advice and payload are recovered by distinct decoders. The advice reader
receives no orientation or payload-index information; zero marks the root. -/
theorem markedAdviceCodec (m q slots : ℕ) (hq : 0 < q)
    (capacity : 2 ^ (1 + m) ≤ q ^ slots) :
    ∃ encode : Fin 2 → (Fin m → Fin 2) → (Option (Fin slots) → Fin (q + 1)),
    ∃ readAdvice : (Option (Fin slots) → Fin (q + 1)) → Fin 2,
    ∃ readPayload : (Option (Fin slots) → Fin (q + 1)) → (Fin m → Fin 2),
    ∀ a p, readAdvice (encode a p) = a ∧ readPayload (encode a p) = p ∧
      ∀ i, encode a p i = 0 ↔ i = none := by
  sorry



/-- Even a centralized lossless decoder needs ceil(degree/2) vertex bits
on the complete graph of that degree. -/
theorem informationLowerBound (degree bits : ℕ)
    (encode : (((⊤ : SimpleGraph (Fin (degree + 1))).edgeSet) → Fin 2) →
      (Fin (degree + 1) → Fin (2 ^ bits)))
    (decode : (Fin (degree + 1) → Fin (2 ^ bits)) →
      (((⊤ : SimpleGraph (Fin (degree + 1))).edgeSet) → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (degree + 1) / 2 ≤ bits := by
  sorry


/-- Lemma 5 of https://doi.org/10.5281/zenodo.23346565: roots are
constructed, every vertex has a unique cell, cells contain enough storage
sites and have degree-only size/radius bounds, and shortest root paths stay
inside their cells. The identifiers are an arbitrary injective assignment. -/
theorem largeComponentPartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (r Δ : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (hlarge : r < Fintype.card V) :
    ∃ roots : Finset V,
      roots.Nonempty ∧
      (∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → 2 * r < G.dist a b) ∧
      (∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r) ∧
      (∀ v, ∃! c, NearestRoot G roots id c v) ∧
      (∀ c ∈ roots, r + 1 ≤ (rootCell G roots id c).card ∧
        (rootCell G roots id c).card ≤ (Δ + 1) ^ (2 * r)) ∧
      (∀ c v, NearestRoot G roots id c v → G.dist c v ≤ 2 * r) ∧
      (∀ c v, NearestRoot G roots id c v →
        ∃ p : G.Walk c v, p.IsPath ∧ p.length = G.dist c v ∧
          ∀ w ∈ p.support, NearestRoot G roots id c w) := by
  sorry

/-- Lemma 8 of https://doi.org/10.5281/zenodo.23346565 on arbitrary
labels, including malformed or uncovered inputs. A cell is nonempty exactly
at a marker, contains at most (Δ+1)^R vertices, has a shortest path of length
at most R from its marker to every vertex, and its nonroot labels are nonzero.
The physical graph is connected; no marker coverage or separation is assumed. -/
theorem arbitraryLabelCellGeometry
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R Δ : ℕ)
    (hdegree : ∀ v, G.degree v ≤ Δ) (labels : V → Fin (q + 1)) (c : V) :
    ((truncatedCell G id R labels c).Nonempty ↔ labels c = 0) ∧
    (truncatedCell G id R labels c).card ≤ (Δ + 1) ^ R ∧
    (∀ v ∈ truncatedCell G id R labels c,
      ∃ p : G.Walk c v, p.IsPath ∧ p.length = G.dist c v ∧ p.length ≤ R ∧
        ∀ w ∈ p.support, w ∈ truncatedCell G id R labels c) ∧
    (∀ v ∈ truncatedCell G id R labels c, v ≠ c → labels v ≠ 0) := by
  sorry

/-- Radius-2R marker agreement determines the entire truncated cell, even
if the two global marker sets differ and either input has uncovered vertices.
This is stability on a fixed graph, not a cross-topology LOCAL-machine claim. -/
theorem boundedCellStability
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q + 1)) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2 * R → (x w = 0 ↔ y w = 0)) :
    truncatedCell G id R x c = truncatedCell G id R y c := by
  sorry

/-- Uniform finite-view reduction for optimal odd-degree storage. Given one
fixed total finite-view orientation rule with good one-bit advice, one decoder
family is chosen before graph order, topology, marker sets, advice and payload.
On every sufficiently large connected graph of maximum degree at most 2k-1,
an encoder stores all edge-membership bits in the 2^k-symbol vertex alphabet.
The SAME decoder depends only on the stated physical neighborhood on every
labeling, even when graphs and marker sets change or inputs are malformed.

Vertices are named 0,...,n-1 with identifiers v+1 and public graph order n.
The radius depends on k and the oracle radius T, never on n. The explicit
oracle premise concerns only a sufficient orientation outdegree bound, not compression.
This is a reduction to that premise, not a formal implementation or proof of
the external orientation algorithm. See Lemmas 7 and 9 of
https://doi.org/10.5281/zenodo.23346565. -/
theorem uniformFiniteViewReconstruction
    (F : LocalDecompression.OrientationOracle.Rule) (T : ℕ → ℕ)
    (hgood : LocalDecompression.OrientationOracle.GoodOneBitOracle F T)
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ decode : (n : ℕ) → SimpleGraph (Fin n) →
        (Fin n → Fin ((2 ^ k - 1) + 1)) → (Fin n × Fin n) → Fin 2,
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
        G.Connected → 16 * (k + 1) < n → (∀ v, G.degree v ≤ 2 * k - 1) →
        ∃ encode : (GraphEdge G → Fin 2) → (Fin n → Fin ((2 ^ k - 1) + 1)),
          ∀ input e, decode n G (encode input) e.val = input e ∧
            decode n G (encode input) e.val.swap = input e) ∧
      (∀ (n : ℕ) (G H : SimpleGraph (Fin n)), G.Connected → H.Connected →
        ∀ (x y : Fin n → Fin ((2 ^ k - 1) + 1)) (u v : Fin n),
          LocalDecompression.FiniteView.SameGraphView G H u (uniformRadius k T) →
          (∀ w, G.dist u w ≤ uniformRadius k T → x w = y w) →
          decode n G x (u, v) = decode n H y (u, v)) := by
  sorry

end PalomarDecompression
