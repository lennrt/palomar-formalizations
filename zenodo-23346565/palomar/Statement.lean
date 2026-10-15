module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.Sort
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-! Proof-independent finite incidence and geometric definitions used by the solution.
Source: https://doi.org/10.5281/zenodo.23346565.
The standalone Challenge repeats these definitions verbatim and imports only
Mathlib. This module contains no challenge holes and no reconstruction proofs. -/
namespace PalomarDecompression
open scoped BigOperators

/-- Degree in a finite loopless edge presentation, counted with multiplicity.
The left/right order is bookkeeping and does not orient the graph. -/
def incidenceDegree {V E : Type*} [DecidableEq V] [Fintype E]
    (left right : E → V) (v : V) : ℕ :=
  ∑ e, ((if left e = v then 1 else 0) + (if right e = v then 1 else 0))

/-- The vertices assigned to one root of a partition. -/
def cellVertices {V C : Type*} [Fintype V] [DecidableEq C]
    (part : V → C) (c : C) : Finset V :=
  Finset.univ.filter (fun v => part v = c)

/-- Number of edges with exactly one endpoint in a cell. -/
def boundaryCount {V E C : Type*} [Fintype E] [DecidableEq C]
    (left right : E → V) (part : V → C) (c : C) : ℕ :=
  ∑ e, if (part (left e) = c ∧ part (right e) ≠ c) ∨
    (part (left e) ≠ c ∧ part (right e) = c) then 1 else 0

/-- Boundary edges owned by a cell when the orientation selects an endpoint:
zero selects left and one selects right. Internal edges are excluded. -/
def outgoingCount {V E C : Type*} [Fintype E] [DecidableEq C]
    (left right : E → V) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (advice : C → Fin 2) (c : C) : ℕ :=
  (Finset.univ.filter (fun e =>
    (if orientation advice e = 0 then part (left e) else part (right e)) = c ∧
      part (left e) ≠ part (right e))).card

/-- The orientation-only oracle condition. This contains no edge payload,
encoder, decoder, or recovery hypothesis. -/
def BalancedBoundaryAdvice {V E C : Type*} [Fintype E] [DecidableEq C]
    (left right : E → V) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (advice : C → Fin 2) : Prop :=
  ∀ c, 2 * outgoingCount left right part orientation advice c ≤
    boundaryCount left right part c + 1

/-- Actual undirected edges listed once in increasing endpoint order. -/
abbrev GraphEdge {V : Type*} [LinearOrder V] (G : SimpleGraph V) :=
  {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}

/-- Actual adjacency of distinct cells, witnessed by a physical graph edge. -/
def CellQuotient {V C : Type*} (G : SimpleGraph V) (part : V → C) : SimpleGraph C where
  Adj c d := c ≠ d ∧ ∃ u v, part u = c ∧ part v = d ∧ G.Adj u v
  symm := ⟨fun _ _ h => ⟨Ne.symm h.1,
    Exists.elim h.2 (fun u hu => Exists.elim hu
      (fun v hv => ⟨v, u, hv.2.1, hv.1, hv.2.2.symm⟩))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- Only quotient-nearby advice can affect this orientation output. Walks
make the definition valid even when the quotient is disconnected. -/
def CellOrientationLocal {V C : Type*} [LinearOrder V] (G : SimpleGraph V)
    (part : V → C) (orientation : (C → Fin 2) → GraphEdge G → Fin 2) (T : ℕ) : Prop :=
  ∀ a b e, (∀ c, (∃ p : (CellQuotient G part).Walk (part e.val.1) c,
    p.length ≤ T) → a c = b c) → orientation a e = orientation b e


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
/-- The ordered nonzero digits on a specified set of storage sites. -/
noncomputable def packetValue {V : Type*} [LinearOrder V] (q : ℕ)
    (labels : V → Fin (q + 1)) (sites : Finset V) : ℕ :=
  ∑ i : Fin (Fintype.card {v // v ∈ sites}),
    ((labels ((Fintype.orderIsoFinOfCardEq {v // v ∈ sites} rfl) i).val).val - 1) *
      q ^ i.val

/-- Explicit advice reader: read the nonroot truncated-cell sites in increasing
vertex order, subtract the marker offset and take the base-q word's parity.
No orientation, advice, or payload index is an input. Empty packets give zero. -/
noncomputable def packetAdvice {V : Type*} [Fintype V] [LinearOrder V]
    (q : ℕ) (G : SimpleGraph V) (id : V → ℕ) (R : ℕ)
    (labels : V → Fin (q + 1)) (c : V) : ℕ :=
  packetValue q labels ((truncatedCell G id R labels c).erase c) % 2


end PalomarDecompression
