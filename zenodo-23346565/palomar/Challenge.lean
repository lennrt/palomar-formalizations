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
The principal selected result is graphMarkerReconstruction, with one decoder
uniform over root sets on a fixed physical graph.
The published orientation theorem and the complete LOCAL simulation are not
claimed as closed Lean proofs. -/
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

/-- Graph-native reconstruction and label-locality of ONE decoder chosen
before the roots and advice. The same simple graph supplies edges, degrees
and distances. The decoder receives only labels, whose zeros reveal roots.
Every separated root set and advice satisfying the boundary outdegree bound
works for every input edge subset. The explicit ordered packet reader recovers
the supplied advice from these same labels, for every covering radius.
It receives no orientation or payload indices. Moreover, if these roots cover within 2r
and the orientation is T-local on the actual cell quotient, the SAME decoder
has physical label radius (4r+1)T+8r+2 at the edge's smaller endpoint on all
labels with this marker set, including labels outside the encoder's image.
The premises concern orientation outputs only, not payload recovery or final
decoder locality. This is the quantitative finite reduction behind Lemmas 7
and 9 of https://doi.org/10.5281/zenodo.23346565. The locality assertion fixes
topology and markers; it does not formalize uniform operational LOCAL
semantics, the external orientation algorithm or malformed-marker execution. -/
theorem graphMarkerReconstruction
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (k : ℕ) (hk : 2 ≤ k)
    (hlarge : 16 * (k + 1) < Fintype.card V)
    (hdegree : ∀ v, G.degree v ≤ 2 * k - 1)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge G → Fin 2) :
    ∃ decode : (V → Fin ((2 ^ k - 1) + 1)) → (GraphEdge G → Fin 2),
    ∀ (roots : Finset V) (hne : roots.Nonempty),
      (∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → 2 * (16 * (k + 1)) < G.dist a b) →
      ∀ part : V → roots, (∀ v, NearestRoot G roots id (part v).val v) →
      (∀ advice : roots → Fin 2,
        BalancedBoundaryAdvice (fun e : GraphEdge G => e.val.1)
          (fun e : GraphEdge G => e.val.2) part (orientation roots hne) advice →
        ∃ encode : (GraphEdge G → Fin 2) → (V → Fin ((2 ^ k - 1) + 1)),
        ∀ input, decode (encode input) = input ∧ zeroMarkers (encode input) = roots ∧
          ∀ R, (∀ v, ∃ c ∈ roots, G.dist c v ≤ R) → ∀ c : roots,
            packetAdvice (2 ^ k - 1) G id R (encode input) c.val = (advice c).val) ∧
      (∀ r T, (∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r) →
        CellOrientationLocal G part (orientation roots hne) T →
        ∀ x y : V → Fin ((2 ^ k - 1) + 1),
          zeroMarkers x = roots → zeroMarkers y = roots →
          ∀ e : GraphEdge G,
            (∀ v, G.dist e.val.1 v ≤ (4 * r + 1) * T + 8 * r + 2 → x v = y v) →
            decode x e = decode y e) := by
  sorry

end PalomarDecompression
