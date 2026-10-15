module

public import Statement
public import LocalDecompression

@[expose] public section

/-! Completed proofs of the exact standalone Palomar challenge statements.
Source: https://doi.org/10.5281/zenodo.23346565.
Challenge.lean is deliberately absent from this module's import closure. -/
namespace PalomarDecompression

/-- The ternary storage inequality for subcubic cells. -/
theorem cubicCapacity (s : ℕ) (hs : 37 ≤ s) :
    2 ^ (1 + (3 * s + 1) / 2) ≤ 3 ^ (s - 1) := by
  exact LocalDecompression.cubic_capacity s hs

/-- The explicit sufficient cell size for every odd degree 2k-1. -/
theorem oddDegreeCapacity (k s : ℕ) (hk : 2 ≤ k) (hs : 16 * (k + 1) + 1 ≤ s) :
    2 ^ (1 + ((2 * k - 1) * s + 1) / 2) ≤ (2 ^ k - 1) ^ (s - 1) := by
  exact LocalDecompression.odd_degree_capacity k s hk hs

/-- Advice and payload are recovered by distinct decoders. The advice reader
receives no orientation or payload-index information; zero marks the root. -/
theorem markedAdviceCodec (m q slots : ℕ) (hq : 0 < q)
    (capacity : 2 ^ (1 + m) ≤ q ^ slots) :
    ∃ encode : Fin 2 → (Fin m → Fin 2) → (Option (Fin slots) → Fin (q + 1)),
    ∃ readAdvice : (Option (Fin slots) → Fin (q + 1)) → Fin 2,
    ∃ readPayload : (Option (Fin slots) → Fin (q + 1)) → (Fin m → Fin 2),
    ∀ a p, readAdvice (encode a p) = a ∧ readPayload (encode a p) = p ∧
      ∀ i, encode a p i = 0 ↔ i = none := by
  refine ⟨(fun a p => LocalDecompression.markedBlock capacity a (finFunctionFinEquiv p)),
    (fun word => LocalDecompression.blockAdvice (LocalDecompression.unmarkedBlock hq word)),
    (fun word => LocalDecompression.bitBlockPayload (LocalDecompression.unmarkedBlock hq word)), ?_⟩
  intro a p
  refine ⟨by simp, ?_, ?_⟩
  · simp [LocalDecompression.bitBlockPayload]
  · intro i
    exact LocalDecompression.markedBlock_zero_iff capacity a (finFunctionFinEquiv p) i

/-- The ordinary whole-component code, using all available vertex symbols. -/
theorem plainBitCodec (edges vertices bits : ℕ) (capacity : edges ≤ bits * vertices) :
    ∃ encode : (Fin edges → Fin 2) → (Fin vertices → Fin (2 ^ bits)),
    ∃ decode : (Fin vertices → Fin (2 ^ bits)) → (Fin edges → Fin 2),
    ∀ x, decode (encode x) = x := by
  exact ⟨LocalDecompression.plainBlockEncode
    (LocalDecompression.plain_binary_capacity edges vertices bits capacity),
    LocalDecompression.plainBlockDecode, fun x => LocalDecompression.plainBlock_roundtrip _ x⟩

/-- Almost-balanced boundary ownership gives the required cell load. -/
theorem ownedEdgeCapacity (internal boundary outgoing degree size : ℕ)
    (hincidence : 2 * internal + boundary ≤ degree * size)
    (hbalance : 2 * outgoing ≤ boundary + 1) :
    internal + outgoing ≤ (degree * size + 1) / 2 := by
  exact LocalDecompression.owned_edge_bound internal boundary outgoing degree size hincidence hbalance

/-- Even a centralized lossless decoder needs ceil(degree/2) vertex bits
on the complete graph of that degree. -/
theorem informationLowerBound (degree bits : ℕ)
    (encode : (((⊤ : SimpleGraph (Fin (degree + 1))).edgeSet) → Fin 2) →
      (Fin (degree + 1) → Fin (2 ^ bits)))
    (decode : (Fin (degree + 1) → Fin (2 ^ bits)) →
      (((⊤ : SimpleGraph (Fin (degree + 1))).edgeSet) → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (degree + 1) / 2 ≤ bits := by
  exact LocalDecompression.completeGraph_lower_bound degree bits encode decode roundtrip

/-- Main finite graph/cell reconstruction theorem. Fix the graph, partition,
roots and orientation algorithm. A single advice reader and a single edge
 decoder work for EVERY balanced advice assignment and EVERY edge labelling.
The two decoders are chosen before the advice. The encoder stores everything
on the original vertices and marks exactly the designated roots.

This is the finite coding reduction used by the paper, not an assertion of
cross-graph LOCAL machine semantics or a formal proof of the cited orientation
theorem. Linear orders represent the fixed vertex and edge identifier orders.
The displayed alphabet has (2^k-1)+1 = 2^k states, hence exactly k bits. -/
theorem adviceFirstGraphReconstruction
    {V E C : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
    [Fintype C] [DecidableEq C]
    (left right : E → V) (noLoop : ∀ e, left e ≠ right e)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (k : ℕ) (hk : 2 ≤ k)
    (hdegree : ∀ v, incidenceDegree left right v ≤ 2 * k - 1)
    (hsize : ∀ c, 16 * (k + 1) + 1 ≤ (cellVertices part c).card) :
    ∃ readAdvice : (V → Fin ((2 ^ k - 1) + 1)) → (C → Fin 2),
    ∃ decode : (V → Fin ((2 ^ k - 1) + 1)) → (E → Fin 2),
    ∀ advice, BalancedBoundaryAdvice left right part orientation advice →
      ∃ encode : (E → Fin 2) → (V → Fin ((2 ^ k - 1) + 1)),
      ∀ input, readAdvice (encode input) = advice ∧ decode (encode input) = input ∧
        ∀ v, encode input v = 0 ↔ v = root (part v) := by
  let G : LocalDecompression.EdgePresentation V E := ⟨left, right, noLoop⟩
  have hd : ∀ v, G.degree v ≤ 2 * k - 1 := hdegree
  have hs : ∀ c, 16 * (k + 1) + 1 ≤ (LocalDecompression.Reduction.partCell part c).card := hsize
  have hq : 0 < 2 ^ k - 1 := by
    have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  let capacity := LocalDecompression.Reduction.odd_cell_capacity part root hroot k hk hs
  refine ⟨(fun labels => LocalDecompression.Reduction.decodeAdvice
    (LocalDecompression.Reduction.wordsOfLabels hq
      (LocalDecompression.Reduction.digitLayout part root hroot) labels)),
    LocalDecompression.Reduction.vertexDecode G part root hroot orientation
      (2 * k - 1) (2 ^ k - 1) hq, ?_⟩
  intro advice hbalanced
  have hb : LocalDecompression.Reduction.BalancedAdvice G part orientation advice := by
    simpa [BalancedBoundaryAdvice, outgoingCount, boundaryCount,
      LocalDecompression.Reduction.BalancedAdvice, LocalDecompression.Reduction.outgoingEdges,
      LocalDecompression.Reduction.ownedEdges, LocalDecompression.Reduction.edgeOwner,
      LocalDecompression.Reduction.partCell, LocalDecompression.EdgePresentation.boundary,
      G, Finset.filter_filter] using hbalanced
  refine ⟨LocalDecompression.Reduction.vertexEncode G part root hroot orientation advice
    (2 * k - 1) (2 ^ k - 1) hd hb capacity, ?_⟩
  intro input
  refine ⟨?_, ?_, ?_⟩
  · simp only [LocalDecompression.Reduction.vertexEncode,
      LocalDecompression.Reduction.wordsOfLabels_labelsOfWords,
      LocalDecompression.Reduction.decodeAdvice_encode]
  · exact LocalDecompression.Reduction.vertexDecode_encode G part root hroot orientation advice
      (2 * k - 1) (2 ^ k - 1) hq hd hb capacity input
  · intro v
    exact LocalDecompression.Reduction.vertexEncode_zero_iff G part root hroot orientation advice
      (2 * k - 1) (2 ^ k - 1) hd hb capacity input v

/-- The independent geometric definition is the existing total selector's fiber. -/
private theorem truncatedCell_eq_boundedCell
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q + 1)) (c : V)
    (hinj : Function.Injective id) :
    truncatedCell G id R labels c =
      LocalDecompression.BoundedCells.boundedCell G id R labels c := by
  classical
  ext v
  simp only [truncatedCell, Finset.mem_filter, Finset.mem_univ, true_and,
    LocalDecompression.BoundedCells.mem_boundedCell,
    LocalDecompression.BoundedCells.boundedOwner_some_iff G id hinj R labels v c]
  rfl
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
  exact LocalDecompression.exists_large_component_partition
    G hconn id hinj r Δ hdegree hlarge

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
  rw [truncatedCell_eq_boundedCell G id R labels c hinj]
  refine ⟨LocalDecompression.BoundedCells.boundedCell_nonempty_iff_marker
    G hconn id hinj R labels c,
    LocalDecompression.BoundedCells.boundedCell_card_upper
      G hconn id hinj R Δ hdegree labels c, ?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, hd, hr, hs⟩ := LocalDecompression.BoundedCells.boundedOwner_path
      G hconn id hinj R labels
      ((LocalDecompression.BoundedCells.mem_boundedCell G id R labels c v).mp hv)
    exact ⟨p, hp, hd, hr, fun w hw =>
      (LocalDecompression.BoundedCells.mem_boundedCell G id R labels c w).mpr (hs w hw)⟩
  · intro v hv hne
    apply LocalDecompression.BoundedPacket.label_ne_zero_of_mem_boundedSites
      G hconn id hinj R labels
    exact Finset.mem_erase.mpr ⟨hne, hv⟩

/-- Radius-2R marker agreement determines the entire truncated cell, even
if the two global marker sets differ and either input has uncovered vertices.
This is stability on a fixed graph, not a cross-topology LOCAL-machine claim. -/
theorem boundedCellStability
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q + 1)) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2 * R → (x w = 0 ↔ y w = 0)) :
    truncatedCell G id R x c = truncatedCell G id R y c := by
  simp only [truncatedCell_eq_boundedCell G id R x c hinj,
    truncatedCell_eq_boundedCell G id R y c hinj]
  exact LocalDecompression.BoundedCells.boundedCell_eq_of_marker_agreement
    G hconn id hinj R x y c hagree

set_option backward.isDefEq.respectTransparency false in
private theorem packetAdvice_eq_boundedAdvice
    {V : Type*} [Fintype V] [LinearOrder V] {q : ℕ}
    (hq : 0 < q) (G : SimpleGraph V) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q + 1)) (c : V) :
    packetAdvice q G id R labels c =
      (LocalDecompression.BoundedPacket.boundedAdvice hq G id R labels c).val := by
  classical
  have heq := truncatedCell_eq_boundedCell G id R labels c hinj
  rw [packetAdvice, heq]
  simp only [packetValue,
    LocalDecompression.BoundedPacket.boundedAdvice,
    LocalDecompression.BoundedPacket.boundedWord, LocalDecompression.blockAdvice,
    finFunctionFinEquiv_apply, LocalDecompression.Reduction.unmark,
    LocalDecompression.BoundedCells.boundedSites]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  symm
  apply Nat.mod_eq_of_lt
  have := (labels ((Fintype.orderIsoFinOfCardEq
    {v // v ∈ (LocalDecompression.BoundedCells.boundedCell G id R labels c).erase c} rfl) i).val).isLt
  omega
set_option backward.isDefEq.respectTransparency false in
private theorem markerDecode_cellQuotient_local
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge G → Fin 2)
    (d q : ℕ) (hq : 0 < q)
    (roots : Finset V) (hne : roots.Nonempty)
    (part : V → roots) (hpart : ∀ v, NearestRoot G roots id (part v).val v)
    (r T : ℕ) (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    (horacle : CellOrientationLocal G part (orientation roots hne) T)
    (x y : V → Fin (q + 1)) (hx : zeroMarkers x = roots) (hy : zeroMarkers y = roots)
    (e : GraphEdge G)
    (hagree : ∀ v, G.dist e.val.1 v ≤ (4 * r + 1) * T + 8 * r + 2 → x v = y v) :
    LocalDecompression.Reduction.markerDecode G hconn id hinj orientation d q hq x e =
      LocalDecompression.Reduction.markerDecode G hconn id hinj orientation d q hq y e := by
  have heq : part = LocalDecompression.rootOwner G roots id hne := by
    funext v
    exact ((LocalDecompression.rootOwner_eq_iff G roots id hne hinj v (part v)).mpr
      (hpart v)).symm
  subst part
  have hcell : ∀ v, G.dist (LocalDecompression.rootOwner G roots id hne v).val v ≤ 2 * r := by
    intro v
    exact LocalDecompression.voronoi_radius G roots id r hcover
      (LocalDecompression.owner_spec G roots id hne v)
  have hedge : ∀ c c' : roots,
      (CellQuotient G (LocalDecompression.rootOwner G roots id hne)).Adj c c' →
        G.dist c.val c'.val ≤ 4 * r + 1 := by
    intro c c' ⟨_, u, v, hu, hv, huv⟩
    have hdU := hcell u
    have hdV := hcell v
    rw [hu] at hdU
    rw [hv] at hdV
    have hdUV := SimpleGraph.dist_eq_one_iff_adj.mpr huv
    have htU := hconn.dist_triangle (u := c.val) (v := u) (w := v)
    have htV := hconn.dist_triangle (u := c.val) (v := v) (w := c'.val)
    rw [G.dist_comm (u := v) (v := c'.val)] at htV
    omega
  apply LocalDecompression.Reduction.markerDecode_local_on_markers G hconn roots id hne hinj
    orientation d q hq (CellQuotient G (LocalDecompression.rootOwner G roots id hne))
    (2 * r) T (4 * r + 1) hcell horacle hedge x y hx hy e
  intro v hv
  apply hagree
  have hd := (LocalDecompression.within_iff_dist G hconn _ _ v).mp hv
  simpa only [← Nat.mul_assoc, Nat.reduceMul, LocalDecompression.graphPresentation] using hd

set_option backward.isDefEq.respectTransparency false in
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
  have hq : 0 < 2 ^ k - 1 := by
    have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega)
    omega
  refine ⟨LocalDecompression.Reduction.markerDecode G hconn id hinj orientation
    (2 * k - 1) (2 ^ k - 1) hq, ?_⟩
  intro roots hne hsep part hpart
  constructor
  · intro advice hbalanced
    have heq : part = LocalDecompression.rootOwner G roots id hne := by
      funext v
      exact ((LocalDecompression.rootOwner_eq_iff G roots id hne hinj v (part v)).mpr
        (hpart v)).symm
    subst part
    have hd : ∀ v, (LocalDecompression.graphPresentation G).degree v ≤ 2 * k - 1 :=
      fun v => (LocalDecompression.graphPresentation_degree G v).trans_le (hdegree v)
    have hb : LocalDecompression.Reduction.BalancedAdvice
        (LocalDecompression.graphPresentation G) (LocalDecompression.rootOwner G roots id hne)
        (orientation roots hne) advice := by
      intro c
      have hout : (LocalDecompression.Reduction.outgoingEdges
          (LocalDecompression.graphPresentation G) (LocalDecompression.rootOwner G roots id hne)
          (orientation roots hne) advice c).card =
          outgoingCount (fun e : GraphEdge G => e.val.1) (fun e : GraphEdge G => e.val.2)
            (LocalDecompression.rootOwner G roots id hne) (orientation roots hne) advice c := by
        apply congrArg Finset.card
        ext e
        simp only [LocalDecompression.Reduction.outgoingEdges,
          LocalDecompression.Reduction.ownedEdges, Finset.mem_filter,
          Finset.mem_univ, true_and, LocalDecompression.Reduction.edgeOwner,
          LocalDecompression.graphPresentation]
      rw [hout]
      simpa [boundaryCount, LocalDecompression.EdgePresentation.boundary,
        LocalDecompression.Reduction.partCell, LocalDecompression.graphPresentation] using hbalanced c
    have capacity := LocalDecompression.Reduction.graph_cell_capacity G hconn roots id hne hinj
      k hk hsep hlarge
    refine ⟨LocalDecompression.Reduction.vertexEncode (LocalDecompression.graphPresentation G)
      (LocalDecompression.rootOwner G roots id hne) Subtype.val
      (LocalDecompression.rootOwner_root G hconn roots id hne hinj)
      (orientation roots hne) advice (2 * k - 1) (2 ^ k - 1) hd hb capacity, ?_⟩
    intro input
    refine ⟨LocalDecompression.Reduction.markerDecode_vertexEncode G hconn roots id hne hinj
      orientation advice (2 * k - 1) (2 ^ k - 1) hq hd hb capacity input,
      LocalDecompression.Reduction.vertexEncode_recognizedRoots G hconn roots id hne hinj
        (orientation roots hne) advice (2 * k - 1) (2 ^ k - 1) hd hb capacity input, ?_⟩
    intro R hcover c
    have hcell : ∀ v, G.dist (LocalDecompression.rootOwner G roots id hne v).val v ≤ R := by
      intro v
      obtain ⟨w, hw, hdist⟩ := hcover v
      exact (LocalDecompression.voronoi_dist_le G roots id
        (LocalDecompression.owner_spec G roots id hne v) hw).trans hdist
    rw [packetAdvice_eq_boundedAdvice hq G id hinj]
    exact congrArg Fin.val (LocalDecompression.BoundedPacket.boundedAdvice_vertexEncode
      hq G hconn roots id hne hinj R hcell (orientation roots hne) advice
      (2 * k - 1) hd hb capacity input c)

  · intro r T hcover horacle x y hx hy e hagree
    exact markerDecode_cellQuotient_local G hconn id hinj orientation (2*k-1) (2^k-1) hq
      roots hne part hpart r T hcover horacle x y hx hy e hagree

end PalomarDecompression
