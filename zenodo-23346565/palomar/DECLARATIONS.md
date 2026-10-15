# Selected declarations

[comparator.json](comparator.json) selects eight names in the namespace
`PalomarDecompression`. The standalone [Challenge.lean](Challenge.lean)
imports only Mathlib, repeats the geometric and finite-view oracle definitions,
and supplies exactly eight intentional proof placeholders.
[Solution.lean](Solution.lean) imports the proof-independent
[Statement.lean](Statement.lean), [UniformStatement.lean](UniformStatement.lean) and complete library, never the Challenge.

| Selected declaration | Mathematical role and substantive proof |
|---|---|
| `cubicCapacity` | For cell size `s >= 37`, the ternary nonroot symbols store one advice bit and `floor((3s+1)/2)` payload bits. [Encoding.lean](LocalDecompression/Encoding.lean), `cubic_capacity`. A budget ingredient, not a separate novelty claim. |
| `oddDegreeCapacity` | For `k >= 2` and `s >= 16(k+1)+1`, `(2^k-1)^(s-1)` states suffice for the advice bit and degree-`2k-1` owned-edge budget. [Encoding.lean](LocalDecompression/Encoding.lean), `odd_degree_capacity`. |
| `markedAdviceCodec` | Under the capacity inequality, gives a root-marked encoder and two readers: advice is recovered independently of orientation or the payload index, and every payload also roundtrips. [Encoding.lean](LocalDecompression/Encoding.lean), `markedBlock`, `blockAdvice`, `bitBlockPayload` and their roundtrip lemmas. |
| `informationLowerBound` | On `K_(degree+1)`, any lossless edge-bit encoding into a uniform vertex budget requires at least `ceil(degree/2)` bits, without a locality restriction. [Ownership.lean](LocalDecompression/Ownership.lean), `completeGraph_lower_bound`. |
| `largeComponentPartition` | Constructs separated roots in every sufficiently large connected degree-bounded graph, proves unique nearest-root cells, size interval `[r+1, (Δ+1)^(2r)]`, radius `2r`, and actual shortest paths staying in each cell. [Partition.lean](LocalDecompression/Partition.lean), `exists_large_component_partition`. |
| `arbitraryLabelCellGeometry` | For arbitrary labels on a connected graph, the radius-truncated nearest-marker cell is nonempty exactly at a marker, has at most `(Δ+1)^R` vertices, contains root-to-vertex geodesics of length at most `R`, and has only nonzero nonroot labels. [BoundedCells.lean](LocalDecompression/BoundedCells.lean), `boundedCell_nonempty_iff_marker`, `boundedCell_card_upper`, `boundedOwner_path`; [BoundedPacket.lean](LocalDecompression/BoundedPacket.lean), `label_ne_zero_of_mem_boundedSites`. No coverage or separation premise. |
| `boundedCellStability` | Radius-`2R` agreement of marker status determines the entire truncated cell, with no assumption that global marker sets agree or cover the graph. [BoundedCells.lean](LocalDecompression/BoundedCells.lean), `boundedCell_eq_of_marker_agreement`. Fixed topology is explicit. |
| `uniformFiniteViewReconstruction` | One decoder family is fixed before graph order, topology, markers, advice and payload. Given a total finite-view orientation rule with sufficient one-bit advice, every connected graph on `Fin n`, with canonical IDs, `n>16(k+1)` and degree at most `2k-1`, admits recovery of every edge bit at **either endpoint** using `2^k` labels per vertex. The same decoder is local on **arbitrary labels across different connected graphs and marker patterns**, within `K=(3R+2)+(2R+1)(T(D)+1)+1`, where `R=32(k+1)` and `D=(2k-1)(2k)^R`. [UniformRecovery.lean](LocalDecompression/UniformRecovery.lean), `uniform_reconstruction`; [SymmetricDecoder.lean](LocalDecompression/SymmetricDecoder.lean), `symmetricUniformDecode_eq_of_graph_view`; [UniformDirections.lean](LocalDecompression/UniformDirections.lean), exact compatibility with the supplied encoder. |

## Statement fidelity

The actual undirected edge type is `{(u,v) // u<v ∧ G.Adj u v}`. The
canonical graph presentation agrees with Mathlib's edge set and degree.
The final query wrapper sorts the two endpoints, so both endpoints recover
the same bit; its extra physical hop is included in `uniformRadius`.

[UniformStatement.lean](UniformStatement.lean) defines the independent
finite-record oracle interface and view relation. Challenge repeats those
definitions and imports only Mathlib. An oracle receives public `N,D,c`,
two endpoint IDs, and a finite set of records containing node IDs, advice
and neighbor IDs. It never receives the physical graph, global marker set,
payload or chosen encoder. `GoodOneBitOracle` assumes only existence of advice
with `2*outdegree <= degree+1`; this sufficient one-sided bound is not full
almost balance and contains no reconstruction or decoder-locality premise.

[OrientationOracle.lean](LocalDecompression/OrientationOracle.lean) proves
exact padding and view invariance. [FiniteView.lean](LocalDecompression/FiniteView.lean),
[ViewPackets.lean](LocalDecompression/ViewPackets.lean), and
[OracleView.lean](LocalDecompression/OracleView.lean) transport walks, cells,
packets and full residual neighbor records across different graphs. The
fringe neighbor records account for the `T(D)+1` factor.
[CrossingBridge.lean](LocalDecompression/CrossingBridge.lean) proves an
order isomorphism preserving actual parallel-edge ranks;
[ResidualBridge.lean](LocalDecompression/ResidualBridge.lean) identifies
the ambient bounded quotient with the original root quotient plus isolated
nonroots. [NamedCorrectness.lean](LocalDecompression/NamedCorrectness.lean)
connects the total decoder to the original `vertexEncode`. Thus the selected
recovery conclusion is derived from the same concrete construction whose
arbitrary-input locality is proved.

The main theorem uses canonical IDs `v.val+1` and fixed public `n` in each
view comparison. It selects a decoder family before all `n`, so topology or
marker sets cannot be hidden in a graph-specific witness. Locality needs only
connected graphs and agreement of the stated finite topology and labels;
it does not assume coverage, separation, good advice, or an encoded input.
Malformed inputs have explicit deterministic defaults in the implementation.
The degree-only radius is conservative; no polynomial bound on the external
radius function or computability of its total rule is proved.

The selected complete-graph lower bound concerns the full graph class. It
matches the storage budget but is not, by itself, a lower bound inside the
restricted large-connected upper-bound domain.

The earlier `graphMarkerReconstruction`, `plainBitCodec`, `ownedEdgeCapacity`
and `adviceFirstGraphReconstruction` remain proved supporting results.
Exact marker recovery and packet-advice recovery are retained; old fixed-graph
locality statements are not substituted for the new uniform endpoint.
The external orientation algorithm, machine semantics and final
mixed-component assembly are explicitly outside scope. See
[README.md](README.md#exact-limits).
