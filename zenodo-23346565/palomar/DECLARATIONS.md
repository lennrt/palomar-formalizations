# Selected declarations

[comparator.json](comparator.json) selects eight names in the namespace
`PalomarDecompression`. The standalone [Challenge.lean](Challenge.lean)
imports only Mathlib, repeats the finite incidence and geometric definitions,
and supplies exactly eight intentional proof placeholders.
[Solution.lean](Solution.lean) imports the proof-independent
[Statement.lean](Statement.lean) and complete library, never the Challenge.

| Selected declaration | Mathematical role and substantive proof |
|---|---|
| `cubicCapacity` | For cell size `s >= 37`, the ternary nonroot symbols store one advice bit and `floor((3s+1)/2)` payload bits. [Encoding.lean](LocalDecompression/Encoding.lean), `cubic_capacity`. A budget ingredient, not a separate novelty claim. |
| `oddDegreeCapacity` | For `k >= 2` and `s >= 16(k+1)+1`, `(2^k-1)^(s-1)` states suffice for the advice bit and degree-`2k-1` owned-edge budget. [Encoding.lean](LocalDecompression/Encoding.lean), `odd_degree_capacity`. |
| `markedAdviceCodec` | Under the capacity inequality, gives a root-marked encoder and two readers: advice is recovered independently of orientation or the payload index, and every payload also roundtrips. [Encoding.lean](LocalDecompression/Encoding.lean), `markedBlock`, `blockAdvice`, `bitBlockPayload` and their roundtrip lemmas. |
| `informationLowerBound` | On `K_(degree+1)`, any lossless edge-bit encoding into a uniform vertex budget requires at least `ceil(degree/2)` bits, without a locality restriction. [Ownership.lean](LocalDecompression/Ownership.lean), `completeGraph_lower_bound`. |
| `largeComponentPartition` | Constructs separated roots in every sufficiently large connected degree-bounded graph, proves unique nearest-root cells, size interval `[r+1, (Δ+1)^(2r)]`, radius `2r`, and actual shortest paths staying in each cell. [Partition.lean](LocalDecompression/Partition.lean), `exists_large_component_partition`. |
| `arbitraryLabelCellGeometry` | For arbitrary labels on a connected graph, the radius-truncated nearest-marker cell is nonempty exactly at a marker, has at most `(Δ+1)^R` vertices, contains root-to-vertex geodesics of length at most `R`, and has only nonzero nonroot labels. [BoundedCells.lean](LocalDecompression/BoundedCells.lean), `boundedCell_nonempty_iff_marker`, `boundedCell_card_upper`, `boundedOwner_path`; [BoundedPacket.lean](LocalDecompression/BoundedPacket.lean), `label_ne_zero_of_mem_boundedSites`. No coverage or separation premise. |
| `boundedCellStability` | Radius-`2R` agreement of marker status determines the entire truncated cell, with no assumption that global marker sets agree or cover the graph. [BoundedCells.lean](LocalDecompression/BoundedCells.lean), `boundedCell_eq_of_marker_agreement`. Fixed topology is explicit. |
| `graphMarkerReconstruction` | For an actual connected simple graph of odd degree bound `2k-1` with more than `16(k+1)` vertices, chooses **one decoder before the roots and advice**. Every sufficiently separated root set and advice satisfying the explicit boundary outdegree bound admits an encoder recovering all edge bits and exactly that marker set, using `2^k` labels per vertex. The independently defined base-`q` packet parity reader also recovers the supplied advice from those same labels at every covering radius. **The same decoder** is label-local within `(4r+1)T+8r+2` physical hops at the smaller endpoint when roots cover within `2r` and orientation is `T`-local on the actual cell quotient; both compared inputs have the specified markers. [GraphReduction.lean](LocalDecompression/GraphReduction.lean), `graph_cell_capacity`; [Decoder.lean](LocalDecompression/Decoder.lean), `markerDecode_vertexEncode`, `vertexEncode_recognizedRoots`, and `markerDecode_local_on_markers`; [BoundedPacket.lean](LocalDecompression/BoundedPacket.lean), `boundedAdvice_vertexEncode`; [Main.lean](LocalDecompression/Main.lean), the ownership, advice-first and payload roundtrips. |

## Statement fidelity

The graph edge type is `{(u,v) : V × V // u < v ∧ G.Adj u v}`;
[GraphPresentation.lean](LocalDecompression/GraphPresentation.lean) proves
its equivalence to Mathlib's actual undirected edge set and agreement of
incidence degrees. The graph theorem quantifies a proposed partition together
with its independent nearest-root specification; uniqueness identifies it
with the decoder's reconstructed partition. No chosen partition, root set,
advice, or unknown edge payload is an input to the final decoder.

The graph's topology and identifier assignment, and the complete orientation
family, are fixed before the decoder. The correctness and locality conclusions
share this decoder witness. The advice reader is the explicit `packetAdvice`
definition: natural-valued ordered base-`q` digits from the nonroot truncated
cell, reduced modulo two. Its equivalence to the library's bounded advice
reader is proved, and the same encoded labels recover the supplied advice
for every radius covering the roots. The formula takes no orientation or
payload-index input. Empty packet behavior is the literal empty sum, zero. `CellQuotient` is the actual simple graph of
crossing cells, and its distance condition uses walks so disconnected cases
are not collapsed by totalized natural distance. The local-orientation premise
concerns only advice and edge-orientation bits. Physical root distances are
derived from coverage, and final decoder label dependence is proved.
The boundary bound is conditional and one-sided. [QuotientOrientation.lean](LocalDecompression/QuotientOrientation.lean)
proves the residual-quotient lift, but the cited distributed orientation
algorithm itself is not formalized. Locality compares all label assignments with the same markers on the fixed
physical graph, not just encoded inputs. It does not impose operational
uniformity across graph topologies or rule out topology-specific precomputation.
The selected statements therefore do not assert the full unconditional
operational LOCAL theorem.

`plainBitCodec`, `ownedEdgeCapacity`, and the abstract fixed-partition
`adviceFirstGraphReconstruction` remain proved in Solution and the library as
supporting results, but are not individually selected. The larger library
also retains the more specialized residual-quotient locality theorem,
across-marker ordered-packet
stability, component recognition, quotient geometry, and virtual padding.
The manuscript's remaining operational bridges are documented in
[README.md](README.md#exact-limits-of-the-formal-theorem).
