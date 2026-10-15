# Optimal Local Decompression: Finite Reduction and Graph Geometry

Lennart Rudolph · [10.5281/zenodo.23346565](https://doi.org/10.5281/zenodo.23346565)

The graph is the communication network. An unrestricted encoder sees the
graph and an arbitrary subset of its edges, and writes a fixed number of bits
at each vertex. The distributed decoder learns remote topology through
communication and should recover the incident edge-membership bits.
The paper proves a constant-round construction with the counting-optimal
`k` bits per vertex for each fixed odd maximum degree `2k-1 >= 3`.
This Lean project formalizes the finite reconstruction and geometric parts
of that argument. The full operational LOCAL theorem remains only partially
mechanized, as the manuscript's Section 7 explains.

## Why the construction matters

[Balliu et al., Distributed Computation with Local Advice](https://doi.org/10.4230/LIPIcs.DISC.2025.12),
Section 1.8, Question 4, asks whether cubic graphs admit two-bit local
decompression. Their earlier general method needs one additional bit above
the counting budget. The manuscript's idea is to amortize marker and
orientation metadata over bounded connected cells. For odd degree `2k-1`,
reserving one symbol of the `2^k`-symbol alphabet leaves `2^k-1` data symbols,
whose rate exceeds `(2k-1)/2` bits per vertex. Large enough cells therefore
hold both the owned edge bits and one advice bit.

A decoder first finds the zero markers and reconstructs the cells. It reads
each cell's advice before computing orientation or payload positions. This
order avoids assuming the ownership information needed to locate the advice
itself. The selected graph theorem checks that a **single decoder, chosen
before the roots and advice**, recovers every edge-bit assignment and the
exact marker set on a connected component with more than `16(k+1)` vertices.
An explicit ordered packet reader recovers the supplied advice from those
same labels. The same decoder has physical label radius `(4r+1)T+8r+2`
when roots cover within `2r` and orientation is `T`-local on the actual cell
quotient; this locality comparison fixes both topology and marker set.
Its graph is an actual finite simple graph: the degree,
edge set, and distance metric all refer to the same graph.

The work is relevant to distributed algorithms and graph labeling because it
connects the optimal integer storage budget with geometrically bounded,
recognizable cells and advice-first decoding. Positional coding, counting,
Voronoi partitions, and almost-balanced orientation are established tools;
the submission does not claim those tools as new individual results.
The arithmetic and codec endpoints document the budget and noncircular
interface used by the principal reconstruction theorem. Formal notability
review is a separate Palomar decision.

## Selected formal scope

[Challenge.lean](Challenge.lean) imports only pinned Mathlib. Its definitions
and eight propositions are independent of this proof library.
[Solution.lean](Solution.lean) proves the same declarations and never imports
Challenge. [DECLARATIONS.md](DECLARATIONS.md) maps each result to its proof.

The selected results establish:

- the explicit cubic and general odd-degree storage inequalities;
- an advice reader and payload reader whose roundtrips are simultaneous,
  with zero reserved exactly for the root;
- the integer counting lower bound on complete graphs, even for a centralized
  decoder;
- existence of a separated nearest-root partition with unique ownership,
  bounded size and radius, and cell-contained shortest paths;
- bounded cells on arbitrary labels, including uncovered or malformed inputs,
  with nonempty cells exactly at markers and nonzero nonroot storage symbols;
- stability of the complete truncated cell under radius-`2R` marker agreement,
  even when the global marker sets differ;
- graph-native marker reconstruction for all sufficiently separated root
  sets and every advice assignment satisfying the boundary outdegree bound,
  with explicit ordered packet recovery of that advice from the same labels,
  together with conditional fixed-marker label locality of the **same decoder**
  within physical radius `(4r+1)T+8r+2`.

The complete development includes 15 supporting modules under
[LocalDecompression](LocalDecompression), including canonical graph edges,
parallel-edge pairing, the residual simple quotient, orientation lifting,
actual vertex layouts, marker recovery, ordered packet reading, virtual
padding, and fixed-marker decoder locality. These retained proofs are not
replaced by assumptions merely because they are outside the comparison list.

## Exact limits of the formal theorem

`BalancedBoundaryAdvice` requires only the sufficient inequality
`2 * outgoing <= boundary + 1` for each cell. It says nothing about the input
edge labels or their recovery. The graph reconstruction theorem is
conditional on that orientation property; it does not prove the existence
of a one-bit distributed orientation algorithm. The library separately
proves how the bound follows from the corresponding residual-simple-quotient
bound by canonically pairing parallel edges.

[Balliu et al.'s full version](https://arxiv.org/abs/2405.04519v2), Appendix B,
Corollary 15, supplies the orientation theorem used by the manuscript.
It is a documented external mathematical dependency, never a Lean axiom.
Their marker, clustering, and ordered-storage predecessors are credited in
Appendices C.1 and E; those general methods are not claimed as novel here.

The selected graph theorem combines correctness and locality of one decoder;
these are not statements about independently chosen functions. `packetAdvice`
is a specified arithmetic reader, not an existential function chosen to make
the roundtrip hold. Every covering radius gives the correct supplied advice
on the encoder's labels. This verifies the stored metadata along with the
payload; it does not require the recovered edge bits in order to read advice.
`CellQuotient` has an edge exactly when two distinct cells have a physical
crossing edge.
`CellOrientationLocal` requires orientation outputs to agree when all advice
within a radius-`T` quotient walk agrees. It assumes neither recovery nor
locality of the final decoder. Root coverage bounds each cell's radius by
`2r` and every quotient edge's physical length by `4r+1`, yielding the displayed
physical decoding radius. The partition theorem supplies coverage with
`r = 16(k+1)`.

The assembled decoder's selected label locality fixes the physical topology
and the marker set. Its existential quantifier permits a topology-specific
function; this extensional theorem does not rule out global precomputation
or supply a single operational algorithm for all graphs. Separate bounded-cell
and packet results permit changes
of marker sets on a fixed connected graph. Those results do not constitute
a uniform synchronous machine across changing quotient topologies.
The published algorithm's operational simulation and totalization, and the
final assembly over mixed small and large components, remain written
arguments. Small-component codecs and recognition are present in the library,
but selecting their ingredients would not close that missing assembly.

Natural graph distance is used only with explicit connectedness in these
geometric results. Linear orders fix deterministic storage ordering;
injective natural-number identifiers fix distance ties. The manuscript uses
identifier-induced orders. The interface permits these two fixed orders to
be supplied independently.

## Build and submission

From this directory, with [Lean installed through elan](https://github.com/leanprover/elan):

```sh
lake exe cache get
lake build
```

`lean-toolchain` and `lake-manifest.json` pin the compiler and all dependencies.
The optional cache download does not change the dependency revisions. The
build includes the complete library, independent statement definitions,
Solution, and Challenge. Challenge's intentional eight `sorry` placeholders
are the unproved tasks presented for comparison and are never proof
dependencies. No proof source uses `sorry` or an added axiom.

[comparator.json](comparator.json) selects the eight names with NanoDa enabled
and permits only `propext`, `Quot.sound`, and `Classical.choice`.
[formalization.yaml](formalization.yaml) uses Palomar's v0.4 metadata format.
The submission project path is `zenodo-23346565/palomar`.
Build success and local rendering/metadata checks do not guarantee service
acceptance, notability approval, or independent human review.
The repository's [local verification workflow](../../LOCAL-VERIFICATION.md)
runs the official metadata/source checks, fresh Lean replay, independent
Comparator kernels and sanitized rendering. The supplied finite experiment
can be reproduced with `python3 experiments/check_invariants.py`; it checks
160 packets and 16 graph/identifier fixtures, without implementing the
external orientation algorithm.

## Authorship and automation

Lennart Rudolph is the sole human author and responsible maintainer.
The supplied manuscript and proofs disclose extensive OpenAI ChatGPT/Codex
assistance. Codex also prepared this independent interface, strengthened its
selected graph statements, and performed local verification and adversarial
review. Automated review is not independent human mathematical review.
Lean sources and repository scaffolding use the [MIT license](LICENSE).
