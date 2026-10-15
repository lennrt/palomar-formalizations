# Optimal Local Decompression: Uniform Finite-View Reduction

Lennart Rudolph · [10.5281/zenodo.23346565](https://doi.org/10.5281/zenodo.23346565)

An encoder sees a graph and an arbitrary subset of its edges, and stores a
fixed number of bits at each vertex. A local decoder must recover each
incident edge bit from nearby topology and stored labels. For odd maximum
degree `2k-1`, counting over the full bounded-degree graph class requires at least `k` bits
per vertex. The paper
constructs a constant-round scheme meeting that budget.

The principal selected Lean theorem proves a **uniform finite-view reduction**
for sufficiently large connected graphs. Given one total finite-view rule
with the stated one-bit orientation guarantee, it constructs one decoder
family before graph order, topology, markers, advice, or payload are chosen.
Every eligible graph admits an encoder using exactly the `2^k`-symbol vertex
alphabet. The **same decoder** has a degree-only physical radius on every
label assignment, including malformed inputs and changes to graph topology
and marker pattern. The external orientation theorem remains an explicit
premise; this is not a claim that the entire paper or an executable LOCAL
machine has been formalized.

## Research motivation

[Balliu et al., Distributed Computation with Local Advice](https://doi.org/10.4230/LIPIcs.DISC.2025.12),
Section 1.8, Question 4, asks whether cubic graphs admit two-bit local
decompression. Their earlier general construction needs one extra bit above
the counting budget. The manuscript amortizes marker and orientation data
over bounded connected cells. Reserving zero as a marker leaves `2^k-1`
nonzero symbols. Their storage rate exceeds `(2k-1)/2` bits per vertex, so
large enough cells can hold their owned edge bits together with one advice bit.

A global packing argument alone would not settle the local problem: a decoder
might secretly depend on the entire graph or on an uncommunicated partition.
Here the encoder and decoder are connected to explicit finite neighborhood
records. Advice is read from the cell packet **before** computing orientation
or payload positions. Parallel crossing edges are paired canonically, with
only a possible unpaired edge using the simple residual quotient's advice.
Padding makes the oracle's public order and exact degree independent of the
number of markers. This explains why the reduction addresses local storage,
beyond its capacity inequality and elementary counting lower bound.

The upper bound for large connected graphs matches the counting lower bound
for the full graph class. The selected complete-graph lower bound does not
itself prove optimality within the restricted large-connected class.

The contribution is relevant to distributed algorithms and graph labeling.
Positional coding, counting, Voronoi partitions, and almost-balanced
orientations are established ingredients and are credited as such.
Palomar's editorial notability decision is separate from proof verification.

## Selected formal scope

[Challenge.lean](Challenge.lean) independently defines the mathematical
interface using only pinned Mathlib. [Solution.lean](Solution.lean) proves
the same eight selected declarations without importing Challenge.
[DECLARATIONS.md](DECLARATIONS.md) maps each endpoint to its substantive proof.
The endpoints cover the storage budget, independent advice/payload codec,
counting lower bound, existence and geometry of bounded cells, arbitrary-label
cell stability, and the uniform reconstruction reduction.

For `k >= 2`, write

```text
r = 16(k+1),  R = 2r,
D = (2k-1)(2k)^R,
K = (3R+2) + (2R+1)(T(D)+1) + 1.
```

`uniformFiniteViewReconstruction` chooses a total decoder family and proves:

- On every connected graph on `Fin n` with `n > 16(k+1)` and degree at most
  `2k-1`, some encoder recovers every edge-bit assignment using `2^k` labels
  per vertex. Either endpoint can query the same recovered edge bit.
- For any two connected graphs on `Fin n`, equal radius-`K` rooted induced
  topology and equal labels there give equal decoder output at the queried
  endpoint pair. This includes nonedges, uncovered vertices, malformed
  packets, and globally different marker sets. No degree, coverage,
  separation, good-advice, or encoder-image condition is needed for this
  locality clause.

The proof constructs separated covering roots, obtains a degree bound for
the residual simple quotient, and applies the oracle premise to a padded
graph of exact order `n+D+1` and degree `D`. It proves that isolated nonroots
and the disjoint dummy clique cannot affect root views. On encoded labels,
the actual bounded packet reader recovers the chosen advice, named crossing
fibers preserve the original parallel-edge ranks, and the total decoder
agrees with the supplied graph encoder. These are proved bridges, not
recovery hypotheses. Arbitrary-input locality is proved independently by
transporting walks, cells, packets, crossing fibers and oracle records
between graphs with the same finite view.

The complete supplied library is retained. The additional modules prove
cross-topology finite-view transport, total named-edge decoding, oracle
padding invariance, exact rank transport, and the assembled uniform reduction.
The earlier fixed-graph `graphMarkerReconstruction` remains proved as a
supporting theorem, including exact marker and packet-advice recovery.

## Exact limits

`GoodOneBitOracle F T` states that the same rule `F` admits a one-bit advice
assignment on every finite graph with the specified exact order, maximum
degree, and polynomial identifier range, making `2*outdegree <= degree+1`.
It concerns only orientations: it assumes no compression, payload recovery,
cell partition, or final decoder locality. `F` receives public `N,D,c`, two
endpoint IDs, and a finite set of records containing IDs, advice bits, and
neighbor-ID sets. Full fringe neighbor records cost one extra virtual round,
which is included in `K`.

The [full version of Balliu et al.](https://arxiv.org/abs/2405.04519v2),
Appendix B, Corollary 15, supplies the external mathematical orientation
result used in the paper. Its algorithm and normalization to this precise
finite-view interface are not proved here. `F` is an arbitrary total Lean
function; its computability is not asserted. The proved finite-view reduction
therefore does not by itself formalize an executable synchronous machine.

The selected reconstruction theorem uses connected graphs on `Fin n`,
canonical identifiers `v.val+1`, and public graph order `n`. It covers large
components; the paper's final assembly over mixed small and large components
is not selected. Supporting geometric and locality results allow more general
ordered vertex types and injective identifiers. Natural distance is used
with explicit connectedness. The conservative radius above equals
`(4r+1)T(D)+10r+4`; it is larger than the paper's stated radius and is not
claimed to be a sharp round bound.

## Build and verification

From this directory:

```sh
lake exe cache get
lake build
```

`lean-toolchain` and `lake-manifest.json` pin Lean and all dependencies.
Challenge's eight intentional `sorry` placeholders are comparison goals and
are never proof dependencies. Proof sources have no placeholders or added
axioms. [comparator.json](comparator.json) enables NanoDa and permits only
`propext`, `Quot.sound`, and `Classical.choice`.

The [local verification workflow](../../LOCAL-VERIFICATION.md) checks source
policy and metadata, builds all targets, replays proofs with fresh Lean and
independent kernels, compares the independently elaborated statements, and
renders/sanitizes the Challenge. GitHub Actions runs the pinned official full
Linux mechanical workflow. These reports identify their exact source
snapshot; local checks are not a hosted editorial acceptance or registration.
The submission project path is `zenodo-23346565/palomar`.

The supplied experiment `python3 experiments/check_invariants.py` checks
160 packets and 16 graph/identifier fixtures. These finite checks supplement
the proofs and do not implement the external orientation algorithm.

## Authorship

Lennart Rudolph is the sole human author and responsible maintainer.
The supplied manuscript and proofs disclose extensive OpenAI ChatGPT/Codex
assistance. Codex added the independent interface, strengthened the uniform
reduction, and performed local verification and adversarial analysis.
Automated review is not independent human mathematical review.
Lean sources and repository scaffolding use the [MIT license](LICENSE).
