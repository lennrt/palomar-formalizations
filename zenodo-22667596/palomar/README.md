# Short-Cycle Decompositions and Full Zombie Damage in Cubic Graphs

Lennart Rudolph <a href="https://orcid.org/0009-0009-0198-085X"><img src="https://orcid.org/sites/default/files/images/orcid_16x16.png" alt="ORCID" width="16" height="16"></a>

Release 1.0.0 · 9 September 2026 · Lean 4.32.0

This self-contained Lean project includes the full one-zombie damage game and
the complete proof of Randy Davila’s Conjecture 24. For every finite simple
connected bridgeless cubic graph $G$ with $n\geq10$ vertices,

$$
\operatorname{zdmg}(G)=n.
$$

The survivor can force this damage within $2n(n+1)$ survivor moves, against
every initial zombie position and every legal geodesic reply. The proof also
gives the complete characterization: a connected bridgeless cubic graph has
full damage exactly when it is not isomorphic to $K_4$, $K_{3,3}$, the
triangular prism or the cube. No classification, routing or initialization
assumption is left to the caller.

Randy Davila introduced the zombie damage number and posed Conjecture 24 in
[The Zombie Damage Number of a Graph](https://arxiv.org/abs/2607.16382v1).
Lennart Rudolph developed this proof and formalization with the AI assistance
disclosed below. The associated paper and artifacts have DOI
[10.5281/zenodo.22667596](https://doi.org/10.5281/zenodo.22667596).

## Read the proof and game

- [Conjecture 24 as a numerical equality](ZombieMain/NumericalConjecture.lean).
- [Complete main proof and the explicit move bound](ZombieMain/MainTheorem.lean).
- [The 39 selected statements and their definitions](Challenge.lean).
- [Game rules, strategies and damage](GAME.md), with direct links to their definitions.
- [Source attribution](SOURCE_THEORY.md) and [selected declaration map](DECLARATIONS.md).

The numerical damage value is defined from forceable scores. Its positive
thresholds, its equivalence with eventual forcing, and its full-damage endpoint
are proved in [GameValue.lean](ZombieMain/GameValue.lean). Thus the numerical
conjecture is connected to the actual game rather than introduced as a new
meaning for the full-damage predicate.

The proof passes from local graph structure to a strategy on every graph in
the stated class. The four-port inequality and short-cycle classification
describe the components between clean edges; metric exit and target routes
then transfer from those components to the ambient graph and compose into
the bounded full-damage strategy. Explicit strategies on prisms and Möbius
ladders and traps in the four exceptions complete the characterization.
The selected game-value and normalization lemmas connect that strategy to
Davila's numerical parameter and original rules. The boundary and expansion
corollaries record consequences of the same decomposition, while recurrent
coverage strengthens the strategy's behavior beyond a single tour.
These results concern extremal damage in geodesic pursuit and the short-cycle
structure of cubic graphs: an exact all-order game classification, an explicit
worst-case move bound and safe strategies that repeatedly cover the graph.

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan), then run from
this directory:

```sh
lake exe cache get
lake build
python3 scripts/verify.py
```

The cache command is optional. If the cache host is unavailable, `lake build`
builds the pinned dependencies from source; this takes longer. The committed
manifest pins Mathlib and its dependencies to immutable commits. No adjacent
project or prebuilt project object files are required. The Python scripts
require Python 3.11 or later.

For the independent Comparator and NanoDa checks, install Git, Cargo and Go,
then run:

```sh
python3 scripts/verify-comparator.py
```

The script obtains and builds the recorded verification tools, requires the
real Landrun sandbox, and runs both the 39-declaration pursuit comparison and
the original 24-declaration regression comparison. The latter includes two
supplementary sensing results and is not the Palomar submission selection. Local logs
go under `.verification/`. See [VERIFICATION.md](VERIFICATION.md) for the checked
scope and [SUBMISSION.md](SUBMISSION.md) for the Palomar entry point.

All 135 supplied library source files are preserved byte-for-byte: the original
132-file development plus its three numerical damage-value modules.
The new [presentation wrappers](PalomarWrappers.lean) directly apply 13 original
theorems using four transparent helpers, avoiding Palomar's known renderer
type-alias issue. The [selection map](verification/selection-map.json) records
the 39 selected results: 12 wrappers and 27 original names. All 13 wrappers
remain proved in the library. No mathematical statement is weakened. The
axiom audit checks all 263 supplied roots plus these 13 wrappers.
The deliberate statement holes are confined to `Challenge.lean` (39
selections) and the auxiliary `GameChallenge.lean` (24 additional comparison
statements). The main Challenge imports only Std and pinned Mathlib; no proved
local theorem or local definition is imported. Neither Challenge is imported
by the proof. The only allowed axioms are `propext`,
`Quot.sound` and `Classical.choice`.

## Authorship, AI assistance and scope

OpenAI ChatGPT and OpenAI Codex (Astra) assisted with research, formalization,
verification, writing and release preparation. Anthropic Fable 5.1 assisted in
adversarial reviews, as reported by the author. Lennart Rudolph is the author
of this formalization; no AI is an author. AI-produced computational reviews
are supplementary evidence in the associated artifacts, not independent
human peer review.

The project formalizes the game rules, payoff and strategy semantics together
with the stated main and supporting results. It does not claim to formalize
every theorem in Davila’s paper or to provide an executable optimal-value
solver for every finite graph. Known closed-graph classification and
ring-of-diamonds sensor results are credited in [SOURCE_THEORY.md](SOURCE_THEORY.md).

The distance-shell involution obstruction, diamond central-pair sensor lemma
and ring sensor-cardinality bound are supplementary library results, not
part of the selected pursuit package. Their proofs remain included and
audited; their statements and sensing-only definitions are not in the main
Challenge. [DECLARATIONS.md](DECLARATIONS.md) identifies this boundary exactly.

Theorem 13's degree-independent arbitrary-game
interface is written only; the entire cubic-game application is formalized
directly. Remark 19's ring-structure connection to recurrent coverage is also
written only; its involution obstruction and sensor-cardinality bound are
formalized as unselected supplementary material. Computational census counts and historical regressions are tests,
not extra selected theorem claims.

The Challenge exposes the 39 selected results and their actual graph/game
definitions. [VERIFICATION.md](VERIFICATION.md) records the checked size,
rendering evidence and the distinction between historical and current checks.

The source and documentation are [MIT licensed](../../LICENSE). See
[CITATION.cff](CITATION.cff) for citation metadata.
