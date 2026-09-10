# Formal game and numerical value

The mathematical source is Randy Davila’s Definition 1 in
[arXiv:2607.16382v1](https://arxiv.org/abs/2607.16382v1). The Lean implementation
and proofs are by Lennart Rudolph, with the disclosed AI assistance.

| Rule or concept | Formal definition or result |
|---|---|
| A simple undirected graph | `ZombieDamage.Graph` in [Graph.lean](ZombieDamage/Graph.lean) |
| Actual walks, shortest distance, every distance-decreasing zombie reply | `Graph.Walk`, `Distance`, `GeodesicReply` in [Graph.lean](ZombieDamage/Graph.lean) |
| Both positions and the set of distinct damaged vertices | `FullGame.State` in [FullGame.lean](ZombieDamage/FullGame.lean) |
| The zombie chooses first, the survivor answers, then the zombie moves first | `initial`, `FullDamageWithin` in [FullGame.lean](ZombieDamage/FullGame.lean) |
| Survivor edge moves and passes | `LegalSurvivor` in [FullGame.lean](ZombieDamage/FullGame.lean) |
| Capture and adversarial choice among all legal zombie replies | `ForcesWithin.zombie`, `ForcesWithin.survivor` in [FullGame.lean](ZombieDamage/FullGame.lean) |
| Damage credited on departure after a survived zombie turn; passes credit the same source | `State.survivorTo` and `pass_damages_source` in [FullGame.lean](ZombieDamage/FullGame.lean) and [OriginalGameChecks.lean](ZombieDamage/OriginalGameChecks.lean) |
| Every neighboring survivor destination, including the occupied zombie vertex | `PermissiveForces` in [OccupiedVertexNormalization.lean](ZombieDamage/OccupiedVertexNormalization.lean) |
| Equivalence of the permissive and normalized rules for every damaged-set objective | `PermissiveForces.iff_normalized` in [OccupiedVertexNormalization.lean](ZombieDamage/OccupiedVertexNormalization.lean) |
| Bounded contingent strategies and sequential composition | `ForcesWithin`, `ForcesWithin.bind` in [FullGame.lean](ZombieDamage/FullGame.lean) |
| Eventual forcing and its finite-graph equivalence with bounded forcing | `ForcesEventually`, `ForcesEventually.bounded`, `fullDamage_iff_eventual` in [EventualGame.lean](ZombieDamage/EventualGame.lean) |
| Number of distinct damaged vertices and forceable score thresholds | `damageCount`, `CanForceDamage` in [GameValueDefinitions.lean](ZombieMain/GameValueDefinitions.lean) |
| Davila’s numerical zombie damage number | `zombieDamageNumber` in [GameValueDefinitions.lean](ZombieMain/GameValueDefinitions.lean) |
| Positive threshold characterization, eventual-score equivalence, and full-damage equality | [GameValue.lean](ZombieMain/GameValue.lean) |
| Actual adjacency of the Mathlib graph, without replacing the graph by a game premise | `gameGraph` in [ShortCycles.lean](ZombieMain/ShortCycles.lean) |
| A fixed safe controller revisiting every vertex beyond every finite time | [RecurrentDefinitions.lean](ZombieMain/RecurrentDefinitions.lean) and [RecurrentCoverage.lean](ZombieMain/RecurrentCoverage.lean) |

An immediate-capture move onto the zombie damages the departure vertex and
ends play. Replacing that move by a pass achieves the same damaged set within
the same move budget. This is a proved normalization for damage-only
objectives, at every state and phase; it does not assert equivalence for
objectives depending on the final positions.

`CanForceDamage G k` includes the graph-order bound and a strategy for each
initial zombie vertex. The zombie choices are universally quantified inside
each strategy. The numerical value is the largest forceable score, with zero
as the default payoff when no distinct starting pair exists. Bounding scores
by the graph order prevents empty-graph quantifier vacuity from creating
positive scores. On a nonempty graph the full-damage endpoint is equivalent to
the numerical equality with the graph order. Conjecture 24 has at least ten
vertices, so the endpoint lemma adds no hypothesis to that result.

The numerical value uses classical propositions and is noncomputable. Its
formal role is to state and prove the mathematical value; the associated
computational supplement contains finite game evaluators separately.
