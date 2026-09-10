# Selected declarations

The root `comparator.json` selects the 39 pursuit and short-cycle results below
for one Palomar entry. The table links their original proofs; 27 selections use
those original names, while 12 use definitionally identical `PalomarVerified` interfaces from
[PalomarWrappers.lean](PalomarWrappers.lean). The complete exact original-to-selected
mapping is in [selection-map.json](verification/selection-map.json). Three
supplementary sensing results are not selected; their unchanged proofs are
listed separately below. Every selected proof is supplied by `Solution`; all proof source is in this
repository. The source theory and prior-work credits are in
[SOURCE_THEORY.md](SOURCE_THEORY.md).

| Declaration and source | Meaning |
|---|---|
| [`ZombieMain.full_damage_within_iff`](ZombieMain/MainTheorem.lean#L64) | Four-exception characterization with the explicit move bound |
| [`ZombieMain.full_damage_iff`](ZombieMain/MainTheorem.lean#L78) | Four-exception characterization for full damage |
| [`ZombieMain.davila_conjecture_24`](ZombieMain/MainTheorem.lean#L88) | Complete Conjecture 24 with the explicit move bound |
| [`ZombieMain.full_damage_of_clean_edge`](ZombieMain/CleanFullDamage.lean#L10) | Full damage from an actual clean edge |
| [`ZombieMain.recurrent_coverage_of_clean_edge`](ZombieMain/RecurrentCoverage.lean#L32) | Fixed-controller infinite safe recurrent coverage |
| [`ZombieMain.mobius_recurrent_coverage`](ZombieMain/PeriodicCoverage.lean#L69) | Infinite safe recurrent coverage on Möbius ladders |
| [`ZombieMain.four_boundary_edges`](ZombieMain/Boundary.lean#L51) | At most four exterior edges of a short-cycle union |
| [`ZombieMain.short_component_expansion`](ZombieMain/Expansion.lean#L48) | Expansion bound for a short-cycle component |
| [`ZombieMain.four_port_principle`](ZombieMain/CycleCapacity.lean#L123) | Universal four-port inequality |
| [`ZombieMain.cycle_union_classification`](ZombieMain/Classification.lean#L62) | Closed and at-least-two-port classification, with an explicit one-port alternative |
| [`ZombieDamage.Graph.geodesicReply_iff_commonNeighbor`](ZombieDamage/Graph.lean#L69) | Geodesic replies at distance two are precisely common neighbors |
| [`ZombieDamage.Graph.cleanEdge_forces_reply`](ZombieDamage/Graph.lean#L99) | A clean edge forces the unique geodesic reply |
| [`ZombieDamage.Graph.short_twoStep_closed`](ZombieDamage/Graph.lean#L126) | Internal two-step replies stay in the short-edge graph |
| [`ZombieDamage.Verified.finite_component_routing`](ZombieDamage/Routing.lean#L487) | All prescribed exits and targets in the five finite gadgets |
| [`ZombieDamage.OpenStrip.metric_exit_contract`](ZombieDamage/OpenStripMetricContract.lean#L10) | All-parameter open-strip exit routing |
| [`ZombieDamage.OpenStrip.metric_target_contract`](ZombieDamage/OpenStripMetricContract.lean#L42) | All-parameter open-strip target routing |
| [`ZombieDamage.TriangleRoute.prescribed_exit`](ZombieDamage/TriangleRoute.lean#L31) | Triangle prescribed-exit routing |
| [`ZombieDamage.TriangleRoute.target_route`](ZombieDamage/TriangleRoute.lean#L59) | Triangle target routing |
| [`ZombieDamage.DiamondRoute.target_route`](ZombieDamage/DiamondRoute.lean#L75) | Diamond target routing |
| [`ZombieDamage.Task.fullGame_metricForcesWithin`](ZombieDamage/FullGameConverse.lean#L60) | Full-game strategies imply the faithful local metric contract |
| [`ZombieDamage.FullGame.fullDamage_iff_eventual`](ZombieDamage/EventualGame.lean#L84) | Bounded and eventual full-damage semantics agree |
| [`ZombieDamage.Graph.MetricCertificate.distance`](ZombieDamage/FiniteMetric.lean#L44) | Checked metric values equal actual shortest-walk distance |
| [`ZombieDamage.Task.metricForcesWithin_fullGame`](ZombieDamage/FullGameBridge.lean#L39) | Local metric strategies transfer to the full game |
| [`ZombieDamage.FullGame.fullDamage_of_contract`](ZombieDamage/Covering.lean#L48) | Initialization and routing compose to give full damage |
| [`ZombieDamage.FullGame.universal_vertex_not_fullDamage`](ZombieDamage/OriginalGameChecks.lean#L27) | A universal vertex prevents full damage |
| [`ZombieDamage.FullGame.pass_damages_source`](ZombieDamage/OriginalGameChecks.lean#L38) | Passing credits the current departure source |
| [`ZombieDamage.CycleGame.full_damage`](ZombieDamage/CycleGame.lean#L77) | Full damage on cycles of length at least five; Davila Theorem 6 |
| [`ZombieDamage.MobiusGame.full_damage`](ZombieDamage/MobiusGame.lean#L102) | Full damage on Möbius ladders with parameter at least four |
| [`ZombieDamage.PrismGame.full_damage`](ZombieDamage/PrismGame.lean#L265) | Full damage on prisms with rim length at least five |
| [`ZombieDamage.Exceptions.not_full_damage`](ZombieDamage/ExceptionTraps.lean#L48) | Explicit traps prevent full damage in the four exceptions |
| [`ZombieDamage.GraphIso.fullDamage_iff`](ZombieDamage/Isomorphism.lean#L123) | Graph isomorphisms preserve full damage |
| [`ZombieDamage.ShortComponentModel.metricForcesWithin_ambient`](ZombieDamage/Ambient.lean#L131) | Faithful component models transfer to the actual ambient graph |
| [`ZombieDamage.FullGame.PermissiveForces.iff_normalized`](ZombieDamage/OccupiedVertexNormalization.lean#L65) | Every damaged-set objective is unchanged by occupied-vertex normalization |
| [`ZombieDamage.FullGame.fullDamage_iff_permissive`](ZombieDamage/OccupiedVertexNormalization.lean#L74) | Original permissive and normalized full-damage rules agree |
| [`ZombieDamage.FullGame.zombieDamageNumber_le_card`](ZombieMain/GameValue.lean#L42) | The numerical value is at most the graph order |
| [`ZombieDamage.FullGame.canForceDamage_iff_le_number`](ZombieMain/GameValue.lean#L51) | Positive score thresholds are forceable exactly below the value |
| [`ZombieDamage.FullGame.canForceDamage_iff_eventual`](ZombieMain/GameValue.lean#L73) | Bounded and eventual score guarantees agree on finite graphs |
| [`ZombieDamage.FullGame.zombieDamageNumber_eq_card_iff`](ZombieMain/GameValue.lean#L97) | The numerical endpoint equals the full-damage predicate |
| [`ZombieMain.davila_conjecture_24_damage_number`](ZombieMain/NumericalConjecture.lean#L10) | Conjecture 24 as the numerical equality zdmg(G)=n |

`Challenge` independently states all 39 selected results with their necessary definitions;
it imports only Std and pinned Mathlib, never a local proof or definition module.
Every selected result is an explicit documented declaration in that file.
`GameChallenge` separately reconstructs the original 24 game statements using
only Std. Its additional comparison is retained as a regression check, not a
second submission configuration; it includes two supplementary sensing results.
The two normalization results quantify over the actual game definitions.

## Renderer-compatible names

The following original basenames are selected as `PalomarVerified.<basename>`:

- `full_damage_within_iff`, `full_damage_iff`, `davila_conjecture_24`,
  `full_damage_of_clean_edge`, `recurrent_coverage_of_clean_edge`;
- `four_boundary_edges`, `short_component_expansion`, `four_port_principle`,
  `cycle_union_classification`, `davila_conjecture_24_damage_number`;
- `metric_exit_contract`, `metric_target_contract`.

Four transparent helpers spell ordinary graph degree, a diamond vertex pair,
and equality/inequality decisions on ports. Each wrapper is proved by a direct
`exact` application of its original theorem. This handles the known
[Palomar core-notation alias issue #134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134)
without changing hypotheses, conclusions, game rules or original proof sources.

## Supplementary library results — not selected

These results are outside the main pursuit selection and its Challenge. They
remain in the complete source distribution and in the 276-root axiom audit.
The retained `central_pair_sensor` wrapper is the thirteenth wrapper in the
library, but is not one of the twelve selected interfaces above.

| Original declaration and source | Scope |
|---|---|
| [`ZombieMain.diamond_ring_sensor_bound`](ZombieMain/SensorCounting.lean#L9) | Attributed ring sensor-cardinality lower bound; supplementary to paper Remark 19 |
| [`ZombieDamage.Graph.involution_blocks_recovery`](ZombieDamage/Observation.lean#L74) | Elementary involution collision obstructing distance-shell recovery |
| [`ZombieDamage.DiamondRing.central_pair_sensor`](ZombieDamage/DiamondRing.lean#L97) | Every central diamond pair needs a sensor; also proved as `PalomarVerified.central_pair_sensor` |

The known ring sensor bound is credited to Sardar et al.; these sensing
statements do not serve as premises of the claimed pursuit characterization
or as additional research claims in this Comparator selection.
