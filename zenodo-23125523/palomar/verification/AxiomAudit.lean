module

public import ShellObservability

@[expose] public section

-- Generic report faults and the complete population model.
#print axioms ShellObservability.correctsBlocks_iff
#print axioms ShellObservability.toleratesErasures_iff
#print axioms ShellObservability.correctsBags_iff_tradeWeight
#print axioms ShellObservability.erasureBags_iff_tradeWeight
#print axioms ShellObservability.mass_two_iff_pairConfig

-- Literal geometry, actual-grid adapter, all-order extremal statements.
#print axioms ShellObservability.skinny_trade_detector
#print axioms ShellObservability.parallelogram_detected
#print axioms ShellObservability.skinny_trade_moment_detector
#print axioms ShellObservability.parallelogram_moment_detected
#print axioms ShellObservability.corner_collision_hasIntervalDetector
#print axioms ShellObservability.grid_cross_sensor_lower_bound_refined
#print axioms ShellObservability.gridRobust_iff_intervalCuts
#print axioms ShellObservability.OrderedStars.splitPlacement_interval_cut_ge_two
#print axioms ShellObservability.GridTheorems.exact_corner_grid_robust_minimum
#print axioms ShellObservability.GridTheorems.all_orders_grid_robust_bounds
#print axioms ShellObservability.gridMomentRobust_iff_intervalCuts
#print axioms ShellObservability.gridMomentRobust_iff_gridRobust

-- Actual cube distances, general construction, and exact antipodal condition.
#print axioms ShellObservability.Hypercube.cube_dist_eq_hamming
#print axioms ShellObservability.Hypercube.exists_odd_graph_bisector
#print axioms ShellObservability.Hypercube.card_oddWords
#print axioms ShellObservability.Hypercube.evenPrefix_balances
#print axioms ShellObservability.Hypercube.evenPrefix_distance
#print axioms ShellObservability.Hypercube.evenPrefix_orthogonal_iff
#print axioms ShellObservability.Hypercube.evenPrefix_unique_orthogonal_partner
#print axioms ShellObservability.Hypercube.prefixEqualizer_isDistanceEqualizer
#print axioms ShellObservability.Hypercube.prefixEqualizer_card
#print axioms ShellObservability.Hypercube.infinite_counterexample_family
#print axioms ShellObservability.Hypercube.dimension_twelve_counterexample
#print axioms ShellObservability.Hypercube.equalizer_contains_parity_class
#print axioms ShellObservability.Hypercube.odd_union_equalizer_iff_antipodal_cover

-- Concrete bishop graph and full even-board theorem.
#print axioms ShellObservability.BishopParity.two_domination_lower
#print axioms ShellObservability.BishopParity.outerColumns_twoDominates
#print axioms ShellObservability.BishopParity.exact_two_domination

-- Two concrete Petersen graphs, with explicit graph-definition bridges.
#print axioms ShellObservability.no_single_defect
#print axioms ShellObservability.Petersen.domination_iff_graph
#print axioms ShellObservability.Petersen.exact_domination
#print axioms ShellObservability.Petersen.conjectured_value_false
#print axioms ShellObservability.PetersenSecond.domination_iff_graph
#print axioms ShellObservability.PetersenSecond.exact_domination
#print axioms ShellObservability.PetersenSecond.conjectured_value_false

-- Real-valued fractional optimization faces, not only integer witnesses.
#print axioms ShellObservability.FractionalCounterexample.graph_connected
#print axioms ShellObservability.FractionalCounterexample.load_eq_closed_sum
#print axioms ShellObservability.FractionalCounterexample.counterexample

-- Rectangular, semiring-valued certificates for literal uncovered supports.
#print axioms ShellObservability.residual_syndrome
#print axioms ShellObservability.packing_defect_syndrome
#print axioms ShellObservability.no_packing_with_defect_card
#print axioms ShellObservability.regular_packing_count
#print axioms ShellObservability.syndrome_packing_bound
#print axioms ShellObservability.syndrome_excludes_packing_card
