# Selected declarations

[comparator.json](comparator.json) selects the following 14 declarations in
six mathematical groups. Every selected name has the prefix `PalomarResults`.
[Challenge.lean](Challenge.lean) reconstructs their required definitions using
Mathlib and supplies deliberate statement holes. [Solution.lean](Solution.lean)
proves each interface by applying the linked original theorem; it does not
import the Challenge. The substantive library is included in this project.

| Selected declaration | Plain-language statement and original proof |
|---|---|
| `Grid.gridRobust_iff_intervalCuts` | With four corners present, one-erasure recovery of all populations of mass at most two is equivalent to meeting every equal-length interior interval cut twice. [GridRecovery.lean](ShellObservability/GridRecovery.lean), `ShellObservability.gridRobust_iff_intervalCuts`. |
| `Grid.gridMomentRobust_iff_gridRobust` | Full corner reports and scalar distance sums at all other sensors have exactly the same one-erasure recovery property as full shell reports everywhere. [GridMomentRecovery.lean](ShellObservability/GridMomentRecovery.lean), `ShellObservability.gridMomentRobust_iff_gridRobust`. |
| `Grid.grid_robust_sensor_lower_bound` | Every robust square-grid placement with positive interior size `m` satisfies `3m < 2|S|`, without a corner assumption. [GridTheorems.lean](ShellObservability/GridTheorems.lean), corresponding theorem. |
| `Grid.exact_corner_grid_robust_minimum_all` | For every interior size `m >= 1`, constructs a corner-containing robust placement of size `(3m+10)/2` using natural-number division and proves every such placement has at least that size. This is `ceil((3m+9)/2)`. [GridAllOrders.lean](ShellObservability/GridAllOrders.lean), corresponding theorem. |
| `Hypercube.infinite_counterexample_family` | For every `q >= 3`, an actual-distance equalizer of `Q_(4q)` has size strictly below the conjectured `2^(4q-1)+2^(2q-2)`. The proof uses the explicit prefix construction. [HypercubeCounterexample.lean](ShellObservability/HypercubeCounterexample.lean), corresponding theorem. |
| `Hypercube.odd_union_equalizer_iff_antipodal_cover` | An odd-parity class augmented by `T` is an actual-distance equalizer precisely when every even antipodal pair is met at an endpoint or has a selected middle-distance vertex. [HypercubeReduction.lean](ShellObservability/HypercubeReduction.lean), corresponding theorem. |
| `Hypercube.equidistant_dimension_within_one` | In every positive dimension `4q`, gives an equalizer of size `2^(4q-1)+2q` and proves every equalizer has at least `2^(4q-1)+2q-1` vertices. [CubeLowerBound.lean](ShellObservability/CubeLowerBound.lean), corresponding theorem. |
| `Bishop.exact_two_domination` | On every positive even bishop board of side `N+1`, constructs an ordinary 2-dominating set of size `2(N+1)` and proves the matching lower bound. [BishopUpper.lean](ShellObservability/BishopUpper.lean), `ShellObservability.BishopParity.exact_two_domination`. |
| `Petersen11.exact_domination` | Gives a 16-vertex double-total-dominating set in `P(11,4)` and proves every such set has at least 16 vertices. [PetersenCounterexample.lean](ShellObservability/PetersenCounterexample.lean), `ShellObservability.Petersen.exact_domination`. |
| `Petersen16.exact_domination` | Gives a 24-vertex double-total-dominating set in `P(16,5)` and proves every such set has at least 24 vertices. [PetersenSecond.lean](ShellObservability/PetersenSecond.lean), `ShellObservability.PetersenSecond.exact_domination`. |
| `Fractional.graph_connected` | The explicit six-vertex graph in the next statement is connected. This qualifies the counterexample rather than constituting a separate result group. [FractionalCounterexample.lean](ShellObservability/FractionalCounterexample.lean), corresponding theorem. |
| `Fractional.counterexample` | Its real-valued optimal fractional domination and packing faces intersect with neither containing the other, but no vertex is zero on both complete faces. [FractionalCounterexample.lean](ShellObservability/FractionalCounterexample.lean), corresponding theorem. |
| `Rectangle.gridRobust_iff_intervalCuts` | The four-corner interval-cut characterization for rectangular grids, with actual distance-bag recovery after one erasure. [RectangleRecovery.lean](ShellObservability/RectangleRecovery.lean), `ShellObservability.Rectangle.gridRobust_iff_intervalCuts`. |
| `Rectangle.exact_long_rectangle_robust_minimum` | For positive `N <= M` with `5N <= 3M`, the exact four-corner robust sensor minimum on the `(M+2)` by `(N+2)` grid is `2N+4`, including construction and lower bound. [RectangleTheorems.lean](ShellObservability/RectangleTheorems.lean), corresponding theorem. |

## Retained, unselected development

The selection omits redundant special cases, construction-cardinality helpers,
prefix-distance formulas, and secondary three-word/four-word geometry. It also
omits standalone additive-field, tensor-moment, Boolean interpolation, and
general syndrome statements. All their original proved modules remain in
the library and the full-development audits; they are not deleted or turned
into assumptions. Known algebraic ingredients are not advertised as separate
original research results by the selection.

The paper's stronger unrestricted grid lower bound and exact finite
hypercube values are outside this selected formal scope. The general moment
capacity and sharp report-distance theorems also require paper-level bridges
not supplied by selecting the supporting tensor or interpolation lemmas.
[README.md](README.md#coverage-limits) describes these limits, and
[formalization.yaml](formalization.yaml) records the source relationships.
