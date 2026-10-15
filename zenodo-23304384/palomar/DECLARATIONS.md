# Declaration map

Every compared declaration is in namespace `PalomarResults.LossyShell`, defined
in [Solution.lean](Solution.lean), and independently stated in
[Challenge.lean](Challenge.lean). The canonical source is
[10.5281/zenodo.23252713](https://doi.org/10.5281/zenodo.23252713), manuscript
version 2.0.0 at [record 23304384](https://zenodo.org/records/23304384).
All library proof sources are included locally.

| Selected declaration | Mathematical content and source correspondence | Substantive proof |
| --- | --- | --- |
| `endpoint_trace_equivalence` | Proposition 3.1: report entries are the zero-padded deletion trace; the surviving horizon recovers the trace exactly. Includes zero-valued surviving relays. Does not assert imported complexity bounds. | `LossyShell/Trace.lean`: `legReport_eq_trace_getD`, `trace_eq_map_legReport` |
| `probability_endpoints` | At `p = 0` the law is concentrated at zero; at `p = 1` it is concentrated at the fold. Explains failure of the nondegenerate recovery mechanism at the endpoints. | `LossyShell/Main.lean`: `twoLegLaw_zero`, `twoLegLaw_one` |
| `mean_eq_iff_fold_eq` | Path specialization of Theorem 4.1: equal real means iff equal folds for `p > 0`. It formalizes no arbitrary-tree theorem. | `LossyShell/Main.lean`: `fold_eq_of_twoLegMean_eq`, `twoLegMean_eq_of_fold_eq`; triangular inversion in `Recovery.lean` |
| `legs_eq_of_mean_covariance` | Theorem 5.4: equal mean and covariance of the actual two-leg experiment imply equality up to global exchange. | `LossyShell/Main.lean`: `legs_eq_of_mean_covariance`; polarization in `Moments.lean`, deepest-entry reconstruction in `Recovery.lean` |
| `legs_eq_of_mean_covariance_sparse` | Corollary 5.9: the mean, covariance diagonal, and column of the last nonzero corrected diagonal suffice. All-zero imbalance needs no selected column. At most `2n-1` covariance entries for positive `n`. | `LossyShell/Main.lean`: `legs_eq_of_mean_covariance_sparse`; `Recovery.lean`: `eq_or_eq_neg_of_Qform_sparse` |
| `twoLegLaw_eq_iff` | Theorem 5.4 and its exchange converse: law equality is exactly equality of unordered leg pairs. Uses moments derived from the law and explicit exchange of independent masks. | `LossyShell/Main.lean`: `twoLegLaw_eq_iff`, `legs_eq_of_twoLegLaw`, `twoLegLaw_swap` |
| `variance_sensitive_bounds` | Version 2 sample-analysis components: variance is bounded by `2(2h)^2(1-p^(k+1))`, and the centered-product second moment by `2(2h)^4(1-p^(k+1))`. Not a concentration or estimator-success theorem. | `ShellResearch/FiniteSample.lean`: `report_variance_le`, `centered_product_second_moment_le` |
| `fold_recovery` | Proposition 5.6 / Section 7 deterministic component: the descending rounding equations recover the entire integer fold under explicit weighted mean errors. | `ShellResearch/Pipeline.lean`: `fold_recovery`; `Deterministic.lean`: `rounded_triangular_recovery` |
| `difference_recovery` | Proposition 5.6 / Section 7 deterministic component: the oriented difference recurrence is exact, conditional on the correct deepest coordinate, magnitude, and the specified column errors. | `ShellResearch/Pipeline.lean`: `difference_recovery`; actual `Qform_col_top` identity and triangular rounding |
| `all_length_designed_lower_bound` | Section 7's explicit weaker formal counterpart of Theorem 5.12: at `p=2n/(2n+1)`, every randomized test with both errors at most `δ` needs `N ≥ (n/2) log(1/(2δ))`. Actual masks and reports for every `n ≥ 2` are included. The paper's stronger coefficient and full minimax composition are not asserted. | `ShellSampling/AllLengthLower.lean`: `all_length_designed_lower_bound`, from the four-initial-relay common-event coupling |

The final test has output in `[0,1]`, interpreted as its probability of choosing
the split-side candidate. The two errors are explicit expectations under the
same-side and split-side populations, not assumptions that a minimax theorem
holds. `near_populations_binary` and `near_populations_distinct` prove that the
candidates are genuine distinct binary inputs. Nonnegative normalized mask
weights are established by `roundWeight_nonneg` and `roundWeight_sum`.

## Definitions and comparison independence

The Challenge repeats the concrete population, mask, report, pattern-weight,
mean, second-moment, covariance, landing, and covariance-form definitions.
These are definitions over pinned Mathlib, with no import of this project's
proof library. `imbalanceCovariance` is twice the observed covariance minus
the covariance form of the fold; it is determined after the mean inversion.
The sampling definitions specify the actual binary candidates and product
weights for independent rounds. None assumes reconstruction or a lower bound.

Comparator checks the selected theorem types, including transitive definition
content, against the solution. The ten intended holes are isolated to Challenge;
no solution or supporting module imports it. Library theorems not selected here
remain part of the included development but are not advertised as additional
separate research contributions.
