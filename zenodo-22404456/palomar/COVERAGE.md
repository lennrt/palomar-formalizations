# Statement alignment and scope

Source: public release 1.0.0 of the companion paper, 2026-09-06. All compared declarations
are in `Solution.lean`, namespace `ShellTomography.Verified`.

| Declaration | Paper statement | Exact coverage |
|---|---|---|
| `trade_criterion` | Proposition 1 | Every finite vertex type, supplied sensor, natural observation table and mass bound; bounded-recovery clause. The Lean statement also covers `h = 0`, while the paper states `h ≥ 1`; the extension is immediate because only the zero population has mass zero. |
| `product_kernel` | Theorem 7, equation (3) | Every finite connected pair of simple graphs and labelled factor placement; actual product graph distance; the entire integer kernel slice by slice. Lean also permits an empty sensor-label type, where both invisibility predicates are vacuous. |
| `product_recovery` | Theorem 7 | Equivalence of recovery through every natural mass bound in the factor and full-factor placement. Lean also permits an empty sensor-label type; both sides resolve only the mass-zero domain. |
| `grid_lower_bound` | Lemma 8 | Every natural `n` and every placement with fewer than `n−2` sensors fails recovery through mass two. The paper assumes `n ≥ 3`; for `n < 3`, Lean's truncated subtraction makes the hypothesis `S.card < n−2` impossible, so those cases are vacuous. |
| `grid_kernel_uniform` | Lemma 10 | Every n ≥ 6, every signed integer population, all radii: invisible iff z = Bₙp for a unique integer quadruple. |
| `grid_capacity_uniform` | Theorem 9; Lemma 11 | Every n ≥ 6 and every natural h: recovery through h iff h < n−2 (odd n), or h < n−3 (even n). |
| `grid_sensor_optimality` | Theorem 9 | For every n ≥ 6 and 2 ≤ h below the threshold, an n−2 sensor placement resolves h and every resolving placement has at least n−2 sensors. |
| `grid_fibre_uniform` | Corollary 13, population-level consequence | Every n ≥ 6 and natural populations x,y: equal complete observations iff y = x + Bₙp for a unique integer quadruple. |

Stable paper labels: `prop:trade`, `thm:product`, `eq:productkernel`, `lem:diamond`,
`lem:kernel`, `lem:minimum`, `thm:main`, and `cor:fibre`. Numbering was checked
against the final LaTeX auxiliary file.

## Definition fidelity

- `Configuration V = V → ℕ`: occupancy, with zero and repetition allowed.
- `bag δ x s` is the multiset sum of `replicate (x v) (δ s v)` over vertices.
- `ResolvesUpTo` quantifies over both populations of mass at most h.
- `Invisible` quantifies over every natural radius, not a sampled shell range.
- `Grid n = Fin n × Fin n`; `gridGraph` joins unit Manhattan displacements.
  `Grid.lean` proves that graph shortest-path distance is Manhattan distance.
- `AltSensor n = Fin (n−2)`; index k represents first coordinate i=k+1.
  Odd i lies on boundary zero; even i lies on boundary n−1.
- `Params4` consists of four unrestricted integers. `alternatingKernelVector`
  expands the paper's parity-specific row formulas, including the four boundary
  exceptions. Truncated natural exponents occur only where the selected domain
  makes them agree with the paper's integer exponents.
- `extract_reconstruct_uniform` and `kernel_complete_uniform` prove both
  coordinate-extraction identities in the implementation for every n ≥ 6.
- Product labels may repeat a sensor position; repetitions add no information.
- Three harmless domain extensions are explicit above: `h = 0` in Proposition 1,
  the empty sensor-label type in the selected clauses of Theorem 7, and vacuous
  `n < 3` cases in Lemma 8. None changes a nondegenerate paper claim.

## Proof structure

`UniformLaurent` and `UniformInverse` prove response identities and the local
tridiagonal inverse. `UniformGridBridge` connects these to actual shell sums.
`UniformSupport`, `UniformNecessity`, and `UniformParameters` force exactly four
integer parameters. `UniformSufficiency`, `UniformLift`, and
`UniformReconstruction` prove reconstruction and extraction in both directions.
`UniformNorm`, `UniformRowBounds`, and `UniformBoundary` prove the row and boundary
mass estimates. `UniformMinimum`, `UniformAttainer`, and `UniformRecovery` prove
sharpness, optimality and fibres. No bounded order or population census is used.

## Proved source endpoints outside the Comparator selection

The complete source development is included and built. In addition to the eight
paper-facing wrappers, it proves the exactly-h/at-most-h equivalence, the actual
grid-distance/Manhattan bridge, the parameter-extraction inverse, direct minimum
trade and attaining-parameter statements, and the alternating placement's
cardinality and recovery property. These are used by, or strengthen the
explanation of, the selected endpoints; they are not separately advertised in
`comparator.json`. The source also contains the full supporting proof chain.

## Paper results not formalized as paper-level Lean theorems

The release does not claim a theorem-complete formalization of the paper. The
following remain written results: the rational-rank and rational-kernel clauses;
the generic detector-hypergraph, B-channel, and capacity-profile reformulations;
the two-sensor distance-level cycle theorem and forest decoder; the converse half
of the exact diamond detector-cross description; the coefficient census and exact
arbitrary-parameter norm formulas; the normalized rational fibre, integrality and
slab characterization; the adjacent-corner metric-dimension and named
capacity-jump statements; and executable decoder correctness, termination, and
complexity. The selected fibre theorem concerns actual nonnegative integer
populations and does not assert the rational-normalization algorithm or a runtime
bound.
