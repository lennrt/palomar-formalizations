# Mathematical contribution and research interest

The motivating inverse problem is recovery of indistinguishable targets on a
known graph from complete distance histograms at labelled sensors. On a square
grid, two adjacent corners locate a single vertex, yet two-target recovery
requires at least n−2 sensors. Losing target correspondence creates a geometric
obstruction even when every reported distance is exact.

The selected Lean statements prove a matching construction for every n ≥ 6.
Alternating boundary sensors have exactly a four-parameter integer kernel, with
first ambiguity at n−3 for even n and n−2 for odd n. The optimality theorem proves
that n−2 sensors are necessary and sufficient throughout 2 ≤ h below that threshold.
The fibre theorem gives unique integer coordinates for every equal-observation
population change, at every mass. Precise source alignment is in COVERAGE.md.

These consequences determine an optimal sensor design across an infinite graph
family, explain how a fixed four-dimensional ambiguity space coexists with a
growing minimum integer trade, and reduce exact reconstruction fibres from n²
occupancies to four integer parameters. The proof uses Laurent-polynomial
responses, a local tridiagonal inverse, boundary support restrictions and a bound
of at most one zero interior row. The threshold proof is independent of finite
coefficient enumeration. The Cartesian-product theorem transports the entire
kernel and every population recovery bound under full-factor sensing.

The intended audience includes researchers in discrete tomography, graph
identification, integer inverse problems and channels with multiset outputs.
The paper distinguishes these observations from nearest-object sensing, ordinary
metric dimension, coordinatewise code compositions and radial distributions on
an unknown metric-measure space. The integer-trade framework is established
background; the specific grid construction and its uniform structural analysis
supply the principal contribution.

Laihonen (2016), DOI 10.1016/j.ipl.2016.06.002, is credited for the antecedent grid
cross obstruction in a nearest-object model. Hajdu–Tijdeman (2007), DOI
10.1007/978-0-8176-4543-4_4, supplies algebraic-tomography context; D'yachkov et al.
(2019), DOI 10.1109/TIT.2019.2893234, studies coordinatewise multiset output;
Mémoli–Needham (2022), DOI 10.1111/sapm.12526, studies radial distributions with a
different unknown. The public Zenodo release contains the dated literature search
record. It reports that no equivalent theorem was found in the inspected sources
and states the finite-search and indexing limits explicitly.

This research-interest statement describes the mathematical case for the work.
Formal coverage, written-only results and verification limits remain explicit in
COVERAGE.md and VERIFICATION.md. No external peer review or official Palomar
acceptance is asserted.
