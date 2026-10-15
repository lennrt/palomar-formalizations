# Lossy Distance-Shell Tomography on Paths

Lennart Rudolph · manuscript version 2.0.0, 11 October 2026 · Lean 4.35.0-rc2

This project formalizes the central path-recovery results of
[Lossy Distance-Shell Tomography on Paths: Recovery from Mean and Covariance](https://doi.org/10.5281/zenodo.23252713).
The supplied version 2 manuscript and proof archive are preserved at
[the version-specific record](https://zenodo.org/records/23304384).
The canonical citation is **10.5281/zenodo.23252713**. The enclosing directory
retains the supplied version's record number for reproducible provenance.

## Why the result matters

A path sensor counts targets at each hop, without identifying targets or saying
which side they occupy. Without failures, two populations `a` and `b` produce
only the coordinatewise fold `a + b`. For example, one target at depths one
and two on a single side has the same folded report as targets at depth one
on one side and depth two on the other.

In the paper's specified loss model, every relay independently survives a round
with known probability `p`. A failed relay's own targets are silent, and surviving
relays beyond it are connected through the contracted path. The report still
adds both sides. Shared surviving prefixes create correlations that distinguish
these folded collisions. For every `0 < p < 1`, the mean and covariance identify
the two population vectors up to global exchange. This is a statement about
anonymous aggregate observations under that contraction rule; it does not
assert that every physical routing protocol implements the model.

The proof first recovers the fold by a triangular mean system. Polarization
subtracts its known covariance contribution, leaving the covariance form of
`a - b`. The last nonzero corrected diagonal identifies the deepest nonzero
difference and its magnitude. Once its sign is chosen, that column recovers
all earlier differences through nonzero pivots `1 - p^(k+1)`. Consequently,
the mean plus the covariance diagonal and one adaptive column suffice.
For positive length `n`, this uses at most `2n - 1` covariance entries.

This channel-specific recovery mechanism is the principal research result.
Polarization, triangular elimination, nearest-integer rounding, and two-point
testing are standard ingredients, not individually claimed as new theorems.
The endpoint-to-deletion-trace identity supplies model context; the imported
trace-reconstruction complexity theorems are not re-proved here. The manuscript
contains the detailed literature comparison. It is a preprint, without a claim
of completed independent human peer review or publication priority established
by the formal checker.

## Mathematical contract

A leg is `Fin n → ℕ`, allowing arbitrary multiplicities, all-zero populations,
and `n = 0`. Index `i` means true depth `i + 1`; report index `k` means observed
hop `k + 1`. The sensor stays present. Boolean masks describe survival on each
leg, and pattern weights are literal products of `p` and `1-p`. Report laws,
means, and covariances are finite sums over these independent masks, not
abstract observables whose identifiability is assumed.

The interface uses real probabilities. The supporting exact-recovery library
proves the corresponding algebra over linearly ordered fields. All compared
legs have the same length. Padding shorter paths with zero populations is an
interpretation described in the manuscript, not an additional formal theorem
relating different lengths. Global exchange is unavoidable; independent swaps
at different depths are not allowed by the conclusion. The endpoint report
forgets trailing zero counts, and its horizon is required to reconstruct the
full deletion trace, including silent surviving relays.

## Selected results and supporting development

[Challenge.lean](Challenge.lean) independently defines the experiment using
Mathlib alone and states ten comparison obligations.
[Solution.lean](Solution.lean) imports the complete substantive proof library
and proves those identical propositions. It never imports the Challenge.
[DECLARATIONS.md](DECLARATIONS.md) maps every endpoint to its source theorem,
proof module, mathematical role, and limitations.

The selection contains the full and sparse recovery theorems, exact
characterization of equality of report laws, mean/fold equivalence, endpoint
semantics, actual-model variance bounds, two deterministic reconstruction
recurrences, and a logarithmic testing lower bound on actual length-`n` reports.
The latter proves

`N ≥ (n/2) log(1/(2δ))`, at `p = 2n/(2n+1)`, for `n ≥ 2`,

whenever an arbitrary randomized test has both candidate error probabilities
at most `δ`. This is the factor-two weaker constant explicitly documented in
the manuscript's formalization section. It is not a formal claim of the
paper's sharper `n log(1/(2δ))` bound. The candidates are concrete distinct
binary populations, so they also belong to every count class with bound at
least one. The informative regime is `0 < δ < 1/2`.

All six `LossyShell` proof modules, four `ShellResearch` modules, and three
`ShellSampling` modules are included. The supporting library additionally
contains exact length-two law calculations, geometric design bounds, threshold
and square-root recovery, symmetric-case handling, and tail summation.
The exact Python decoder and checks supplied with the paper are included under
[experiments](experiments); finite checks supplement the proofs and are not
additional kernel-certified theorems.

## Scope limits

The deterministic reconstruction statements assume the stated empirical error
bounds and rounding equations. The difference recurrence also assumes that
the deepest index and its oriented magnitude were correctly recovered. The
library proves components of these stages, but no endpoint silently treats
these hypotheses as a complete probability guarantee.

Bernstein concentration, the simultaneous good-event probability, independence
for the two-batch estimator, and the final minimax upper-bound composition
remain written proofs. Thus the full finite-sample recovery guarantee and
matching minimax theorem are not formalized here. The general-tree mean and
landing formulas, unknown-rate calibration, spider moment obstruction, tree
recursion and conjecture, imported trace-complexity bounds and their simulation
transfer, derivative-based optimal-rate calculation, and manuscript-wide
computations likewise lie outside the Lean endpoints. These limitations agree
with Section 7 of the supplied version 2 manuscript.

## Build and check

From this directory, with elan and the pinned toolchain available:

```sh
lake exe cache get
lake build
lake env lean verification/AxiomAudit.lean
python3 experiments/check_sampling.py
python3 experiments/check_streaming.py
python3 experiments/check_design_bounds.py
```

The cache is optional. The manifest pins dependencies; no adjacent paper's
sources are imports. The deliberate `sorry` statements occur only in Challenge.
The solution and its libraries must depend only on `propext`, `Classical.choice`,
and `Quot.sound`.

The repository release checker runs the official local preflight, comparator,
independent kernels, and rendering checks. See [SUBMISSION.md](SUBMISSION.md)
and [VERIFICATION.md](VERIFICATION.md) for commands, evidence, and the boundary
between local validation and Palomar service/editorial decisions.

## Authorship, provenance, and automation

Lennart Rudolph is the sole human author and responsible maintainer. The paper
credits Anthropic Claude (Opus) and OpenAI ChatGPT/Codex with substantial help
on literature review, mathematical development, exact computations, Lean, and
writing; Codex additionally assisted the version 2 sampling analysis and
formalization. Codex prepared this repository's independent interface, module
migration, documentation, and local checks. AI systems are not listed as authors;
automated review does not constitute independent human peer review.

The original supplied proof sources and scripts are retained with their MIT
licenses. The source modules were adapted to Lean's explicit public module
system; their mathematical statements and proofs are retained. The interface
and metadata use the repository's [MIT license](../../LICENSE).
