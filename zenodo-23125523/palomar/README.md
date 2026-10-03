# Distance-Shell Tomography: Geometric Certificates

Lennart Rudolph <a href="https://orcid.org/0009-0009-0198-085X"><img src="https://orcid.org/sites/default/files/images/orcid_16x16.png" alt="ORCID" width="16" height="16"></a>

3 October 2026 · Lean 4.35.0-rc2

This self-contained Lean project accompanies
[Distance-Shell Tomography: Geometric Certificates for Fault-Tolerant Sensing,
Moment Compression, and Hypercube Equalization](https://doi.org/10.5281/zenodo.23125523),
also published on
[ResearchGate](https://www.researchgate.net/publication/415199103_Distance-Shell_Tomography_Geometric_Certificates_for_Fault-Tolerant_Sensing_Moment_Compression_and_Hypercube_Equalization).
It includes the complete proof library and an independent 14-statement
Challenge covering six result groups. The paper is a preprint; journal
acceptance and completed independent human peer review are not claimed.

## Main results and observation contract

A population assigns a nonnegative integer multiplicity to each graph vertex.
Every labelled sensor reports the multiset of distances to that population.
Coincident targets and the empty population are allowed. Distances in the
formal graph results are actual shortest-path distances.

On the square grid with side length `n >= 3`, require the four corners and
recovery of every population of mass at most two after one identified sensor
erasure. The minimum number of sensors is exactly

$$\left\lceil\frac{3(n+1)}2\right\rceil.$$

The proof characterizes robustness by crossing counts for every pair of
equal-length interior intervals. Leaf-star placements meet every such cut
twice, and a boundary-sensitive degree count proves optimality. Keeping full
reports at the four corners and only the sum of distances at every other
sensor gives exactly the same robustness condition. The selected unrestricted
lower bound is `3m < 2|S|`, where `m = n - 2`; the stronger unrestricted bound
in the manuscript is not represented as a Lean endpoint.

For positive `q`, the hypercube results construct a distance-equalizer set
of size `2^(4q-1) + 2q` and prove that every equalizer has size at least
`2^(4q-1) + 2q - 1`. Thus

$$2^{4q-1}+2q-1\le\xi(Q_{4q})\le2^{4q-1}+2q.$$

Equalization quantifies over distinct vertices **outside** the selected set:
some selected vertex must be equidistant from each such pair. The formal
proof retains this quantifier. Parity reduces the problem to antipodal
coverage; even prefixes provide the upper witness, and a parity-orthogonality
argument gives the lower bound. For `q >= 3`, the upper witness contradicts
the conjectured exponential correction.

The other selected results give:

- the interval criterion and exact `2N + 4` corner-constrained optimum on
  `(M + 2)` by `(N + 2)` rectangles when `0 < N <= M` and `5N <= 3M`;
- ordinary 2-domination number `2n` for every positive even `n` by `n` bishop board;
- double-total-domination numbers `16` for `P(11,4)` and `24` for `P(16,5)`;
- a connected six-vertex graph whose real fractional optimal faces have the
  stated Class I relation but no vertex null on both faces.

[DECLARATIONS.md](DECLARATIONS.md) explains every compared theorem and links
its substantive proof. [Challenge.lean](Challenge.lean) independently states
the selected definitions and propositions using pinned Mathlib alone.
[Solution.lean](Solution.lean) never imports the Challenge.

## Development and related work

This repository contains the substantive development, including 39 library
source files under [ShellObservability](ShellObservability) and
[ShellTomography](ShellTomography). The interface wrappers directly apply
their proved theorems. The imports include population semantics, grid and
cube graph-distance proofs, collision geometry, charging inequalities,
constructions, parity arguments, and concrete domination certificates.

The predecessor,
[Distance-Shell Tomography on Graphs](https://doi.org/10.5281/zenodo.22404456),
supplies the population model, integer trades, and imported graph-distance
foundations, and asks about redundancy. The present grid results address one
erased report. The singleton cut constraints are related to total domination
in rook graphs: the three-leaf star patterns and the rectangular regimes have
antecedents in [Kazemi, Pahlavsay, and Stones](https://doi.org/10.2298/FIL1819713K)
and [Carballosa and Wisby](https://doi.org/10.1016/j.dam.2023.04.008).
The formal sensing theorem additionally requires all interval cuts and the
boundary accounting for the specified observation contract.

For cubes, [Gispert-Fernández, Rodríguez-Velázquez, and Yero](https://doi.org/10.1007/s40840-026-02088-4)
provide the conjecture and existing parity geometry. Prefix balancing and
the parity lemma are classical, from
[Knuth](https://doi.org/10.1109/TIT.1986.1057136) and
[Alon, Bergmann, Coppersmith, and Odlyzko](https://doi.org/10.1109/18.2610).
The folded orthogonality quotient is also an existing graph, studied by
[Boutin and Cockburn](https://doi.org/10.1002/jgt.22704).
The compared statements concern the actual equalizer contract and its
cardinality bounds; they do not claim those ingredients as new.

[Burchett's Conjecture 5.1](https://doi.org/10.61091/um124-04) is the source of
the even bishop-board question; its upper bound was already known. The two
Petersen values contradict the formulas in
[Zhao and Wei, Conjectures 3.1–3.2](https://doi.org/10.12988/ams.2017.7114).
No first-refutation priority is claimed: the full scope of an earlier
[Sun–Shao paper](https://doi.org/10.1166/jctn.2016.5595) remains an access
limitation in the source review. The fractional statement concerns
[Rubalcaba's dissertation, Conjecture 5.2.5](https://etd.auburn.edu/handle/10415/1030),
and uses continuous optimal faces rather than an integral surrogate.
Precise source relationships and bibliographic authorship are recorded in
[formalization.yaml](formalization.yaml).

## Build and verify

Install [Lean through elan](https://github.com/leanprover/elan), then run from
this directory:

```sh
lake exe cache get
lake build
lake env lean verification/AxiomAudit.lean
lake env lean verification/ExpansionAudit.lean
python3 scripts/check_snapshot.py
```

The committed toolchain and manifest pin Lean and Mathlib. The cache command
is optional; no adjacent project's build products are required. The only
permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.
The Challenge's deliberate statement holes are excluded from the proved
development and are never imported by a proof.

Run the independent comparison before the full release check:

```sh
python3 scripts/verify_comparison.py
python3 scripts/verify_release.py
```

The comparison uses the pinned toolchain's Lean, NanoDa, and con-ron checkers.
Its default uses Linux Bubblewrap. On an author-controlled macOS checkout,
the script offers the explicit local alternative
`--allow-unsandboxed-local-comparison`; this is not service-side verification.
The release script builds, audits, and runs fourteen exact finite programs,
including long exhaustive searches. These require Python and a C++17
compiler; the proof checks do not depend on an optimization solver.
The solver used for discovery is not part of verification.

[VERIFICATION.md](VERIFICATION.md) summarizes the completed checks. Logs and
input fingerprints are recorded under [verification](verification).
A passed report applies to its recorded inputs, not automatically to a changed
selection. For the local official metadata and source-policy checks, install
PyYAML and use a clean checkout of `PalomarRegistry/PalomarSubmission` at
commit `65f0154ed776cd26c224254aa57b379137f28b0d`:

```sh
python3 scripts/verify_palomar.py --submission-tools /path/to/PalomarSubmission
```

This writes `verification/palomar-preflight.json`, distinguishing the new
project from the whole repository. The new project is separate from the pre-existing module-header
issues in 258 sibling Lean files: current Palomar policy scans the entire
repository. [SUBMISSION.md](SUBMISSION.md) records this external blocker.
The [local significance assessment](verification/local-significance.json)
explains the six result groups and their specialist audiences. Local
mathematical checks are not official significance review, service verification,
or registration.

## Coverage limits

The 14 selected statements are enumerated in [DECLARATIONS.md](DECLARATIONS.md).
Other proved modules remain available, including additive-field recovery,
tensor moments, Boolean interpolation, syndrome certificates, and the
three-word/four-word hypercube geometry. Their inclusion is not a claim that
each is a separate research contribution.

The manuscript's general quantitative polynomial balancing theorem, the
folded graph as a separate formal object, its exact domination numbers in
dimensions 8, 12, and 16, the stronger unrestricted grid bound, finite optimal
placements, and the full Hamming-moment capacity and report-distance theorems
are not selected Lean endpoints. The finite values have exact computational
checks; they are not kernel certificates. The library's tensor and sampling
lemmas do not by themselves formalize those full moment theorems.

## Automation

Lennart Rudolph directed the work and is its sole human author and responsible
maintainer. OpenAI Codex assisted the first version with research, proofs,
formalization, verification, and writing. Anthropic Claude (Claude Code)
assisted the 3 October revision, including the stronger cube lower bound,
leaf-star design, all-order grid optimum, and additional exact searches.
OpenAI Codex assisted the final review and repository preparation. No AI is
an author; automated reviews are not independent human peer review.

The source and repository documentation are
[MIT licensed](../../LICENSE). Publication materials are available separately
at the cited Zenodo record.
