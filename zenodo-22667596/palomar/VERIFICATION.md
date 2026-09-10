# Verification — 10 September 2026 selection revision

The Palomar configuration now selects 39 pursuit, short-cycle and game-value
results. It excludes three supplementary sensing statements:
`ZombieMain.diamond_ring_sensor_bound`,
`ZombieDamage.Graph.involution_blocks_recovery` and
`PalomarVerified.central_pair_sensor`. Their proofs remain in the library.
The 135 supplied library sources, all 13 presentation wrappers and the
276-root axiom audit are retained. Twelve wrappers and 27 original names
are selected by the revised configuration.

The main Challenge contains only the selected pursuit material and its
definitions. The 24-statement `GameChallenge` is unchanged and remains an
additional regression comparison, not a Palomar submission configuration;
it includes two supplementary sensing statements.

## Revised-selection checks

The revised selection was checked against its own input hashes. Its evidence
is recorded under [editorial-2026-09-10/](verification/editorial-2026-09-10/);
the historical 42-result reports below do not certify the modified Challenge
or configuration.

| Check | Revised-selection result |
|---|---|
| Lean 4.32.0 build | Passed; 3,163 build jobs and 141 local Lean files |
| Library preservation | All 135 supplied library files retain their original hashes |
| Transitive axiom audit | All 276 roots passed with only `propext`, `Quot.sound`, `Classical.choice` |
| Main Comparator comparison | All 39 selections passed Comparator, NanoDa and Lean; 137.70 seconds |
| Supplementary regression comparison | All 24 statements passed Comparator, NanoDa and Lean; 40.56 seconds |
| Comparison input stability | All 146 proof/configuration inputs unchanged during each comparison |
| Trusted core-notation audit | All 39 selected signatures passed |
| Verso and official sanitizer | Passed; all 39 compiler-backed declarations rendered |
| Challenge import policy | Passed with high trust and no untrusted source dependency |
| Statement preservation | Retained declaration tokens unchanged; only the separate sensing surface removed |
| Official metadata contract | Passed; author and maintainer fields contain only Lennart Rudolph |
| Repository structural preflight | All 12 projects passed |

The current proof evidence includes the [build/audit result](verification/editorial-2026-09-10/lean/result.json),
[build log](verification/editorial-2026-09-10/lean/build.log) and
[276 axiom reports](verification/editorial-2026-09-10/lean/axioms.log).
The [39-result Comparator report](verification/editorial-2026-09-10/comparator/result.json)
and [log](verification/editorial-2026-09-10/comparator/comparator.log), and the
[24-result regression report](verification/editorial-2026-09-10/game-comparator/result.json)
and [log](verification/editorial-2026-09-10/game-comparator/comparator.log), each
have before/after input-hash manifests in their respective directories.

The [render report](verification/editorial-2026-09-10/render/report.json),
[signature inventory](verification/editorial-2026-09-10/render/audit-declarations.json),
[allowlist audit](verification/editorial-2026-09-10/render/challenge-allowlist.json)
and [statement-preservation report](verification/editorial-2026-09-10/render/statement-preservation.json)
record the exact current Challenge. Its SHA-256 is
`4040c4fce0ea13a6f01c48cbf6bcad8ca73ee283e0d5261f62aa18157da774e6`.
The [metadata report](verification/editorial-2026-09-10/metadata/report.json)
is bound to `formalization.yaml` SHA-256
`ea98d0e290bdd7eefe08847c20b0f6cfc359b5926b8b3be19942888700f898cd`.

The revised Challenge is 902 lines and 49,366 bytes, within the hard
1,000-line / 100-KiB limits but above the preferred 300-line / 32-KiB surface.
Static checks confirm 39 main statement holes, the unchanged 24 regression
statement holes, all 135 preserved library hashes and the 276-root audit scope.

The public Palomar policy and submission-tool `main` commits were rechecked
on 10 September 2026 and match the pins in [tool-pins.json](tool-pins.json):
PalomarPolicy `e9c8c238f5695b10f75db7175648a1d0195352c1` and
PalomarSubmission `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`.

The [10 September eight-lane source/duplication audit](verification/provenance/editorial-scoop-check-2026-09-10.md)
reached GREEN for this bounded selection revision. It records the finite search
and known antecedents, not an absolute priority claim. These local checks do
not certify Palomar's hosted Linux confinement, immutable-commit intake or
editorial decision; those are performed on the submitted revision.

## Historical snapshots — 9 September 2026

Verification of the complete v1.0.0 Lean development. The manuscript was used
as a review source; its PDF and LaTeX files are not part of the repository.
The following tables and reports describe the previous 42-result selection,
not the current 39-result configuration.

### Historical checked results

| Check | Result |
| --- | --- |
| Full Lean 4.32.0 build | Passed; 3,163 build jobs, 141 local Lean files |
| Supplied library preservation | All 135 library files byte-identical, including the original 132-file manifest |
| Independent submission statements | All 42 results stated explicitly in `Challenge`; no local imports |
| Comparator and independent NanoDa kernel | All 42 selected results passed; Lean kernel also accepted |
| Additional Std-only game comparison | All 24 original game statements passed Comparator, NanoDa and Lean |
| Transitive axiom audit | All 276 roots passed: 263 supplied roots plus 13 presentation wrappers |
| Permitted axioms | Only `propext`, `Quot.sound`, `Classical.choice` |
| Proof holes in Solution or its dependencies | Zero |
| Deliberate statement holes | 42 in `Challenge`, 24 in auxiliary `GameChallenge` |
| Trusted core-notation audit | All 42 selected signatures accepted with submitted extensions disabled; render snapshot noted below |
| Verso rendering and official sanitizer | Passed; all 42 compiler-backed declaration anchors present; render snapshot noted below |
| Challenge import policy | Canonical pinned Mathlib/core closure; no untrusted statement dependency |
| Metadata and source provenance | Official current contract passed; source-based, substantive development |
| Repository structural preflight | All 12 projects passed; root licence and nested project layout checked |
| Challenge hard size limits | 973 lines and 53,034 bytes: within 1,000 lines / 100 KiB |

That Challenge exceeded the 300-line / 32-KiB preferred-surface advisory.
The 10 September change excludes an unrelated sensing group; it does not
weaken the pursuit statements or alter any original proof.

### Historical evidence and exact snapshot

#### Proof-only package

After excluding the manuscript PDF and LaTeX source, the build and all 276
axiom checks were rerun successfully. Comparator, NanoDa and Lean also passed
the 42-result comparison and the additional 24-result game comparison again.
The corresponding historical evidence is in
[proof-only-2026-09-09/](verification/proof-only-2026-09-09/):

- [Build and axiom result](verification/proof-only-2026-09-09/lean-result.json).
- [42-result Comparator report](verification/proof-only-2026-09-09/comparator-42.json).
- [24-result Comparator report](verification/proof-only-2026-09-09/comparator-24.json).
- [Compared input hashes](verification/proof-only-2026-09-09/comparator-inputs.json).
- [Packaging and comment-only change check](verification/proof-only-2026-09-09/packaging-inputs.json).

That proof-only snapshot's `Challenge.lean` SHA-256 is
`852d410b9cdc001fdde80e7cc77481ab68f65b733da8cdbfcff68f8ab6b32561`.
Its only change since the original rendered snapshot is one source-attribution
line in a module docstring. Removing comments leaves identical Lean content;
all 135 supplied library files remain unchanged. The renderer was not rerun
for this packaging change: the retained trusted-render results identify their
original snapshot below, rather than claiming a new rendering run.

The official metadata contract was rerun after updating the manuscript's
availability note. Its [historical report](verification/local-2026-09-09/metadata-report.json)
is bound to metadata SHA-256
`faa6f843a6b67d444ad8a73a521f37d5f96a4b921e457f73539baf43235c8b6a`.

#### Original build and render snapshot

The original verified snapshot is retained in
[local-2026-09-09/](verification/local-2026-09-09/):

- [Build, static checks and 276-root audit result](verification/local-2026-09-09/lean-result.json),
  [build log](verification/local-2026-09-09/build.log) and
  [actual axiom reports](verification/local-2026-09-09/axioms.log).
- [42-result Comparator report](verification/local-2026-09-09/comparator-42.json)
  and [full proof-check log](verification/local-2026-09-09/comparator-42.log).
- [Additional 24-result report](verification/local-2026-09-09/comparator-24.json)
  and [log](verification/local-2026-09-09/comparator-24.log).
- [Trusted render report](verification/local-2026-09-09/render-report.json),
  [rendered signature inventory](verification/local-2026-09-09/rendered-declarations.json)
  and [import-policy report](verification/local-2026-09-09/challenge-allowlist.json).
- [Official metadata/provenance report](verification/local-2026-09-09/metadata-report.json),
  bound to the final metadata hash and sole-author/maintainer fields.
- [Compared proof-input hashes](verification/local-2026-09-09/comparator-inputs.json).
  All 146 proof/configuration inputs remained unchanged during both comparisons.
  The end-to-end build/audit script additionally hashes 156 inputs including
  verification scripts, metadata and source-preservation manifests.

SHA-256 identities of that original proof snapshot:

| File | SHA-256 |
| --- | --- |
| `Challenge.lean` | `24409a2acade562c18753964d6d4c29fba2af674db891652d6ba5ff12db4fa42` |
| `comparator.json` | `747bb6031bd08898a5f432e71d5fcd69d03e98b857bb5d24db46a2677cd35d89` |

[tool-pins.json](tool-pins.json) records the exact current service revisions:
Submission `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`,
Comparator `575674928e239f5bc452aab72d1dd7b0f1326494`,
the Lean 4.32 exporter, NanoDa, Landrun and Verso.
The local replay uses the service's Comparator pin, not the different
template-based Comparator pin in the supplied archive.

The shipped `scripts/verify.py` was run end to end. Comparator checks used the
equivalent direct invocation of the exact trusted binaries, with the official
Landrun argument adapter. The shipped `verify-comparator.py` launcher was
reviewed and statically checked; its executable local Landrun adapter was
smoke-tested against the real pinned sandbox. No stub or skipped NanoDa check
was used. Its commands are documented in [README.md](README.md).

### Original faithful interface repair

The supplied `MainChallenge` imported local proof/definition modules and did not
independently declare 26 selections. It was replaced by a complete standalone
`Challenge`, retaining the separate Std-only comparison.

The current renderer has a documented
[transparent-alias bug, issue #134](https://github.com/PalomarRegistry/PalomarSubmission/issues/134).
Thirteen original signatures encountered it. Four transparent helpers now spell
ordinary graph degree, a typed diamond vertex pair, and port equality/inequality.
Each corresponding theorem in [PalomarWrappers.lean](PalomarWrappers.lean) is
proved by a direct `exact` application of its original theorem. The helpers
change no mathematical meaning, hypothesis, game rule or conclusion.
The original interface selected 42 results: 13 wrapper names and 29 original
names. Both Comparator and the unmodified renderer accepted that interface.
The current [selection map](verification/selection-map.json) instead records
39 pursuit results: 12 wrapper names and 27 original names.

The original 135 library sources remain unchanged and are hash-checked by
[the supplied-library manifest](verification/library-sources.json). Historical
author-supplied verification files are preserved separately in
[verification/supplied-artifact/](verification/supplied-artifact/), not presented
as evidence for the repaired package's current gates.

## Mathematical scope and hosted checks

Independent AI-assisted source review inspected the manuscript's mathematical
body, rendered pages, actual graph/game definitions and the proof dependency
chain. It found no mismatch in the main characterization, explicit bound,
initialization, recurrent coverage, short-cycle classification or final numerical
Conjecture 24. The main theorem assumes only its stated graph hypotheses.
The selected results concern the all-order characterization and strategy
bounds, the graph decomposition and metric routing that establish them, and
their structural and recurrent-coverage consequences. Known closed
classifications remain credited; the separate sensing results are no longer
selected and their attribution is preserved.

The paper's degree-independent arbitrary-game interface theorem and the
ring-family structural connection in Remark 19 remain written-only; their
complete cubic application is formalized, as is the unselected supplementary
sensor lower bound. Census
counts and historical regressions remain tests. No independent human refereeing,
absolute novelty, or Palomar editorial acceptance is claimed. The dated
[eight-lane source/duplication audit](verification/provenance/editorial-scoop-check-2026-09-10.md)
records the 10 September selection-revision sweep and its finite-search limits;
it must be refreshed before a later public submission if the context changes.

The historical macOS run reproduced the trusted rendering configuration, signature audit,
Verso and sanitizer. It did not reproduce the hosted Linux systemd/Landrun
render-confinement wrapper, GitHub immutable-commit fetch, submitter authorization
or Palomar's server-side editorial decision. Those require a later public
submission. The manuscript was reviewed privately and is distributed separately;
neither its PDF nor its LaTeX source is included in this repository. Follow
[SUBMISSION.md](SUBMISSION.md) when ready.
