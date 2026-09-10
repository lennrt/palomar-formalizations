# Local verification — 9 September 2026

Verification of the complete v1.0.0 Lean development. The manuscript was used
as a review source; its PDF and LaTeX files are not part of the repository.

## Checked results

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

The 300-line / 32-KiB preferred-surface advisory remains. It is disclosed rather
than removed by dropping statements. The complete game and all 42 results are
independently visible to reviewers.

## Evidence and exact snapshot

### Proof-only package

After excluding the manuscript PDF and LaTeX source, the build and all 276
axiom checks were rerun successfully. Comparator, NanoDa and Lean also passed
the 42-result comparison and the additional 24-result game comparison again.
The current evidence is in
[proof-only-2026-09-09/](verification/proof-only-2026-09-09/):

- [Build and axiom result](verification/proof-only-2026-09-09/lean-result.json).
- [42-result Comparator report](verification/proof-only-2026-09-09/comparator-42.json).
- [24-result Comparator report](verification/proof-only-2026-09-09/comparator-24.json).
- [Compared input hashes](verification/proof-only-2026-09-09/comparator-inputs.json).
- [Packaging and comment-only change check](verification/proof-only-2026-09-09/packaging-inputs.json).

The current `Challenge.lean` SHA-256 is
`852d410b9cdc001fdde80e7cc77481ab68f65b733da8cdbfcff68f8ab6b32561`.
Its only change since the original rendered snapshot is one source-attribution
line in a module docstring. Removing comments leaves identical Lean content;
all 135 supplied library files remain unchanged. The renderer was not rerun
for this packaging change: the retained trusted-render results identify their
original snapshot below, rather than claiming a new rendering run.

The official metadata contract was rerun after updating the manuscript's
availability note. Its [current report](verification/local-2026-09-09/metadata-report.json)
is bound to metadata SHA-256
`faa6f843a6b67d444ad8a73a521f37d5f96a4b921e457f73539baf43235c8b6a`.

### Original build and render snapshot

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

## Faithful interface repair

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
[selection-map.json](verification/selection-map.json) records all 42 results:
13 wrapper names and 29 original names. Both Comparator and the unmodified
current renderer accepted this interface.

The original 135 library sources remain unchanged and are hash-checked by
[the supplied-library manifest](verification/library-sources.json). Historical
author-supplied verification files are preserved separately in
[verification/supplied-artifact/](verification/supplied-artifact/), not presented
as evidence for the repaired package's current gates.

## Mathematical review and remaining hosted checks

Independent AI-assisted source review inspected the manuscript's mathematical
body, rendered pages, actual graph/game definitions and the proof dependency
chain. It found no mismatch in the main characterization, explicit bound,
initialization, recurrent coverage, short-cycle classification or final numerical
Conjecture 24. The main theorem assumes only its stated graph hypotheses.
The all-order characterization and strategy bounds provide substantive research
content; known closed classifications and ring sensor bounds remain credited.

The paper's degree-independent arbitrary-game interface theorem and the
ring-family structural connection in Remark 19 remain written-only; their
complete cubic application and the sensor lower bound are formalized. Census
counts and historical regressions remain tests. No independent human refereeing,
absolute novelty, or Palomar editorial acceptance is claimed. The dated
[eight-lane source/duplication audit](verification/provenance/local-scoop-check.md)
records finite-search limits and must be refreshed before public submission.

This macOS run reproduced the trusted rendering configuration, signature audit,
Verso and sanitizer. It did not reproduce the hosted Linux systemd/Landrun
render-confinement wrapper, GitHub immutable-commit fetch, submitter authorization
or Palomar's server-side editorial decision. Those require a later public
submission. The manuscript was reviewed privately and is distributed separately;
neither its PDF nor its LaTeX source is included in this repository. Follow
[SUBMISSION.md](SUBMISSION.md) when ready.
