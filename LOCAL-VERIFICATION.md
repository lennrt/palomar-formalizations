# Local verification of the October companions

The projects at `zenodo-23304384/palomar` and `zenodo-23346565/palomar`
use Lean `v4.35.0-rc2` and the dependency revisions in their manifests.
The repository script `scripts/verify-local.py` runs reproducible local checks;
it does not submit to Palomar or modify a remote repository.

## Reproduce

Install the pinned Lean toolchain and Python 3.11 or later with PyYAML.
Clone [PalomarSubmission](https://github.com/PalomarRegistry/PalomarSubmission)
at commit `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44` and
[Verso](https://github.com/leanprover/verso) at commit
`9f8096e40b31715b1d8d5997f15a0bd832f7e37d` (release `v4.35.0-rc2`).
Keep both source checkouts clean. Materialize the pinned project dependencies
with `lake exe cache get`, and Verso's dependencies with `lake build` in its
checkout. Do not update the project's manifest.

From this repository root, run the following for each project:

```sh
ruby scripts/check-layout.rb
python3 scripts/verify-local.py zenodo-23304384/palomar \
  --submission-tools /path/to/PalomarSubmission \
  --verso /path/to/verso \
  --renderer-packages /path/to/verso/.lake/packages
```

On macOS, add `--allow-unsandboxed-local-comparison` to use Comparator's
documented local mode. The explicit option is restricted to macOS. It does
not assert that Palomar's Linux Bubblewrap confinement has been exercised.
Repeat with `zenodo-23346565/palomar`. The `--stage` option can run preflight,
kernel replay, comparison or rendering separately; the default `all` runs
preflight, the full default build, fresh Lean kernel replay, comparison and
rendering in order.

After the full run and the finite experiments, bind the final inputs and
the complete sanitized artifact manifest with:

```sh
python3 scripts/verify-local.py zenodo-23304384/palomar \
  --submission-tools /path/to/PalomarSubmission --stage release
```

Repeat for `zenodo-23346565/palomar`. Release validation requires a successful
full run and unchanged proof, configuration and rendered artifact inputs.
It permits a metadata-only wording edit after a fresh official preflight,
records both metadata hashes, and preserves the original full report intact.

## What the evidence establishes

Each project's `verification/all.json` records the successful or failed result,
input SHA-256 fingerprints, checker versions, commands and timings. The script
rejects Lean, build-configuration or metadata changes during a run. Build caches and generated
web assets stay under ignored `.lake` directories; compact reports and logs
are committed. `verification/supplied-inputs.json` fingerprints the original
PDF and supplemental archive provided by the author.
The final `verification/release.json` links that full report by hash, rechecks
the current metadata and dependency sources, verifies the finite-experiment
program/log fingerprints, and records the sanitized bundle's complete tree
hash. It explicitly records any metadata-only refresh after the full run.

The local stages check:

- Official v0.4 metadata and Comparator configuration validation, repository-wide
  Lean source policy, compiler-parsed project module headers, independent
  Mathlib-only Challenge imports and source size limits, and clean pinned
  dependency revisions, remotes and Mathlib toolchain.
- Full default library builds and fresh Lean kernel replay of `Solution`.
- Bundled Comparator equality of independently elaborated selected statements,
  the standard axiom allowlist, and exported-proof replay with NanoDa and con-ron.
- The official core-notation signature audit, Verso literate and HTML rendering
  of unchanged Challenge bytes, and the unmodified official sanitizer's selected
  declaration and browser-content checks.

The per-project axiom audits and exact supplemental Python experiments provide
additional evidence with their own scope; finite experiments are not proofs
of universal statements. A later edit requires checking its relevant inputs
again. Reports from another snapshot do not certify the current snapshot.

## What remains a hosted decision

The GitHub Actions workflow
[palomar-october.yml](.github/workflows/palomar-october.yml) calls the exact
pinned official reusable workflow with `mode: full` and the
`palomar-standard-v1` execution profile for both project paths. It runs on
candidate-branch pushes and can also be dispatched manually. Its downloaded
mechanical reports must say `status: pass` for the exact candidate commit
before requesting Palomar intake. This Linux workflow exercises the full
mechanical pipeline; it does not run editorial review or register either work.
The local reports remain separate evidence, even after that workflow passes.

These are local checks using pinned official tools, not a full execution of
the hosted verifier. The reports explicitly identify unexercised service
confinement, authenticated canonical build and cache preparation, checker
controls, licensing/ORCID/network provenance checks and editorial review.
In particular, notability, definition fidelity and source alignment require
editorial judgment; an automated local mathematical audit cannot promise an
acceptance decision. The project READMEs explain the research motivation,
precise theorem coverage, antecedents and limitations for that review.

Neither project claims end-to-end formalization of every result in its paper.
The lossy companion covers exact two-leg recovery and selected sample-analysis
components; the decompression companion proves a conditional uniform finite-view
reconstruction reduction for large connected graphs, with geometry, coding
and a full-class counting lower bound. Remaining probabilistic results, the
external orientation algorithm and operational LOCAL-machine semantics are
identified explicitly.
