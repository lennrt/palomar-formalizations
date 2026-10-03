# Repository-wide Lean module migration

Palomar checks every Lean source in the submitted repository, including sibling
projects outside the selected Comparator configuration. The migration ports the
258 older files to the module system; the 45 files in `zenodo-23125523` already
used it. This removes the missing-header errors that prevented intake of the
geometric-certificates project.

Each migrated file has a `module` header, public imports, and an exposed public
section. These preserve the declarations and reducible definitions that the
older files exported. Where an existing native computation requires executable
imported definitions, the required imports also have explicit `meta` visibility.
Two Betti proof helpers, `iso_cycles_map` and `sevenTriangle_bijective`, become
public so exposed definitions can refer to them across module boundaries. Their
statements and proofs are unchanged. All theorem statements, proof bodies,
Comparator selections, toolchain pins, dependency manifests, and PDFs are unchanged.

Five older metadata entries also listed automated assistants as authors. Their
project and paper author fields now name only Lennart Rudolph, consistent with
the repository's authorship policy; the automation and automated-review
disclosures remain.

## Validation scope

Eleven projects pass complete library builds. Sobol and Barnette use the bounded
build checks described below. All 13 Challenges render and pass the official
sanitizer: 110 selected theorems and seven selected definitions.

The machine-readable [migration record](verification/module-migration.json)
records the final source fingerprints and results. Checks use the official
`PalomarRegistry/PalomarSubmission` tooling at commit
`65f0154ed776cd26c224254aa57b379137f28b0d`.

- The official repository-wide source policy checks all 303 Lean files for
  valid module headers and the 10,000-line limit.
- Lean 4.35.0-rc2 parses all 303 headers with `--deps-json`, matching the toolchain
  of the intended `zenodo-23125523` submission. Older projects additionally use
  their own pinned compiler for their build checks.
- The official metadata validator checks all 13 projects. Each project's author
  and responsible-maintainer lists contain only Lennart Rudolph.
- The repository layout check covers all 13 projects and accepts release-candidate
  pins. Regression fixtures exercise comments, malformed headers, missing headers,
  the line limit, and rejection of a violation in an unused sibling file.
- Challenge rendering uses the matching pinned Verso release, followed by the
  official HTML sanitizer. Rendering checks the selected statement surface;
  it does not execute exhaustive census programs or substitute for proof checking.

The Sobol project (`zenodo-21925582`) has an expensive census embedded in its Lean
proofs. Its `Core`, `Census.Defs`, and independent `Challenge` are compiled, and
its Challenge is rendered. The 35 census window modules and census-dependent
`Solution` are deliberately not rebuilt in this migration check. Their headers
are compiler-checked and their proof bodies are unchanged. A full Sobol build
would re-evaluate those certificates; it is not claimed here.

The Barnette project (`zenodo-21890733`) has a separate auxiliary library whose
existing native proofs exhaustively enumerate walks in 137 deletion subgraphs.
That costly auxiliary build was stopped. Its independent selected `Challenge`
and `Solution` build and render successfully; the full native auxiliary rebuild
is not claimed. Its module header and required runtime imports are ported without
changing the finite certificate statements or proof bodies.

No repository-wide Comparator, independent-kernel, or exhaustive-experiment
rerun is claimed. The geometric-certificates project's existing comparison and
rendering input fingerprints still match its unchanged Lean sources and
selection. Its default build and Challenge rendering are checked again.
These are local checks, not hosted verification, editorial approval, or a
registry submission.

## Reproduction

Run the inexpensive repository checks from the repository root:

```sh
ruby scripts/check-layout.rb
python3 zenodo-23125523/palomar/scripts/verify_palomar.py \
  --submission-tools /path/to/PalomarSubmission
```

The second command requires PyYAML and a clean checkout at the tooling revision
above. It now exits unsuccessfully if either the selected project or a sibling
violates the repository-wide source policy.

Build commands and rendered declaration counts are recorded per project in the
migration record. `scripts/build-all.sh` remains available for a complete default
target build, but includes the expensive Sobol census. An explicit build of the Barnette
auxiliary library also runs its exhaustive native certificates. Rendering follows the
pinned official `render_challenge.py` workflow with the project's matching Verso
release; generated HTML, dependencies, and build caches are not committed.

The older registered projects retain Lean 4.30.0 or 4.32.0 to preserve their
existing build environments. This migration addresses the repository-wide
source policy. Submitting an older project as a new entry would additionally
require a toolchain accepted by Palomar at that time. The intended new entry
continues to use `zenodo-23125523/palomar/comparator.json` and Lean 4.35.0-rc2.
