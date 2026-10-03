# Local Challenge rendering verification

All 14 selected declarations passed the official core-notation signature audit,
Verso literate generation, HTML rendering, and Palomar's unmodified sanitizer.
All 45 project Lean files also passed compiler-based module-header checks.
`report.json` binds the results to the submitted inputs, official tool sources,
Lean release, Verso revision, and every materialized dependency revision.

These are local macOS checks. They do not certify hosted Bubblewrap confinement,
editorial approval, or registration. The generated HTML/assets remain under
ignored `.lake/local-render/`; only compact evidence is committed here.

## Reproduction

Use PalomarSubmission commit `65f0154ed776cd26c224254aa57b379137f28b0d`
and Verso commit `9f8096e40b31715b1d8d5997f15a0bd832f7e37d`
(the `v4.35.0-rc2` release). With the pinned project built:

1. Run `lake env lean --deps-json FILE` for each file recorded in
   `module-headers.json`, and parse the result with the official
   `verify_submission.parse_lean_header` routine. Every result must have
   `is_module = true` and exit code zero.
2. Run `lake env lean --run PATH_TO_PALOMAR_SUBMISSION/scripts/core_notation_audit.lean
   Challenge theorem NAME ...`, taking the names in comparator configuration order.
   The exact executed command and tool hash are in `core-notation-report.json`.
3. Construct an isolated renderer workspace using the official
   `render_challenge.trusted_lakefile` and `merge_renderer_manifest` functions,
   the project's manifest, and the pinned Verso manifest. Use module `Challenge`
   and source root `.`. Copy `Challenge.lean`, `Solution.lean`, `comparator.json`,
   and `lean-toolchain` unchanged, and materialize the merged pinned dependencies.
4. In that workspace, run `lake build Challenge:literate`, then
   `lake exe verso-html .lake/build/literate .lake/build/palomar-render-raw`.
5. Run the official `render_challenge.py sanitize` command in the Lake environment,
   passing the raw/clean directories, unchanged Challenge/Solution/configuration,
   module `Challenge`, pinned Lean binary, and `audit-declarations.json`.
   The exact executed sanitizer command is recorded in `report.json`.

The renderer setup emits a Mathlib manifest advisory because its generated
Lakefile uses the immutable commit and canonical `.git` URL while the source
manifest retains a release-tag input reference. The materialized revision was
checked against the manifest for all 13 dependencies; none was upgraded.
The Challenge's deliberate theorem-hole warnings and upstream Verso warnings
are preserved in the build logs.
