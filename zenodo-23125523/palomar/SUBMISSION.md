# Palomar submission configuration

The nested project contains the substantive proof library and an independent
14-statement interface. The selection covers six groups: square-grid sensing,
hypercube equalization, bishop domination, Petersen domination, fractional
optimal faces, and rectangular sensing. Supporting modules remain included.

| Field | Value |
|---|---|
| Repository | `https://github.com/lennrt/palomar-formalizations` |
| Commit | Full 40-character SHA of the final tested, pushed source |
| Project path | `zenodo-23125523/palomar` |
| Comparator configuration | `comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Challenge module | `Challenge` |
| Solution module | `Solution` |
| Toolchain | `leanprover/lean4:v4.35.0-rc2` |
| License | Repository-root `LICENSE` (MIT) |
| Associated paper | `10.5281/zenodo.23125523` |

The manuscript PDF and LaTeX source are published at
[Zenodo](https://doi.org/10.5281/zenodo.23125523); they are not needed to build
this Lean project. Bibliographic and authorship metadata are in
[formalization.yaml](formalization.yaml), and the selected mathematical
statements are explained in [DECLARATIONS.md](DECLARATIONS.md).

## Checks and submission scope

Run the build, audits, comparison, and exact verification commands in
[README.md](README.md#build-and-verify). Retain their results together with
the exact source commit and verify that recorded input hashes still match.
After any change to `Challenge.lean`, `Solution.lean`, or `comparator.json`,
rerun the comparison rather than citing a previous selection's success.

The project-specific `scripts/check_snapshot.py` checks the local structure.
Run `scripts/verify_palomar.py --submission-tools /path/to/PalomarSubmission`
with PyYAML and the clean official tooling checkout pinned in that script
for metadata and source-policy inspection. Its report records project and
repository-wide results separately, and either scope failing makes the command
fail. The repository-level `ruby scripts/check-layout.rb` now covers all 13
projects and checks module headers and the per-file source limit.

The [current Palomar submission instructions](https://palomar-registry.org/how-to-submit)
require module headers and a size limit for every regular Lean source file
in the submitted repository, including unused sibling projects. The older
projects have been migrated while retaining their existing build pins;
[MODULE-MIGRATION.md](../../MODULE-MIGRATION.md) records the checks.
Submit a commit containing that migration. This project's Lean sources,
14 selected statements, and 4.35.0-rc2 toolchain remain unchanged.

The [local significance assessment](verification/local-significance.json) is
an advisory review of the selected statements. It is not Palomar's editorial
review or approval. The local macOS
comparison mode also does not reproduce the service's Linux confinement.
No service verification or registry registration is claimed here.

## Eventual submission

Use a public immutable commit containing the tested files; obtain its full
SHA with `git rev-parse HEAD`. Follow the
[official submission instructions](https://palomar-registry.org/how-to-submit)
and, for machine intake, the
[agent protocol](https://submit.palomar-registry.org/llms.txt).
Submission requires authorization from a responsible author or maintainer.
This document records the intended entry point and does not submit it.

Keep the private status-page URL and inspect any review before choosing
registration. Registration is a separate action. Do not invent an existing
Palomar identifier; use one only if a corresponding public record exists.
