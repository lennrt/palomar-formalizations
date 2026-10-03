# Local verification

The following checks passed on 3 October 2026 for the sources fingerprinted in
[the input manifest](verification/source-inputs.json). Lean 4.35.0-rc2 and all
nine committed dependency revisions were checked; the dependency checkouts
had no tracked source changes.

| Check | Result and evidence |
|---|---|
| Complete Lean project | Build passed; [log](verification/build.log). |
| Selected statements | All 14 passed Comparator with Lean, NanoDa, and con-ron; all 49 input hashes match. [Report](verification/comparison.json). |
| Full-development axiom audits | 112 declarations use only `propext`, `Classical.choice`, and `Quot.sound`. [Report](verification/release.json). |
| Exact finite programs | All 14 passed, including the dimension-16 exhaustive enumeration. [Results](experiments/results) and [run record](verification/release.json). |
| Official metadata and source inspection | Passed for this new project; [report](verification/palomar-preflight.json). |
| Compiler module-header inspection | All 45 source files passed. [Record](verification/render/module-headers.json). |
| Independent statement rendering | All 14 selected signatures passed the trusted core-notation audit, Verso rendering, and official sanitizer. [Report and method](verification/render/README.md). |
| Local significance assessment | No blocker identified across the six selected result groups under the pinned published rubric. [Assessment](verification/local-significance.json). |

The Challenge is 386 lines and 15,009 bytes: within the mandatory limits,
with a nonblocking warning for exceeding the preferred 300-line review size.
Only its independent statement obligations contain deliberate proof holes.
The Solution never imports the Challenge.

These records describe local macOS verification. The explicit comparison
mode does not reproduce the service's Linux sandbox. The significance
assessment is an automated local review, not official Palomar editorial
review, independent human peer review, or registration.

Current repository-wide inspection separately reports 258 legacy files
without module headers. The older registered projects and shared scripts
remain unchanged. This project's success does not erase that external
submission blocker; see [SUBMISSION.md](SUBMISSION.md).

Reproduction commands and the pinned official-tool checkout are in
[README.md](README.md#build-and-verify). Generated renderer assets and local
build caches are not committed.
