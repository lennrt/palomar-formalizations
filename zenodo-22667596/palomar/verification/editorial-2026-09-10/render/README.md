# Trusted rendering and scope verification

The revised `Challenge.lean` passed the unmodified trusted rendering core from
PalomarSubmission commit `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763` on
10 September 2026 UTC. The literate build, core-notation signature audit,
Verso HTML generation and official sanitizer all exited successfully for
the 39 selected declarations. Reports and actual command logs are preserved
here. The generated HTML/assets remain in the local rendering cache; they are
not additional mathematical sources.

`statement-preservation.json` records a separate token comparison against
commit `c52864a39eb96a92ff9393e3b8bc62f98b196553`: after removing the two
sensing-only source blocks and ignoring comments/whitespace, every retained
Challenge token is unchanged. Exactly the three named sensing declarations
were removed from the Comparator configuration, with all other configuration
fields and selection order preserved.

`challenge-allowlist.json` records a fresh official source-dependency audit:
Mathlib is allowlisted, no untrusted source is present, and trust is high.
The canonical Mathlib history was fetched from its public GitHub repository;
the pinned checkout `81a5d257c8e410db227a6665ed08f64fea08e997` was verified
as an ancestor of canonical head `01c8d16a8c31eed40a54a38a8c8006c4ee001152`.
The dependency checkout remained clean and at its pinned revision.

The reused local rendering cache emits a Lake manifest advisory. Its
requirement spells the Mathlib commit while the merged manifest retains the
source project's `v4.32.0` input reference. The actual manifest revision and
checkout HEAD both equal the exact pinned revision above; no dependency
upgrade was performed. This advisory is preserved in the stderr logs.

These are local macOS checks, not a hosted Linux Landrun/systemd confinement
execution or a Palomar editorial decision. The 902-line, 49,366-byte Challenge
remains above the preferred review-size advisory but below the hard
1,000-line and 100-KiB limits.
