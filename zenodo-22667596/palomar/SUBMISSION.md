# Palomar submission

This directory is a self-contained Lake project within the repository. Its single unified Palomar
entry selects 42 declarations, including the complete Conjecture 24 proof,
its numerical damage-value conclusion, the game results and the normalization
lemmas. All source files needed for the proof are included; Mathlib and its
dependencies are pinned by `lake-manifest.json`.

When ready, review the new directory and root README changes, then commit and
push them yourself. The manuscript PDF and LaTeX source are not included.
Obtain the full SHA with
`git rev-parse HEAD`. Use these fields:

| Field | Value |
|---|---|
| Repository | `https://github.com/lennrt/palomar-formalizations` |
| Commit | The full 40-character commit SHA of the tested source |
| Project path | `zenodo-22667596/palomar` |
| Comparator configuration | `comparator.json` |
| Formalization metadata | `formalization.yaml` |
| Challenge module | `Challenge` |
| Solution module | `Solution` |
| License | `MIT`, in the repository-root `LICENSE` |
| Release | `1.0.0`, 9 September 2026 |

Only when you decide to publish, run from the repository root:

```sh
git diff --check
ruby scripts/check-layout.rb
git add README.md scripts/check-layout.rb zenodo-22667596
git -c user.name="Lennart Rudolph" -c user.email="lrudolph@hmc.edu" commit -m "Add short-cycle zombie-damage formalization"
git push origin main
git rev-parse HEAD
```

These are future instructions, not actions performed during preparation. Git's
author name/email determine commit attribution; do not put access tokens in
files, remote URLs or commits.

The separate `verification/game-comparator.json` is an additional local check
of the independently reconstructed original game statements. Select the root
`comparator.json` for the unified registry entry.

Before submission, run the two verification commands in [README.md](README.md)
and retain their result files with the exact source commit. The repository’s
required literature sweep must also be current before public submission.

Follow [Palomar’s current submission instructions](https://palomar-registry.org/how-to-submit).
A machine submission should use the [official agent protocol](https://submit.palomar-registry.org/llms.txt).
Palomar requires a public immutable source commit and proof of submission
authorization. Local checker success does not create a registry record.

After Palomar’s mechanical checks and automated review, inspect the review
before choosing registration. Registration permanently publishes the entry
and review. A versioned Palomar permalink can be cited once registration is
complete. Until then, share the immutable GitHub source link and describe it
as locally verified source.

Keep the private status-page URL: it is the way back to the review. A later
fix requires a new commit and a new submission. After registration, add the
versioned Palomar link to the paper and publish it separately on Zenodo at
DOI `10.5281/zenodo.22667596`. Update the source-availability note in
`formalization.yaml` when the manuscript is public. The manuscript PDF and
LaTeX source are excluded by the parent `.gitignore`.
