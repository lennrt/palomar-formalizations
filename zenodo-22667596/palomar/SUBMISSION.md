# Palomar submission

This directory is a self-contained Lake project within the repository. Its Palomar
configuration selects 39 pursuit and short-cycle declarations, including the complete Conjecture 24 proof,
its numerical damage-value conclusion, the game results and the normalization
lemmas. All source files needed for the proof are included; Mathlib and its
dependencies are pinned by `lake-manifest.json`.

Use the full 40-character SHA of the tested, pushed revision, obtained with
`git rev-parse HEAD`. The manuscript PDF and LaTeX source are not included.
Use these fields:

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
| Release | `1.0.0`, with the 10 September 2026 selection revision |

Check the exact source before submission, from the repository root:

```sh
git diff --check
ruby scripts/check-layout.rb
git rev-parse HEAD
```

The separate `verification/game-comparator.json` is an additional regression
check of the independently reconstructed original game statements. It retains
two supplementary sensing results and is not the submission configuration.
Select the root `comparator.json` for the pursuit entry; the distance-shell
obstruction and diamond-ring sensing results are not selected there.

Before submission, run the two verification commands in [README.md](README.md)
and retain their result files with the exact source commit. The repository’s
required literature sweep must also be current before public submission.

Follow [Palomar’s current submission instructions](https://palomar-registry.org/how-to-submit).
A machine submission should use the [official agent protocol](https://submit.palomar-registry.org/llms.txt).
Palomar requires a public immutable source commit and proof of submission
authorization. Local checker success does not create a registry record.

Submit this revised commit as a new submission. Leave the existing Palomar ID
blank unless the result has already been registered publicly. A prior private
submission or its status page is not an existing public registry entry.

After Palomar’s mechanical checks and automated review, inspect the review
before choosing registration. Registration permanently publishes the entry
and review. A versioned Palomar permalink can be cited once registration is
complete.

Keep the private status-page URL: it is the way back to the review. A later
fix requires a new commit and a new submission. After registration, add the
versioned Palomar link to the paper and publish it separately on Zenodo at
DOI `10.5281/zenodo.22667596`. The manuscript PDF and
LaTeX source are excluded by the parent `.gitignore`.
