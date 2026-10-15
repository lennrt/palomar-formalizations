# Submission entry point

Project path: `zenodo-23304384/palomar`.

- Toolchain: `leanprover/lean4:v4.35.0-rc2`.
- Challenge: `Challenge.lean`, module `Challenge`.
- Solution: `Solution.lean`, module `Solution`.
- Declaration selection: `comparator.json` (ten declarations).
- Metadata: `formalization.yaml` v0.4.
- Canonical paper DOI: `10.5281/zenodo.23252713`.
- Pinned manuscript/supplement provenance: Zenodo record `23304384`, version 2.0.0.

The substantive proofs and scripts are included. The submitted project is not
an interface that assumes the paper's theorems or depends on another project's
unpublished object files. The Challenge uses only Mathlib and defines its
observation model independently; the Solution uses the supplied local proof
library, ported to public modules.

Run the repository's local release checker against a clean checkout of the
official `PalomarRegistry/PalomarSubmission` tooling:

```sh
python3 ../../scripts/verify-local.py --help
```

Use the invocation recorded by the generated verification report. Local
metadata/source-policy validation, rendering, statement comparison and kernel
checking provide reviewable evidence for those checks. They do not submit or
register the work, and do not establish Palomar's editorial significance verdict.
The public motivation and scope account are in README.md; precise endpoint
fidelity is in DECLARATIONS.md and formalization.yaml.

The strongest completed theorem concerns known-rate two-leg recovery. The full
sampling probability guarantee and other paper-level results listed in the
coverage limits remain outside the formal claims. No request to review or
register the complete paper should be read as certifying those missing parts.
