# Mechanical verification and rendering

The project pins Lean and Mathlib 4.30.0. Its manifest records a full lowercase
40-character commit for every Git dependency. The Challenge imports only Mathlib,
is below Palomar's warning thresholds, and contains exactly the eight expected
statement placeholders. The Solution and the complete project proof source contain
no `sorry`, `admit`, custom axiom, `native_decide`, `Lean.ofReduceBool`, `opaque`, or
`unsafe` declaration.

The eight compared declarations are replayed by Lean's kernel, and `AxiomAudit.lean`
prints their transitive axiom sets. The only permitted axioms are `propext`,
`Quot.sound`, and `Classical.choice`. The source Zenodo release also contains the
executed Comparator/NanoDa log and independent finite regression evidence; none of
those finite programs is trusted for an all-order theorem.

Local reproduction from this directory:

```sh
lake exe cache get
lake build
lake env lean AxiomAudit.lean
```

The repository-root command `ruby scripts/check-layout.rb` checks the monorepo
layout, metadata, dependency revisions, Challenge size, proof-hole scan, and
Comparator configuration. `COVERAGE.md` records theorem-by-theorem alignment with
the paper, while `NOTABILITY.md` explains the research-interest case.

## Fresh local verification (2026-09-07 UTC)

- A clean source-only copy completed `lake build` (2,994 jobs), including the
  standalone Challenge.
- `AxiomAudit.lean` reported exactly `propext`, `Quot.sound`, and
  `Classical.choice` for each of the eight compared declarations.
- Comparator
  `575674928e239f5bc452aab72d1dd7b0f1326494`, Lean-4.30 lean4export
  `a3e35a584f59b390667db7269cd37fca8575e4bf`, and NanoDa
  `68d5ca9db226849b41a6fff59d796ff19d0a8840` accepted the solution. The
  final Comparator result was `Your solution is okay!`.
- The current Palomar renderer at PalomarSubmission
  `c605f23466450a52999fcfb3c6d68ed8febc56bf`, with Verso
  `8bcbd2b8723307c329c12997a0c16a6ac174d3e9`, built and sanitized the
  Challenge successfully. All eight declaration anchors rendered in a headless
  browser without clipping or horizontal overflow.
- The repository layout check passed all eleven projects. The only warnings were
  pre-existing Challenge-size warnings in two older projects.

Landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` was included in the local
Comparator stack, but macOS cannot reproduce Palomar's Linux Landlock confinement.
The proof comparison and both kernel replays are meaningful local checks; sandbox
confinement and report attestation remain server-only checks.

Palomar's authoritative protected checkout, Comparator/NanoDa replay, editorial
decision, and final Verso rendering operate on an immutable pushed commit. Local
checks can closely reproduce those stages but do not claim an official registry
decision before submission.
