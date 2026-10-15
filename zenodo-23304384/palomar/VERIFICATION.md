# Verification evidence

The pinned Lean project includes all supplied proof modules and an independent
ten-statement Challenge. Local build and axiom-audit logs are written under
`verification/`. The repository release checker records metadata, source policy,
statement comparison, independent-kernel and rendering results with input hashes.
Only completed successful reports for the current files count as evidence.

The Challenge intentionally contains ten theorem holes. No Solution or library
module imports Challenge; proofs must use only `propext`, `Classical.choice`,
and `Quot.sound`. Exact supplemental Python checks exercise the decoder,
streaming statistics and design inequalities; their output is separate from
Lean proof certification.

Local checker success does not constitute Palomar service execution,
registration, an editorial notability decision, independent human peer review,
or a proof of unformalized portions of the manuscript. Source fidelity and
formal scope are documented in DECLARATIONS.md and README.md.
