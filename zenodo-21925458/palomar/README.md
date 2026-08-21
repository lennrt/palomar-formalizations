# Palomar project: the even-cylinder resolving construction

Authors: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), Sol, Fable

This Lean project formalizes the graph-theoretic core of the paper's infinite
family. It defines the coordinate model and standard distance on
`P_m □ C_(6m)`, proves the four-piece cycle distance-pair locus from Lemma 1,
and proves that `(0,0)`, `(0,2m)`, and `(m-1,0)` form a multiset resolving set
for every even `m ≥ 2`.

The formalization establishes the three-landmark upper bound. It does not
formalize the general theorem that a connected non-path graph has multiset
dimension at least three, so it does not claim basis minimality or the exact
dimension equality. The finite exhaustive census also remains outside Lean.

The original Lean v4.19.0 project has been migrated to the Palomar-supported
Lean and Mathlib v4.30.0 pair. Build it with:

```sh
lake exe cache get
lake build
```

`Challenge.lean` contains only the compared theorem placeholders;
`Solution.lean` supplies the proofs. The solution contains no `sorry`,
`native_decide`, or custom axiom.
