# Palomar project: explicit G2 obstruction

Authors: Lennart Rudolph, Sol, Fable

This post-paper Palomar upgrade advertises six declarations in
`Challenge.lean`.  Four retain the original companion's token-order and exact
arithmetic interfaces.  The other two are substantive local proofs: the
paper's general neighbourhood-trace bound for uniform two-word
π-representations and the theorem that its explicit 741,342-vertex
bit-incidence graph `B20` is not representable by two 2-uniform words.

The paper's Section 6 accurately describes the narrower Lean companion that
was archived with the preprint.  This registry package extends that companion
to formalize Theorems 3.1 and 4.1 while leaving the separate compaction
characterization and VC-dimension consequences outside Lean.

The project pins Lean and Mathlib v4.30.0.  Build it with:

```sh
lake exe cache get
lake build
```

`comparator.json` selects only declarations whose transitive proof cones use
no `sorryAx`, `Lean.ofReduceBool`, `native_decide`, or project axiom.
