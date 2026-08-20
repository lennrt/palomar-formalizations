# Palomar project: signed-circulant arithmetic

`Challenge.lean` exposes the exact four-by-four phase-one block, its quartic,
the characteristic-polynomial identity, and two root-location statements.
`Solution.lean` proves those declarations through explicit wrappers around
`ArithmeticAndMonotonicity`.

The project pins Lean and Mathlib v4.30.0.  Build it with:

```sh
lake exe cache get
lake build
```

The selected declarations use ordinary `decide` for finite matrix equalities;
they do not use `native_decide`, `sorry`, or project axioms.

