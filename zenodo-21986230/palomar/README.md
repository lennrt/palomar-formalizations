# Palomar project: G2 companion

This project advertises four scoped declarations in `Challenge.lean` and
proves the same declarations in `Solution.lean` by explicit wrappers around
`G2Companion.OrderBridge`.

The project pins Lean and Mathlib v4.30.0.  Build it with:

```sh
lake exe cache get
lake build
```

`comparator.json` selects only declarations whose transitive proof cones use
no `sorryAx`, `Lean.ofReduceBool`, `native_decide`, or project axiom.

