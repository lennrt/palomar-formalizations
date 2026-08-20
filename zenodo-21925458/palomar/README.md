# Palomar project: MSET25 arithmetic companion

This is the intentionally narrow arithmetic companion to the cylindrical
multiset-dimension preprint.  `Challenge.lean` states one unordered-pair
symmetry and the three rational swap identities; `Solution.lean` supplies
explicit wrappers around `MSET25`.

The original Lean v4.19.0 project has been migrated to the Palomar-supported
Lean and Mathlib v4.30.0 pair.  Build it with:

```sh
lake exe cache get
lake build
```

The project contains no `native_decide`, `sorry`, or custom axiom outside the
deliberate Challenge placeholders.

