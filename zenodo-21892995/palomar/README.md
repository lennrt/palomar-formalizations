# Palomar project: signed-circulant Bloch algebra

Authors: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), Sol, Fable

`Challenge.lean` exposes the paper's exact phase-dependent `8 × 8` Bloch
symbol, with independent variables `z` and `zInv`, together with four compared
results:

- phase reversal transposes the displayed symbol;
- a fraction-free determinant expansion with an explicit correction divisible
  by `z*zInv - 1`;
- the paper's identity `det(xI-B(z)) = F(x^2,z+z^{-1})` under
  `z*zInv = 1`; and
- an all-phase algebraic band-edge certificate locating the phase-one root,
  comparing it with the nested-radical target, proving `F(t0,y) ≥ 0` for
  `y ∈ [-2,2]` with strictness for `y < 2`, and excluding every zero above
  `t0`.

`Solution.lean` proves the determinant identity directly from the exact matrix
entries and combines the arithmetic and monotonicity lemmas in
`ArithmeticAndMonotonicity.lean` into the final all-phase certificate.

The formalized result is algebraic. It does not formalize the Fourier
direct-integral decomposition, the spectral theorem or operator-norm
identification, finite-quotient sampling, the paper's `32 × 32`
characteristic-polynomial/Sturm computation, or the exhaustive
period-at-most-16 classification.

The project pins Lean and Mathlib v4.30.0. Build it with:

```sh
lake exe cache get
lake build
```

The selected proofs use ordinary kernel-checked tactics. They do not use
`native_decide`, `sorry`, or project axioms; their reported axioms are
`propext`, `Quot.sound`, and `Classical.choice`.
