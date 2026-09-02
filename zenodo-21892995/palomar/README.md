# Palomar project: a periodic signing of C_n(1,2) below the conjectured minimum

Formalization authors: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)), Sol, Fable.
The cited paper is by Lennart Rudolph alone.

Nine declarations are compared, in two layers.

## Disproof layer

For every `n` divisible by 8, `signedAdjacency` is the paper's period-8
triangle-flux signing of `C_n(1,2)` as an explicit signed adjacency matrix
over `ZMod n`: every step-1 edge positive, the step-2 edge at `i` signed by
the flux word `(+1,−1,+1,−1,−1,+1,−1,+1)` read through the reduction
`ZMod n → ZMod 8`.

- `signedAdjacency_isCirculantSigning` — the matrix is a symmetric ±1 signing
  of mathlib's `SimpleGraph.circulantGraph {1, 2}`, and vanishes off its
  edges.
- `rayleigh_band_bound` — `|vᵀAv| ≤ (1397/500)·‖v‖²` for **every** real
  vector `v`, proved from two exact rational sum-of-squares window
  certificates whose period-8 local forms telescope to `(1397/500)·I ∓ A` for
  every quotient order at once. The certificate data is rational; every
  property used of it is re-proved in Lean by residue exhaustion, so no
  floating-point search is trusted by the proof.
- `eigenvalue_band_bound` — every real eigenpair of that matrix satisfies
  `|μ| ≤ 1397/500`, derived from the Rayleigh bound.
- `separator_lt_twisted_value` — `1397/500 < ρ₋(n)` for every `n ≥ 32`, where
  `ρ₋(n) = 2·√(cos²(π/n)+cos²(2π/n))` is the conjectured minimum, via the
  closed forms of `cos(π/8)` and `cos(π/16)` and the nested-radical bounds in
  `ArithmeticAndMonotonicity.lean`.
- `periodic_signing_beats_twisted_class` — the bundle: for every
  `n ≡ 0 (mod 8)` with `n ≥ 32` there is an explicit ±1 signing of
  `C_n(1,2)` whose real eigenvalues all lie strictly below `ρ₋(n)`. This
  contradicts Conjecture 3 of Suvagiya, *Signed circulants at the Ramanujan
  bound* (arXiv:2607.18334), on an infinite arithmetic progression.

## Bloch algebra layer

`Challenge.lean` also exposes the paper's exact phase-dependent `8 × 8` Bloch
symbol, with independent variables `z` and `zInv`, and four compared results:

- `bloch_symbol_phase_reversal` — phase reversal transposes the displayed
  symbol;
- `bloch_determinant_with_correction` — a fraction-free determinant expansion
  with an explicit correction divisible by `z*zInv - 1`;
- `bloch_determinant_identity` — the paper's identity
  `det(xI-B(z)) = F(x^2,z+z^{-1})` under `z*zInv = 1`;
- `algebraic_band_edge_certificate` — an all-phase algebraic band-edge
  certificate locating the phase-one root, comparing it with the
  nested-radical target, proving `F(t0,y) ≥ 0` for `y ∈ [-2,2]` with
  strictness for `y < 2`, and excluding every zero above `t0`.

## Scope

The eigenvalue statements quantify over **real eigenpairs**. For a real
symmetric matrix that is the whole spectrum, but the spectral theorem is not
imported and is not asserted here: the uniform statement carrying the content
is `rayleigh_band_bound`, over all real vectors, and the eigenvalue bound is
derived from it.

Not formalized: the identification of the exact common radius `√t₀` (either
direction of Theorem 2.1's equality), the infinite operator and its
direct-integral decomposition, finite-quotient sampling, Sturm's theorem and
the paper's `32 × 32` characteristic-polynomial computation, and the
exhaustive period-at-most-16 classification of Theorem 4.1.

The project pins Lean and Mathlib v4.30.0. Build it with:

```sh
lake exe cache get
lake build
```

The selected proofs use ordinary kernel-checked tactics. They do not use
`native_decide`, `sorry`, or project axioms; their reported axioms are
`propext`, `Quot.sound`, and `Classical.choice`.
