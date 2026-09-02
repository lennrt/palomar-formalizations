# Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification

DOI: [10.5281/zenodo.21892995](https://doi.org/10.5281/zenodo.21892995)

Paper author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X)) — the sole
author of record on the cited Zenodo deposit.

Formalization authors: Lennart Rudolph, Sol, Fable.

This directory contains the standalone Palomar project in `palomar/`.

The compared Lean theorem group formalizes the paper's disproof of Suvagiya's
signed-circulant minimum conjecture (arXiv:2607.18334, Conjecture 3) on the
infinite arithmetic progression n ≡ 0 (mod 8), n ≥ 32, together with the
exact Bloch-determinant layer behind it.

The matrix layer defines the paper's period-8 triangle-flux signing of
C_n(1,2) as an explicit signed adjacency matrix over `ZMod n` and proves:
it is a ±1 signing of mathlib's `circulantGraph {1, 2}`
(`signedAdjacency_isCirculantSigning`); the Rayleigh bound
`|vᵀAv| ≤ (1397/500)‖v‖²` for every real vector, by two exact rational
sum-of-squares window certificates whose period-8 local forms telescope to
`(1397/500)·I ∓ A` for every quotient order at once (`rayleigh_band_bound`);
the eigenvalue corollary `|μ| ≤ 1397/500` for every real eigenpair
(`eigenvalue_band_bound`); the strict comparison `1397/500 < ρ₋(n)` for all
n ≥ 32, where `ρ₋(n) = 2·√(cos²(π/n)+cos²(2π/n))` is the conjectured
minimum, via the closed forms of cos(π/8) and cos(π/16) and the project's
nested-radical bounds (`separator_lt_twisted_value`); and the bundled
disproof (`periodic_signing_beats_twisted_class`): for every n ≡ 0 (mod 8)
with n ≥ 32 there is an explicit signing of C_n(1,2) whose eigenvalues all
lie strictly below the conjectured minimum.

The supporting layer is unchanged: the paper's full phase-dependent 8×8
Bloch symbol, its fraction-free determinant expansion, the specialization
`det(xI−B(z)) = F(x², z+z⁻¹)`, and the all-phase algebraic band-edge
certificate.

Deliberately external, as documented in `formalization.yaml`: the exact
common radius √t₀ (both directions of Theorem 2.1's equality), the infinite
operator and its direct integral, Sturm's theorem, and the exhaustive
period-≤16 classification of Theorem 4.1.

The compared declarations have no `sorry`, no `native_decide`, and use only
`propext`, `Quot.sound`, and `Classical.choice`.

To verify:

```sh
cd palomar
lake exe cache get
lake build
```
