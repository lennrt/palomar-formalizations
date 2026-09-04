/-
Paper: The Even-Order Grünschloß–Keller Permutation Nets Are (0,m,2)-Nets
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.22264675
Preprint version 1.0.0 dated 2026-09-03; Palomar formalization packaged 2026-09-03.
Declaration of generative-AI use: Anthropic Claude and OpenAI Codex were used for
literature searches, algebraic exploration, proof and checker drafting, the Lean
formalization, and adversarial review; the author accepts full responsibility for
the claims, and no AI system is an author.
-/
import GKEvenNet

/-!
# Proved solution

The advertised declarations are provided by the imported, fully proved `GKEvenNet`
development.  `net` is a symbolic proof for every even `m ≥ 4` (no finite enumeration);
`distance_upper` is a symbolic evaluation of one pair for every even `m ≥ 8`; the lower
bound inside `distance_m8_exact` is an exhaustive check over all pairs at `m = 8` reduced by
ordinary kernel `decide`, combined with a symbolic proof that the checked quantity is the
exact lattice minimum.  Only ordinary kernel reduction is used; no custom axioms.
-/

#print axioms GKEvenNet.net
#print axioms GKEvenNet.distance_upper
#print axioms GKEvenNet.distance_m8_exact
