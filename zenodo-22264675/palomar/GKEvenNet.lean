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
import GKEvenNet.Rev
import GKEvenNet.Net
import GKEvenNet.Distance
import GKEvenNet.Certificate
import GKEvenNet.Main

/-! Axiom audit of every theorem-bearing declaration. -/

-- bit reversal
#print axioms GKEvenNet.rev_split
#print axioms GKEvenNet.rev_rev
#print axioms GKEvenNet.rev_inj
-- Theorem A (symbolic, every even m ≥ 4)
#print axioms GKEvenNet.xc_eq
#print axioms GKEvenNet.net_inj
#print axioms GKEvenNet.boxMap_bijective
#print axioms GKEvenNet.exists_unique_in_box
#print axioms GKEvenNet.div_pow_eq_iff
#print axioms GKEvenNet.net
-- tiling metric exactness
#print axioms GKEvenNet.cres_sq_le
#print axioms GKEvenNet.cres_sq_exists
#print axioms GKEvenNet.shiftedSq_le_latVal
#print axioms GKEvenNet.shiftedSq_attained
#print axioms GKEvenNet.shiftedSq_eq_iff
-- Theorem B: witness for every even m ≥ 8, exhaustive m = 8
#print axioms GKEvenNet.witness_latVal
#print axioms GKEvenNet.witness_shiftedSq
#print axioms GKEvenNet.lowerCheck_m8
#print axioms GKEvenNet.attain_m8
#print axioms GKEvenNet.attain_m8_spec
#print axioms GKEvenNet.m8_lower
#print axioms GKEvenNet.m8_exact
#print axioms GKEvenNet.distance_upper
#print axioms GKEvenNet.distance_m8_exact
-- definition sanity (kernel-evaluated finite checks)
#print axioms GKEvenNet.netCheck_m4
#print axioms GKEvenNet.netCheck_m6
#print axioms GKEvenNet.netCheck_m8
#print axioms GKEvenNet.netCheck_mutated_m4
