/-
Paper: An Explicit Obstruction to Uniform Two-Word π-Representability
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21986230
Preprint published: 2026-08-18. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import G2Companion

namespace PalomarG2

theorem fibre_agreement_iff_no_cross_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k)) {x y : V} (hxy : x ≠ y) :
    (∀ i j : Fin k, L₁.lt (x, i) (y, j) ↔ L₂.lt (x, i) (y, j)) ↔
      ¬ ∃ i j : Fin k,
        (L₁.lt (x, i) (y, j) ∧ L₂.lt (y, j) (x, i)) ∨
        (L₁.lt (y, j) (x, i) ∧ L₂.lt (x, i) (y, j)) := by
  simpa only [G2Companion.FibreAgreement, G2Companion.QuotientEdge,
    G2Companion.inversionAdj] using
    G2Companion.fibreAgreement_iff_not_quotientEdge L₁ L₂ hxy

theorem same_fibre_no_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k))
    (h₁ : ∀ x i j, L₁.lt (x, i) (x, j) ↔ i < j)
    (h₂ : ∀ x i j, L₂.lt (x, i) (x, j) ↔ i < j)
    (x : V) (i j : Fin k) :
    ¬ ((L₁.lt (x, i) (x, j) ∧ L₂.lt (x, j) (x, i)) ∨
       (L₁.lt (x, j) (x, i) ∧ L₂.lt (x, i) (x, j))) := by
  simpa only [G2Companion.FibreMonotone, G2Companion.inversionAdj] using
    G2Companion.sameFibre_noInversion L₁ L₂ h₁ h₂ x i j

theorem trace_capacity_endpoint : (Nat.choose 42 2) ^ 2 + 20 < 2 ^ 20 := by
  exact G2Companion.vcDimensionEndpoint_2_20

theorem no_trace_code_injection :
    ¬ ∃ f : Fin 741322 → Fin 741321, Function.Injective f := by
  exact G2Companion.no_trace_code_injection

#print axioms fibre_agreement_iff_no_cross_inversion
#print axioms same_fibre_no_inversion
#print axioms trace_capacity_endpoint
#print axioms no_trace_code_injection

end PalomarG2
