/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Init

/-!
# Abstract safe-cockade induction

This file checks the recursive logical step used after the graph-theoretic and
topological hypotheses have been proved.  It does not encode spatial graphs or
the Holst-Lovasz-Schrijver theorem.
-/

namespace K331Tutte

universe u

inductive CockadeCertificate
    {Graph : Type u}
    (Atom : Graph → Prop)
    (Glue : Graph → Graph → Graph → Prop)
    (Safe : Graph → Prop) : Graph → Type u where
  | atom {g : Graph} : Atom g → CockadeCertificate Atom Glue Safe g
  | glue {g left right : Graph} :
      CockadeCertificate Atom Glue Safe left →
      CockadeCertificate Atom Glue Safe right →
      Glue g left right → Safe g →
      CockadeCertificate Atom Glue Safe g

theorem linkless_of_cockade_certificate
    {Graph : Type u}
    {Atom : Graph → Prop}
    {Glue : Graph → Graph → Graph → Prop}
    {Safe Linkless : Graph → Prop}
    (atomLinkless : ∀ {g}, Atom g → Linkless g)
    (safeGlueLinkless :
      ∀ {g left right}, Glue g left right → Safe g →
        Linkless left → Linkless right → Linkless g)
    {g : Graph}
    (certificate : CockadeCertificate Atom Glue Safe g) :
    Linkless g := by
  induction certificate with
  | atom h => exact atomLinkless h
  | glue _ _ hGlue hSafe ihLeft ihRight =>
      exact safeGlueLinkless hGlue hSafe ihLeft ihRight

theorem four_plus_components_lt_seven
    {components : Nat} (h : components ≤ 2) :
    4 + components < 7 := by omega

#print axioms linkless_of_cockade_certificate
#print axioms four_plus_components_lt_seven

end K331Tutte
