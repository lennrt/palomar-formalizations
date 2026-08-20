/-
Paper: Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892986
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import RegularPathDelay

/-! Proof-bearing wrappers for the declarations in `Challenge.lean`. -/

namespace PalomarRegularPathDelay

open RegularPathDelay

theorem vertex_split_model_equivalence
    {α : Type} {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (hsupport : ∀ ⦃u v⦄, (u, v) ∈ arcs → u ∈ vertices ∧ v ∈ vertices) :
    SplitArcClashFree bar (LiftedArcs vertices arcs) ↔
      VertexClashFree bar vertices := by
  exact RegularPathDelay.vertexSplit_model_equivalence hsupport

theorem split_walk_lift_nodes_iff
    {α : Type} {edge : α → α → Prop} {bar : α → α} (xs : List α) :
    Walk (SplitEdge edge bar) (liftNodes xs) ↔
      Walk (fun u v => edge u v ∧ v ≠ bar u) xs := by
  exact RegularPathDelay.splitWalk_liftNodes_iff xs

theorem regular_extension_with_reachability
    {α : Type} {edge : α → α → Prop} {bar : α → α}
    {old tail : List α} {s v w t : α} {k ℓ : Nat}
    (hinvol : ∀ x, bar (bar x) = x)
    (hprefixRegular : Regular bar (old ++ [w]))
    (hsuffixRegular : Regular bar (w :: tail))
    (hsurvives : SuffixSurvives bar old tail)
    (hprefixReach : Relation.RelatesInSteps edge s v k)
    (hvw : edge v w)
    (hw : Survives bar old w) (ht : Survives bar old t)
    (hsuffixReach : Relation.RelatesInSteps
      (InducedAfterDeletion edge bar old) ⟨w, hw⟩ ⟨t, ht⟩ ℓ) :
    Regular bar (old ++ w :: tail) ∧
      Relation.RelatesInSteps edge s t (k + (ℓ + 1)) := by
  exact RegularPathDelay.regular_and_reachability_join_induced
    hinvol hprefixRegular hsuffixRegular hsurvives
    hprefixReach hvw hw ht hsuffixReach

end PalomarRegularPathDelay

