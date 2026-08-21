/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import K331Tutte.Cockade
import K331Tutte.FiniteLocal

/-!
# Auditable logical reduction

Deep external results are fields of `Inputs`; they are not hidden axioms.  The
formal theorems below verify only their composition.  The paper and validation
report state this boundary explicitly.
-/

namespace K331Tutte

universe u v

structure Vocabulary (Mesh : Type u) (Graph : Type v) where
  graph : Mesh → Graph
  atom : Graph → Prop
  glue : Graph → Graph → Graph → Prop
  safe : Graph → Prop
  ball : Mesh → Prop
  boundaryTriangle : Mesh → Prop
  singleTetrahedron : Mesh → Prop
  nontrivial : Mesh → Prop
  atLeastFive : Graph → Prop
  rigid4 : Graph → Prop
  noK6Minor : Graph → Prop
  nonemptyFourCliqueSeparatorBound : Graph → Prop
  linkless : Graph → Prop
  noK331Minor : Graph → Prop
  fourConnected : Graph → Prop
  admissibleConvexRealization : Mesh → Prop
  embedded : Mesh → Prop

structure Inputs
    {Mesh : Type u} {Graph : Type v}
    (V : Vocabulary Mesh Graph) where
  singleOrNontrivial :
    ∀ m, V.ball m → V.singleTetrahedron m ∨ V.nontrivial m
  singleTetrahedronLinkless :
    ∀ m, V.singleTetrahedron m → V.linkless (V.graph m)
  interiorStarRigidity :
    ∀ m, V.ball m → V.boundaryTriangle m → V.nontrivial m →
      V.rigid4 (V.graph m)
  nontrivialFive :
    ∀ m, V.nontrivial m → V.atLeastFive (V.graph m)
  maderJorgensenEquality :
    ∀ g, V.atLeastFive g → V.rigid4 g → V.noK6Minor g →
      CockadeCertificate V.atom V.glue (fun _ => True) g
  fourCliqueSeparator :
    ∀ m, V.ball m → V.boundaryTriangle m →
      V.nonemptyFourCliqueSeparatorBound (V.graph m)
  separatorPropagation :
    ∀ g, V.nonemptyFourCliqueSeparatorBound g →
      CockadeCertificate V.atom V.glue (fun _ => True) g →
      CockadeCertificate V.atom V.glue V.safe g
  atomLinkless :
    ∀ {g}, V.atom g → V.linkless g
  safeGlueLinkless :
    ∀ {g left right}, V.glue g left right → V.safe g →
      V.linkless left → V.linkless right → V.linkless g
  linklessExcludesK331 :
    ∀ g, V.linkless g → V.noK331Minor g
  alexaEmbeddingTheorem :
    ∀ m, V.ball m → V.boundaryTriangle m →
      V.fourConnected (V.graph m) → V.noK6Minor (V.graph m) →
      V.noK331Minor (V.graph m) → V.admissibleConvexRealization m →
      V.embedded m

theorem structural_linkless
    {Mesh : Type u} {Graph : Type v}
    (V : Vocabulary Mesh Graph) (I : Inputs V) {m : Mesh}
    (hBall : V.ball m) (hBT : V.boundaryTriangle m)
    (hNoK6 : V.noK6Minor (V.graph m)) :
    V.linkless (V.graph m) := by
  rcases I.singleOrNontrivial m hBall with hSingle | hNontrivial
  · exact I.singleTetrahedronLinkless m hSingle
  · have hRigid := I.interiorStarRigidity m hBall hBT hNontrivial
    have hFive := I.nontrivialFive m hNontrivial
    have hCockade := I.maderJorgensenEquality (V.graph m) hFive hRigid hNoK6
    have hSeparator := I.fourCliqueSeparator m hBall hBT
    have hSafeCockade :=
      I.separatorPropagation (V.graph m) hSeparator hCockade
    exact linkless_of_cockade_certificate
      (Atom := V.atom) (Glue := V.glue) (Safe := V.safe)
      (Linkless := V.linkless)
      I.atomLinkless I.safeGlueLinkless hSafeCockade

theorem no_k331_minor_of_no_k6_minor
    {Mesh : Type u} {Graph : Type v}
    (V : Vocabulary Mesh Graph) (I : Inputs V) {m : Mesh}
    (hBall : V.ball m) (hBT : V.boundaryTriangle m)
    (hNoK6 : V.noK6Minor (V.graph m)) :
    V.noK331Minor (V.graph m) :=
  I.linklessExcludesK331 (V.graph m)
    (structural_linkless V I hBall hBT hNoK6)

theorem k331_exclusion_is_redundant
    {Mesh : Type u} {Graph : Type v}
    (V : Vocabulary Mesh Graph) (I : Inputs V) {m : Mesh}
    (hBall : V.ball m) (hBT : V.boundaryTriangle m)
    (hFourConnected : V.fourConnected (V.graph m))
    (hNoK6 : V.noK6Minor (V.graph m))
    (hConvex : V.admissibleConvexRealization m) :
    V.embedded m := by
  exact I.alexaEmbeddingTheorem m hBall hBT hFourConnected hNoK6
    (no_k331_minor_of_no_k6_minor V I hBall hBT hNoK6) hConvex

/- The input interface is consistent.  This trivial model is not mathematical
content; it prevents accidental vacuity caused by an impossible record type. -/
def trivialVocabulary : Vocabulary Unit Unit where
  graph := fun _ => ()
  atom := fun _ => True
  glue := fun _ _ _ => True
  safe := fun _ => True
  ball := fun _ => True
  boundaryTriangle := fun _ => True
  singleTetrahedron := fun _ => True
  nontrivial := fun _ => True
  atLeastFive := fun _ => True
  rigid4 := fun _ => True
  noK6Minor := fun _ => True
  nonemptyFourCliqueSeparatorBound := fun _ => True
  linkless := fun _ => True
  noK331Minor := fun _ => True
  fourConnected := fun _ => True
  admissibleConvexRealization := fun _ => True
  embedded := fun _ => True

noncomputable def trivialInputs : Inputs trivialVocabulary where
  singleOrNontrivial := by
    intro _ _
    exact Or.inl True.intro
  singleTetrahedronLinkless := by
    intro _ _
    exact True.intro
  interiorStarRigidity := by
    intro _ _ _ _
    exact True.intro
  nontrivialFive := by
    intro _ _
    exact True.intro
  maderJorgensenEquality := by
    intro _ _ _ _
    exact .atom trivial
  fourCliqueSeparator := by
    intro _ _ _
    exact True.intro
  separatorPropagation := by
    intro _ _ certificate
    exact certificate
  atomLinkless := by
    intro _ _
    exact True.intro
  safeGlueLinkless := by
    intro _ _ _ _ _ _ _
    exact True.intro
  linklessExcludesK331 := by
    intro _ _
    exact True.intro
  alexaEmbeddingTheorem := by
    intro _ _ _ _ _ _ _
    exact True.intro

noncomputable example : Inputs trivialVocabulary := trivialInputs

#print axioms structural_linkless
#print axioms no_k331_minor_of_no_k6_minor
#print axioms k331_exclusion_is_redundant
#print axioms trivialInputs

end K331Tutte
