/-
Paper: Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21892986
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Cslib.Foundations.Data.RelatesInSteps

/-!
# Auditable statement surface for regular-path enumeration

The definitions below are copied from the proof development because they are
part of the mathematical statement. The three advertised theorems isolate the
formalized core: vertex/arc clash equivalence after splitting, the exact walk
lift, and the prefix-deletion regularity plus reachability join. They do not
state correctness or complexity of the executable enumerator.
-/

namespace RegularPathDelay

variable {α : Type}

inductive SplitNode (α : Type) where
  | minus : α → SplitNode α
  | plus : α → SplitNode α

def splitNodeBar (bar : α → α) : SplitNode α → SplitNode α
  | .minus v => .plus (bar v)
  | .plus v => .minus (bar v)

inductive SplitArc (α : Type) where
  | internal : α → SplitArc α
  | transfer : α → α → SplitArc α

def splitArcBar (bar : α → α) : SplitArc α → SplitArc α
  | .internal v => .internal (bar v)
  | .transfer u v => .transfer (bar v) (bar u)

def VertexClashFree (bar : α → α) (vertices : Set α) : Prop :=
  ∀ ⦃v⦄, v ∈ vertices → bar v ∉ vertices

def SplitArcClashFree (bar : α → α) (arcs : Set (SplitArc α)) : Prop :=
  ∀ ⦃a⦄, a ∈ arcs → splitArcBar bar a ∉ arcs

def LiftedArcs (vertices : Set α) (arcs : Set (α × α)) : Set (SplitArc α)
  | .internal v => v ∈ vertices
  | .transfer u v => (u, v) ∈ arcs

def SplitEdge (edge : α → α → Prop) (bar : α → α) :
    SplitNode α → SplitNode α → Prop
  | .minus u, .plus v => u = v
  | .plus u, .minus v => edge u v ∧ v ≠ bar u
  | _, _ => False

def Walk (edge : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | u :: v :: tail => edge u v ∧ Walk edge (v :: tail)

def liftNodes : List α → List (SplitNode α)
  | [] => []
  | v :: tail => .minus v :: .plus v :: liftNodes tail

def Compatible (bar : α → α) (x y : α) : Prop :=
  x ≠ y ∧ bar x ≠ y ∧ x ≠ bar y

def Regular (bar : α → α) (xs : List α) : Prop :=
  xs.Pairwise (Compatible bar)

def Survives (bar : α → α) (old : List α) (y : α) : Prop :=
  y ∉ old ∧ bar y ∉ old

def SuffixSurvives (bar : α → α) (old tail : List α) : Prop :=
  ∀ y ∈ tail, Survives bar old y

def InducedAfterDeletion
    (edge : α → α → Prop) (bar : α → α) (old : List α) :
    {x // Survives bar old x} → {x // Survives bar old x} → Prop :=
  fun x y => edge x.1 y.1

end RegularPathDelay

namespace PalomarRegularPathDelay

open RegularPathDelay

/-- Supported vertex traces are clash-free exactly when their split arcs are. -/
theorem vertex_split_model_equivalence
    {α : Type} {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (hsupport : ∀ ⦃u v⦄, (u, v) ∈ arcs → u ∈ vertices ∧ v ∈ vertices) :
    SplitArcClashFree bar (LiftedArcs vertices arcs) ↔
      VertexClashFree bar vertices := by
  sorry

/-- Alternating vertex splitting preserves exactly the walks with unit arcs removed. -/
theorem split_walk_lift_nodes_iff
    {α : Type} {edge : α → α → Prop} {bar : α → α} (xs : List α) :
    Walk (SplitEdge edge bar) (liftNodes xs) ↔
      Walk (fun u v => edge u v ∧ v ≠ bar u) xs := by
  sorry

/-- One accepted suffix joins both as a regular list and as an exact-length walk. -/
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
  sorry

end PalomarRegularPathDelay

