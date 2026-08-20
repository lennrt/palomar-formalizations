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
# Model and prefix interfaces for regular-path enumeration

This file checks selected interfaces used by the polynomial-delay enumerator.
It formalizes the vertex-splitting involutions, removal of fixed transfer
arcs, skew-symmetry of the split edge relation, the regularity equivalence for
supported lifted traces, and the exact alternating-walk lift.  It also gives
an abstract exact completion-oracle interface and two recursion-tree facts.

For prefix deletion, a list is regular when no two entries are equal or
paired by the fixed-point-free involution `bar`.  Once `old ++ [z]` is fixed,
a suffix `z :: tail` can be joined exactly when every vertex of `tail`
survives deletion of `old` and its mates.  CSLib's fixed-length relational
reachability checks the graph-edge composition with the exact combined
length.  These witnesses are walks: the file does not formalize simple graph
paths, the fresh endpoint gadget, the Goldberg--Karzanov implementation, or
the executable enumerator and its complexity.
-/

namespace RegularPathDelay

variable {α : Type}

/-- The complement data assumed by the mathematical graph model.

The list lemmas below need only involutivity, so they retain that weaker
hypothesis explicitly.  This structure records the additional fixed-point-free
assumption used for skew-symmetric digraph vertices. -/
structure ComplementedType (α : Type) where
  bar : α → α
  involutive : ∀ x, bar (bar x) = x
  fixedPointFree : ∀ x, bar x ≠ x

/-! ## Vertex splitting

The paper reduces vertex-regular reachability to the arc-regular model of
Goldberg--Karzanov.  The next definitions formalize the model interface.  A
split node records whether it is the incoming or outgoing copy of an original
vertex.  Internal split arcs record use of a vertex, while transfer arcs
record original graph arcs. -/

/-- The incoming and outgoing copies used by vertex splitting. -/
inductive SplitNode (α : Type) where
  | minus : α → SplitNode α
  | plus : α → SplitNode α

/-- Complementation swaps polarity and complements the original vertex. -/
def splitNodeBar (bar : α → α) : SplitNode α → SplitNode α
  | .minus v => .plus (bar v)
  | .plus v => .minus (bar v)

theorem splitNodeBar_involutive
    {bar : α → α} (hinvol : ∀ x, bar (bar x) = x) :
    ∀ x, splitNodeBar bar (splitNodeBar bar x) = x
  | .minus v => by simp [splitNodeBar, hinvol]
  | .plus v => by simp [splitNodeBar, hinvol]

theorem splitNodeBar_ne_self {bar : α → α} :
    ∀ x, splitNodeBar bar x ≠ x
  | .minus _ => by simp [splitNodeBar]
  | .plus _ => by simp [splitNodeBar]

/-- The two kinds of arcs in an alternating split trace. -/
inductive SplitArc (α : Type) where
  | internal : α → SplitArc α
  | transfer : α → α → SplitArc α

/-- Arc complementation in the split model. -/
def splitArcBar (bar : α → α) : SplitArc α → SplitArc α
  | .internal v => .internal (bar v)
  | .transfer u v => .transfer (bar v) (bar u)

theorem splitArcBar_involutive
    {bar : α → α} (hinvol : ∀ x, bar (bar x) = x) :
    ∀ a, splitArcBar bar (splitArcBar bar a) = a
  | .internal v => by simp [splitArcBar, hinvol]
  | .transfer u v => by simp [splitArcBar, hinvol]

/-- Unit transfer arcs are exactly the possible fixed arcs and are deleted by
the reduction before invoking the external arc-regular oracle. -/
def NonUnitSplitArc (bar : α → α) : SplitArc α → Prop
  | .internal _ => True
  | .transfer u v => v ≠ bar u

/-- A transfer arc coming from a unit arc is fixed by the split-arc mate
operation. -/
theorem splitArcBar_unit
    {bar : α → α} (hinvol : ∀ x, bar (bar x) = x) (u : α) :
    splitArcBar bar (.transfer u (bar u)) = .transfer u (bar u) := by
  simp [splitArcBar, hinvol]

theorem splitArcBar_ne_self
    {bar : α → α}
    (hfree : ∀ x, bar x ≠ x)
    {a : SplitArc α} (ha : NonUnitSplitArc bar a) :
    splitArcBar bar a ≠ a := by
  cases a with
  | internal v =>
      simp only [splitArcBar]
      intro h
      exact hfree v (SplitArc.internal.inj h)
  | transfer u v =>
      simp only [splitArcBar]
      intro h
      have hv : bar u = v := (SplitArc.transfer.inj h).2
      exact ha hv.symm

/-- Vertex clash-freeness, separated from list order and simplicity. -/
def VertexClashFree (bar : α → α) (vertices : Set α) : Prop :=
  ∀ ⦃v⦄, v ∈ vertices → bar v ∉ vertices

/-- Arc clash-freeness in the split model. -/
def SplitArcClashFree (bar : α → α) (arcs : Set (SplitArc α)) : Prop :=
  ∀ ⦃a⦄, a ∈ arcs → splitArcBar bar a ∉ arcs

/-- Split arcs induced by an original vertex set and a supported edge set. -/
def LiftedArcs (vertices : Set α) (arcs : Set (α × α)) : Set (SplitArc α)
  | .internal v => v ∈ vertices
  | .transfer u v => (u, v) ∈ arcs

theorem liftedArcs_clashFree_of_vertexClashFree
    {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (hvertices : VertexClashFree bar vertices)
    (hsupport : ∀ ⦃u v⦄, (u, v) ∈ arcs → u ∈ vertices ∧ v ∈ vertices) :
    SplitArcClashFree bar (LiftedArcs vertices arcs) := by
  intro a ha hmate
  cases a with
  | internal v =>
      change v ∈ vertices at ha
      change bar v ∈ vertices at hmate
      exact hvertices ha hmate
  | transfer u v =>
      change (u, v) ∈ arcs at ha
      change (bar v, bar u) ∈ arcs at hmate
      exact hvertices (hsupport ha).2 (hsupport hmate).1

theorem vertexClashFree_of_liftedArcs
    {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (harcs : SplitArcClashFree bar (LiftedArcs vertices arcs)) :
    VertexClashFree bar vertices := by
  intro v hv hbarv
  exact harcs (a := SplitArc.internal v) hv hbarv

/-- Model-equivalence theorem for the regularity constraint.  If every edge
of a trace is supported on its vertex set, vertex clash-freeness is equivalent
to arc clash-freeness after splitting.  The reverse implication uses the
internal arc attached to every visited vertex. -/
theorem vertexSplit_model_equivalence
    {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (hsupport : ∀ ⦃u v⦄, (u, v) ∈ arcs → u ∈ vertices ∧ v ∈ vertices) :
    SplitArcClashFree bar (LiftedArcs vertices arcs) ↔
      VertexClashFree bar vertices := by
  constructor
  · exact vertexClashFree_of_liftedArcs
  · intro hvertices
    exact liftedArcs_clashFree_of_vertexClashFree hvertices hsupport

/-- A supported trace on a clash-free vertex set contains no unit arc. -/
theorem supported_arc_ne_mate
    {bar : α → α} {vertices : Set α} {arcs : Set (α × α)}
    (hvertices : VertexClashFree bar vertices)
    (hsupport : ∀ ⦃u v⦄, (u, v) ∈ arcs → u ∈ vertices ∧ v ∈ vertices)
    {u v : α} (huv : (u, v) ∈ arcs) :
    v ≠ bar u := by
  intro hunit
  have hs := hsupport huv
  exact hvertices hs.1 (by simpa [hunit] using hs.2)

/-- The actual split-edge relation, with unit transfer arcs removed. -/
def SplitEdge (edge : α → α → Prop) (bar : α → α) :
    SplitNode α → SplitNode α → Prop
  | .minus u, .plus v => u = v
  | .plus u, .minus v => edge u v ∧ v ≠ bar u
  | _, _ => False

/-- Vertex splitting preserves contraposition of the edge relation. -/
theorem splitEdge_skew
    {edge : α → α → Prop} {bar : α → α}
    (hinvol : ∀ x, bar (bar x) = x)
    (hskew : ∀ u v, edge u v ↔ edge (bar v) (bar u))
    (x y : SplitNode α) :
    SplitEdge edge bar x y ↔
      SplitEdge edge bar (splitNodeBar bar y) (splitNodeBar bar x) := by
  have hbarinj : Function.Injective bar := by
    intro u v huv
    rw [← hinvol u, ← hinvol v, huv]
  cases x with
  | minus u =>
      cases y with
      | minus v => simp [SplitEdge, splitNodeBar]
      | plus v =>
          simp only [SplitEdge, splitNodeBar]
          constructor
          · intro huv
            subst v
            rfl
          · intro huv
            exact (hbarinj huv).symm
  | plus u =>
      cases y with
      | plus v => simp [SplitEdge, splitNodeBar]
      | minus v =>
          simp only [SplitEdge, splitNodeBar, hinvol]
          constructor
          · rintro ⟨huv, hunit⟩
            exact ⟨(hskew u v).1 huv, fun h => hunit h.symm⟩
          · rintro ⟨huv, hunit⟩
            exact ⟨(hskew u v).2 huv, fun h => hunit h.symm⟩

/-- Consecutive-edge predicate for a finite relational walk. -/
def Walk (edge : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | u :: v :: tail => edge u v ∧ Walk edge (v :: tail)

/-- Alternating node sequence produced by vertex splitting. -/
def liftNodes : List α → List (SplitNode α)
  | [] => []
  | v :: tail => .minus v :: .plus v :: liftNodes tail

/-- Project the minus copies from a split node sequence. -/
def projectMinus : List (SplitNode α) → List α
  | [] => []
  | .minus v :: tail => v :: projectMinus tail
  | .plus _ :: tail => projectMinus tail

@[simp] theorem projectMinus_liftNodes (xs : List α) :
    projectMinus (liftNodes xs) = xs := by
  induction xs with
  | nil => rfl
  | cons v tail ih => simp [liftNodes, projectMinus, ih]

/-- Exact walk correspondence for the alternating lift.  The right side is
the original walk after deletion of unit arcs. -/
theorem splitWalk_liftNodes_iff
    {edge : α → α → Prop} {bar : α → α} (xs : List α) :
    Walk (SplitEdge edge bar) (liftNodes xs) ↔
      Walk (fun u v => edge u v ∧ v ≠ bar u) xs := by
  induction xs with
  | nil => simp [liftNodes, Walk]
  | cons u tail ih =>
      cases tail with
      | nil => simp [liftNodes, Walk, SplitEdge]
      | cons v rest =>
          have ih' :
              Walk (SplitEdge edge bar) (SplitNode.plus v :: liftNodes rest) ↔
                Walk (fun u v => edge u v ∧ v ≠ bar u) (v :: rest) := by
            simpa [liftNodes, Walk, SplitEdge] using ih
          simp [liftNodes, Walk, SplitEdge, ih', and_assoc]

/-! ## Abstract completion-oracle interface -/

/-- A prefix is viable when it is a prefix of at least one target output. -/
def Viable (outputs : List (List α)) (pfx : List α) : Prop :=
  ∃ output, output ∈ outputs ∧ pfx <+: output

/-- Exact Boolean completion oracle, independent of its implementation. -/
structure CompletionOracle (outputs : List (List α)) where
  decide : List α → Bool
  correct : ∀ pfx, decide pfx = true ↔ Viable outputs pfx

theorem oracle_accepts_iff_viable
    {outputs : List (List α)} (oracle : CompletionOracle outputs)
    (pfx : List α) :
    oracle.decide pfx = true ↔ Viable outputs pfx :=
  oracle.correct pfx

/-- Every child entered after an exact positive completion query has an output
descendant.  This is the recursion-tree fact used in the delay proof. -/
theorem accepted_prefix_has_output_descendant
    {outputs : List (List α)} (oracle : CompletionOracle outputs)
    {pfx : List α} (haccept : oracle.decide pfx = true) :
    ∃ output, output ∈ outputs ∧ pfx <+: output :=
  (oracle.correct pfx).1 haccept

/-- A fixed output has at most one prefix at each depth, the combinatorial
source of the no-duplicate recursion branch. -/
theorem equal_prefixes_of_equal_length
    {prefix₁ prefix₂ output : List α}
    (h₁ : prefix₁ <+: output) (h₂ : prefix₂ <+: output)
    (hlen : prefix₁.length = prefix₂.length) :
    prefix₁ = prefix₂ := by
  rw [List.prefix_iff_eq_take] at h₁ h₂
  calc
    prefix₁ = output.take prefix₁.length := h₁
    _ = output.take prefix₂.length := by rw [hlen]
    _ = prefix₂ := h₂.symm

/-- Two vertices can coexist in a vertex-regular path. -/
def Compatible (bar : α → α) (x y : α) : Prop :=
  x ≠ y ∧ bar x ≠ y ∧ x ≠ bar y

/-- A vertex sequence is simple and contains no complementary pair. -/
def Regular (bar : α → α) (xs : List α) : Prop :=
  xs.Pairwise (Compatible bar)

/-- `y` remains after deleting every old prefix vertex and its mate. -/
def Survives (bar : α → α) (old : List α) (y : α) : Prop :=
  y ∉ old ∧ bar y ∉ old

/-- Every proper suffix vertex remains in the prefix-deleted instance. -/
def SuffixSurvives (bar : α → α) (old tail : List α) : Prop :=
  ∀ y ∈ tail, Survives bar old y

theorem compatible_of_survives
    {bar : α → α}
    (hinvol : ∀ x, bar (bar x) = x)
    {old : List α} {x y : α}
    (hx : x ∈ old) (hy : Survives bar old y) :
    Compatible bar x y := by
  constructor
  · intro hxy
    apply hy.1
    rw [← hxy]
    exact hx
  constructor
  · intro hxy
    apply hy.2
    rw [← hxy, hinvol]
    exact hx
  · intro hxy
    apply hy.2
    rw [← hxy]
    exact hx

/-- The prefix-deletion equivalence underlying the extension oracle.

The left side is the regularity of the joined path.  The right side says that
the fixed prefix and proposed suffix are individually regular and that the
proper suffix avoids every deleted complementary pair. -/
theorem regular_join_iff
    {bar : α → α}
    (hinvol : ∀ x, bar (bar x) = x)
    (old tail : List α) (z : α) :
    Regular bar (old ++ z :: tail) ↔
      Regular bar (old ++ [z]) ∧
      Regular bar (z :: tail) ∧
      SuffixSurvives bar old tail := by
  constructor
  · intro hjoin
    rcases List.pairwise_append.mp hjoin with ⟨hold, hsuffix, hcross⟩
    have hprefix : Regular bar (old ++ [z]) := by
      apply List.pairwise_append.mpr
      refine ⟨hold, ?_, ?_⟩
      · simp
      · intro x hx y hy
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        subst y
        exact hcross x hx z (by simp)
    refine ⟨hprefix, hsuffix, ?_⟩
    intro y hy
    constructor
    · intro hyold
      exact (hcross y hyold y (by simp [hy])).1 rfl
    · intro hbarold
      exact (hcross (bar y) hbarold y (by simp [hy])).2.2 rfl
  · rintro ⟨hprefix, hsuffix, hsurvives⟩
    rcases List.pairwise_append.mp hprefix with ⟨hold, _, htoz⟩
    apply List.pairwise_append.mpr
    refine ⟨hold, hsuffix, ?_⟩
    intro x hx y hy
    simp only [List.mem_cons] at hy
    rcases hy with hyz | hy
    · subst y
      exact htoz x hx z (by simp)
    · exact compatible_of_survives hinvol hx (hsurvives y hy)

/-- The relation induced by the vertices that survive prefix deletion. -/
def InducedAfterDeletion
    (edge : α → α → Prop) (bar : α → α) (old : List α) :
    {x // Survives bar old x} → {x // Survives bar old x} → Prop :=
  fun x y => edge x.1 y.1

/-- The graph-side composition used in the converse direction of the
prefix-extension lemma.

CSLib's `RelatesInSteps` records a relational walk together with its exact
number of edges.  A suffix in the induced relation maps to the original edge
relation; prepending the joining edge and then the prefix adds the lengths. -/
theorem reachability_join_induced
    {edge : α → α → Prop} {bar : α → α} {old : List α}
    {s v w t : α} {k ℓ : Nat}
    (hprefix : Relation.RelatesInSteps edge s v k)
    (hvw : edge v w)
    (hw : Survives bar old w) (ht : Survives bar old t)
    (hsuffix : Relation.RelatesInSteps
      (InducedAfterDeletion edge bar old) ⟨w, hw⟩ ⟨t, ht⟩ ℓ) :
    Relation.RelatesInSteps edge s t (k + (ℓ + 1)) := by
  have hsuffix' : Relation.RelatesInSteps edge w t ℓ :=
    hsuffix.map Subtype.val (by
      intro a b hab
      exact hab)
  exact hprefix.trans (hsuffix'.head v w t ℓ hvw)

/-- Package the two formal ingredients used by one accepted extension.

This theorem deliberately keeps the list witness and CSLib relational walk as
separate hypotheses: it does not claim that the enumerator, its path data
structure, or its complexity analysis has been formalized. -/
theorem regular_and_reachability_join_induced
    {edge : α → α → Prop} {bar : α → α} {old tail : List α}
    {s v w t : α} {k ℓ : Nat}
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
  constructor
  · exact (regular_join_iff hinvol old tail w).2
      ⟨hprefixRegular, hsuffixRegular, hsurvives⟩
  · exact reachability_join_induced hprefixReach hvw hw ht hsuffixReach

/-- The concrete complement operation used by the executable artifact. -/
def natMate (v : Nat) : Nat := v ^^^ 1

theorem natMate_involutive (v : Nat) : natMate (natMate v) = v := by
  simp [natMate, Nat.xor_assoc]

theorem natMate_ne_self (v : Nat) : natMate v ≠ v := by
  intro h
  have h' := congrArg (fun x => v ^^^ x) h
  simp [natMate, ← Nat.xor_assoc] at h'

/-- The executable complement satisfies the full mathematical assumptions. -/
def natComplementedType : ComplementedType Nat where
  bar := natMate
  involutive := natMate_involutive
  fixedPointFree := natMate_ne_self

#print axioms regular_join_iff
#print axioms reachability_join_induced
#print axioms regular_and_reachability_join_induced
#print axioms vertexSplit_model_equivalence
#print axioms splitArcBar_unit
#print axioms splitEdge_skew
#print axioms splitWalk_liftNodes_iff
#print axioms accepted_prefix_has_output_descendant
#print axioms equal_prefixes_of_equal_length
#print axioms natMate_involutive
#print axioms natMate_ne_self

end RegularPathDelay
