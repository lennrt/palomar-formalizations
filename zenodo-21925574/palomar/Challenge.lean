/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Formalization: Lennart Rudolph, the responsible author, with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude)
-/
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# The `K₃,₃,₁` exclusion is redundant for tetrahedral balls: the combinatorial core

Alexa's three-dimensional Tutte embedding theorem (Discrete & Computational
Geometry 73, 2025) embeds a tetrahedral mesh whose graph is 4-connected and has
neither a `K₆` nor a `K₃,₃,₁` minor, and asks whether the second exclusion is
needed. The paper proves that it is redundant for a precisely defined class of
meshes. Let `T` be a finite simplicial complex whose realization is a closed
topological 3-ball, let `G` be its 1-skeleton, and assume (BT): every
triangular face whose three vertices lie on the boundary is itself a boundary
face. If `G` has no `K₆` minor, then `G` is linklessly embeddable, hence has
no `K₃,₃,₁` minor (Theorem 1.1), and Alexa's theorem applies to `T` without
the `K₃,₃,₁` clause (Corollary 1.2).

The proof runs in four steps. (1) (BT) makes the closed stars of interior
vertices cover `G`; Gluck's theorem, coning, and rigidity gluing make `G`
generically 4-rigid, so `G` has at least `4|V| - 10` edges; Mader's bound gives
equality and Jørgensen's classification makes `G` an MP₁-cockade, a graph
generated from `K₅` and apex-planar atoms by `K₄`-sums (Corollary 3.6).
(2) For every four-clique `S` of `G`, the relative `F₂` homology
`H₂(T[S], T[S] ∩ ∂T)` has dimension at most one (Lemma 4.3), and relative ball
duality converts this into the separator bound `comp(G - S) ≤ 2`
(Theorem 4.4). (3) A `K₄`-attachment never merges components of the old part
(Lemma 5.2), so the separator bound of the final graph transports down the
cockade construction tree, and the four-clique Holst–Lovász–Schrijver criterion
(Corollary 2.5) preserves linkless embeddability at every internal node
(Proposition 5.3). (4) Linkless embeddability is minor closed and `K₃,₃,₁` is
intrinsically linked. Steps (2) and (3) are the paper's new mathematics;
step (1) is a new argument on cited theorems, and step (4) is cited.

## Compared declarations

Six declarations are compared.

* `K331Tutte.FiniteHomology.Ambient.encoded_induced_four_pair_admissible`,
  `induced_four_coordinate_chain_identification`, and
  `induced_four_clique_relative_homology_bound` are Lemma 7.1, the
  identification of the induced relative chain complex with its four-face,
  six-edge Boolean coordinate model, and Lemma 4.3. They are stated for every
  finite simplicial pair on `Fin n` and every injectively labelled four-clique
  under (BT), not for one fixed configuration. The 32,768-encoding census of
  Section 7 is a regression check of this lemma; the compared statement is the
  lemma itself.
* `K331Tutte.Cockades.attachment_reachable_transfer` and
  `K331Tutte.Cockades.safe_cockade_linkless` are Lemma 5.2 and
  Proposition 5.3 over mathlib `SimpleGraph`s. Linkless embeddability is the
  abstract predicate `nIL`, constrained by exactly the two cited inputs the
  paper uses: atoms are linklessly embeddable (Lemma 5.1) and the four-clique
  HLS criterion (Corollary 2.5).
* `K331Tutte.Bridge.structural_theorem` joins the two layers into the
  combinatorial core of Theorem 1.1. The skeleton of the complex is a
  `SimpleGraph`, every four-clique of the skeleton is a labelled four-clique
  of the pair, Lemma 4.3 supplies the homological bound for each of them, and
  the hypothesis `hduality` (Propositions 4.1 and 4.2 with universal
  coefficients) turns that bound into Theorem 4.4. With Corollary 3.6 as the
  hypothesis `hcockade`, the conclusion is the linkless embeddability of the
  skeleton. Every hypothesis names the cited theorem it stands for.

## External inputs

Generic rigidity (Gluck, Whiteley), Mader's extremal theorem, Jørgensen's
classification, the PL topology behind the deletion retraction and relative
ball duality, the Holst–Lovász–Schrijver theorem, linkless embeddability of
apex graphs, minor-closedness of linkless embeddability, and Alexa's theorem
are not formalized. Each enters the compared statements only as an explicit
hypothesis, matching the paper's own formal-scope statement in Section 7.
-/

set_option autoImplicit true
namespace K331Tutte.FiniteHomology
structure Chain2 where
  t012 : Bool
  t013 : Bool
  t023 : Bool
  t123 : Bool
  deriving DecidableEq

structure Chain1 where
  e01 : Bool
  e02 : Bool
  e03 : Bool
  e12 : Bool
  e13 : Bool
  e23 : Bool
  deriving DecidableEq

structure VertexFlags where
  v0 : Bool
  v1 : Bool
  v2 : Bool
  v3 : Bool
  deriving DecidableEq

def f2add : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

def add2 (x y : Chain2) : Chain2 :=
  ⟨f2add x.t012 y.t012, f2add x.t013 y.t013,
    f2add x.t023 y.t023, f2add x.t123 y.t123⟩

def zero2 : Chain2 := ⟨false, false, false, false⟩
def zero1 : Chain1 := ⟨false, false, false, false, false, false⟩

def d2 (z : Chain2) : Chain1 :=
  ⟨f2add z.t012 z.t013, f2add z.t012 z.t023,
    f2add z.t013 z.t023, f2add z.t012 z.t123,
    f2add z.t013 z.t123, f2add z.t023 z.t123⟩

structure FourVertexPair where
  faces : Chain2
  tetrahedron : Bool
  boundaryVertices : VertexFlags
  boundaryEdges : Chain1
  deriving DecidableEq

def allBoundaryFaceFlags (v : VertexFlags) : Chain2 :=
  ⟨v.v0 && v.v1 && v.v2, v.v0 && v.v1 && v.v3,
    v.v0 && v.v2 && v.v3, v.v1 && v.v2 && v.v3⟩

def relativeFaces (c : FourVertexPair) : Chain2 :=
  let b := allBoundaryFaceFlags c.boundaryVertices
  ⟨c.faces.t012 && !b.t012, c.faces.t013 && !b.t013,
    c.faces.t023 && !b.t023, c.faces.t123 && !b.t123⟩

def Supported2 (available z : Chain2) : Prop :=
  (z.t012 = true → available.t012 = true) ∧
  (z.t013 = true → available.t013 = true) ∧
  (z.t023 = true → available.t023 = true) ∧
  (z.t123 = true → available.t123 = true)

def SupportedOnBoundaryEdges (boundary z : Chain1) : Prop :=
  (z.e01 = true → boundary.e01 = true) ∧
  (z.e02 = true → boundary.e02 = true) ∧
  (z.e03 = true → boundary.e03 = true) ∧
  (z.e12 = true → boundary.e12 = true) ∧
  (z.e13 = true → boundary.e13 = true) ∧
  (z.e23 = true → boundary.e23 = true)

def RelativeCycle (c : FourVertexPair) (z : Chain2) : Prop :=
  Supported2 (relativeFaces c) z ∧
  SupportedOnBoundaryEdges c.boundaryEdges (d2 z)

def Admissible (c : FourVertexPair) : Prop :=
  (c.tetrahedron = true → c.faces = ⟨true, true, true, true⟩) ∧
  (c.boundaryEdges.e01 = true →
    c.boundaryVertices.v0 = true ∧ c.boundaryVertices.v1 = true) ∧
  (c.boundaryEdges.e02 = true →
    c.boundaryVertices.v0 = true ∧ c.boundaryVertices.v2 = true) ∧
  (c.boundaryEdges.e03 = true →
    c.boundaryVertices.v0 = true ∧ c.boundaryVertices.v3 = true) ∧
  (c.boundaryEdges.e12 = true →
    c.boundaryVertices.v1 = true ∧ c.boundaryVertices.v2 = true) ∧
  (c.boundaryEdges.e13 = true →
    c.boundaryVertices.v1 = true ∧ c.boundaryVertices.v3 = true) ∧
  (c.boundaryEdges.e23 = true →
    c.boundaryVertices.v2 = true ∧ c.boundaryVertices.v3 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t012 = true →
    c.faces.t012 = true → c.boundaryEdges.e01 = true ∧
      c.boundaryEdges.e02 = true ∧ c.boundaryEdges.e12 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t013 = true →
    c.faces.t013 = true → c.boundaryEdges.e01 = true ∧
      c.boundaryEdges.e03 = true ∧ c.boundaryEdges.e13 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t023 = true →
    c.faces.t023 = true → c.boundaryEdges.e02 = true ∧
      c.boundaryEdges.e03 = true ∧ c.boundaryEdges.e23 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t123 = true →
    c.faces.t123 = true → c.boundaryEdges.e12 = true ∧
      c.boundaryEdges.e13 = true ∧ c.boundaryEdges.e23 = true)

def d3Boundary (c : FourVertexPair) : Chain2 :=
  if c.tetrahedron then relativeFaces c else zero2

def Homologous (c : FourVertexPair) (x y : Chain2) : Prop :=
  x = y ∨ x = add2 y (d3Boundary c)

namespace Ambient

abbrev VertexSet (n : Nat) := Fin n → Prop
def EmptyVertexSet : VertexSet n := fun _ => False
def SingletonVertexSet (a : Fin n) : VertexSet n := fun v => v = a
def EdgeVertexSet (a b : Fin n) : VertexSet n := fun v => v = a ∨ v = b
def TriangleVertexSet (a b d : Fin n) : VertexSet n :=
  fun v => v = a ∨ v = b ∨ v = d
def FullVertexSet : VertexSet n := fun _ => True
def VertexSet.Subset (a b : VertexSet n) : Prop := ∀ ⦃v⦄, a v → b v

structure FiniteSimplicialComplex (n : Nat) where
  simplex : VertexSet n → Bool
  extensional : ∀ {a b}, (∀ v, a v ↔ b v) → simplex a = simplex b
  empty_mem : simplex EmptyVertexSet = true
  downward_closed : ∀ {a b}, simplex b = true → a.Subset b → simplex a = true

structure FiniteSimplicialPair (n : Nat) where
  ambient : FiniteSimplicialComplex n
  boundary : FiniteSimplicialComplex n
  boundary_subcomplex : ∀ {s}, boundary.simplex s = true → ambient.simplex s = true

def FiniteSimplicialPair.IsBoundaryVertex
    (P : FiniteSimplicialPair n) (v : Fin n) : Prop :=
  P.boundary.simplex (SingletonVertexSet v) = true

def BoundaryTriangleCondition (P : FiniteSimplicialPair n) : Prop :=
  ∀ (a b d : Fin n), a ≠ b → a ≠ d → b ≠ d →
    P.ambient.simplex (TriangleVertexSet a b d) = true →
    P.IsBoundaryVertex a → P.IsBoundaryVertex b → P.IsBoundaryVertex d →
    P.boundary.simplex (TriangleVertexSet a b d) = true

structure LabelledFourClique (P : FiniteSimplicialPair n) where
  label : Fin 4 → Fin n
  injective : ∀ {i j}, label i = label j → i = j
  clique : ∀ i j, i ≠ j →
    P.ambient.simplex (EdgeVertexSet (label i) (label j)) = true

variable {n : Nat} {P : FiniteSimplicialPair n}

def imageVertexSet (L : LabelledFourClique P) (s : VertexSet 4) : VertexSet n :=
  fun v => ∃ i, s i ∧ v = L.label i

def inducedComplex (C : FiniteSimplicialComplex n)
    (L : LabelledFourClique P) : FiniteSimplicialComplex 4 where
  simplex s := C.simplex (imageVertexSet L s)
  extensional := by
    intro a b h; apply C.extensional; intro v
    constructor <;> rintro ⟨i, hi, rfl⟩
    · exact ⟨i, (h i).1 hi, rfl⟩
    · exact ⟨i, (h i).2 hi, rfl⟩
  empty_mem := by
    rw [C.extensional (b := EmptyVertexSet) (by simp [imageVertexSet, EmptyVertexSet])]
    exact C.empty_mem
  downward_closed := by
    intro a b hb h; exact C.downward_closed hb (by
      rintro v ⟨i, hi, rfl⟩; exact ⟨i, h hi, rfl⟩)

def inducedPair (P : FiniteSimplicialPair n)
    (L : LabelledFourClique P) : FiniteSimplicialPair 4 where
  ambient := inducedComplex P.ambient L
  boundary := inducedComplex P.boundary L
  boundary_subcomplex := fun h => P.boundary_subcomplex h

def v0 : Fin 4 := ⟨0, by decide⟩
def v1 : Fin 4 := ⟨1, by decide⟩
def v2 : Fin 4 := ⟨2, by decide⟩
def v3 : Fin 4 := ⟨3, by decide⟩
def f012 : VertexSet 4 := TriangleVertexSet v0 v1 v2
def f013 : VertexSet 4 := TriangleVertexSet v0 v1 v3
def f023 : VertexSet 4 := TriangleVertexSet v0 v2 v3
def f123 : VertexSet 4 := TriangleVertexSet v1 v2 v3
def e01 : VertexSet 4 := EdgeVertexSet v0 v1
def e02 : VertexSet 4 := EdgeVertexSet v0 v2
def e03 : VertexSet 4 := EdgeVertexSet v0 v3
def e12 : VertexSet 4 := EdgeVertexSet v1 v2
def e13 : VertexSet 4 := EdgeVertexSet v1 v3
def e23 : VertexSet 4 := EdgeVertexSet v2 v3

def encodePair (Q : FiniteSimplicialPair 4) : FourVertexPair where
  faces := ⟨Q.ambient.simplex f012, Q.ambient.simplex f013,
    Q.ambient.simplex f023, Q.ambient.simplex f123⟩
  tetrahedron := Q.ambient.simplex FullVertexSet
  boundaryVertices := ⟨Q.boundary.simplex (SingletonVertexSet v0),
    Q.boundary.simplex (SingletonVertexSet v1),
    Q.boundary.simplex (SingletonVertexSet v2),
    Q.boundary.simplex (SingletonVertexSet v3)⟩
  boundaryEdges := ⟨Q.boundary.simplex e01, Q.boundary.simplex e02,
    Q.boundary.simplex e03, Q.boundary.simplex e12,
    Q.boundary.simplex e13, Q.boundary.simplex e23⟩

def actualRelativeFaces (Q : FiniteSimplicialPair 4) : Chain2 :=
  ⟨Q.ambient.simplex f012 && (!Q.boundary.simplex f012),
    Q.ambient.simplex f013 && (!Q.boundary.simplex f013),
    Q.ambient.simplex f023 && (!Q.boundary.simplex f023),
    Q.ambient.simplex f123 && (!Q.boundary.simplex f123)⟩

def quotientBoundaryEdges (Q : FiniteSimplicialPair 4) (x : Chain1) : Chain1 :=
  let b := (encodePair Q).boundaryEdges
  ⟨x.e01 && (!b.e01), x.e02 && (!b.e02), x.e03 && (!b.e03),
    x.e12 && (!b.e12), x.e13 && (!b.e13), x.e23 && (!b.e23)⟩

def actualRelativeD2 (Q : FiniteSimplicialPair 4) (z : Chain2) : Chain1 :=
  quotientBoundaryEdges Q (d2 z)
def actualD3Boundary (Q : FiniteSimplicialPair 4) : Chain2 :=
  if Q.ambient.simplex FullVertexSet then actualRelativeFaces Q else zero2
def ActualRelativeCycle (Q : FiniteSimplicialPair 4) (z : Chain2) : Prop :=
  Supported2 (actualRelativeFaces Q) z ∧ actualRelativeD2 Q z = zero1
def ActualHomologous (Q : FiniteSimplicialPair 4) (x y : Chain2) : Prop :=
  x = y ∨ x = add2 y (actualD3Boundary Q)

abbrev ActualCycleSpace (Q : FiniteSimplicialPair 4) :=
  {z : Chain2 // ActualRelativeCycle Q z}

theorem actual_homologous_refl (Q : FiniteSimplicialPair 4) (x : Chain2) :
    ActualHomologous Q x x := Or.inl rfl

/-- Adding the same F₂ chain twice is the identity, one coordinate at a time. -/
theorem f2add_f2add_cancel (a b : Bool) : f2add (f2add a b) b = a := by
  cases a <;> cases b <;> rfl

/-- Adding the same F₂ chain twice is the identity. -/
theorem add2_add2_cancel (y d : Chain2) : add2 (add2 y d) d = y := by
  cases y
  cases d
  simp only [add2, f2add_f2add_cancel]

theorem actual_homologous_symm {Q : FiniteSimplicialPair 4} {x y : Chain2}
    (h : ActualHomologous Q x y) : ActualHomologous Q y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    calc
      y = add2 (add2 y (actualD3Boundary Q)) (actualD3Boundary Q) :=
        (add2_add2_cancel y (actualD3Boundary Q)).symm
      _ = add2 x (actualD3Boundary Q) := by rw [← h]

theorem actual_homologous_trans
    {Q : FiniteSimplicialPair 4} {x y z : Chain2}
    (hxy : ActualHomologous Q x y) (hyz : ActualHomologous Q y z) :
    ActualHomologous Q x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  · left
    calc
      x = add2 y (actualD3Boundary Q) := hxy
      _ = add2 (add2 z (actualD3Boundary Q)) (actualD3Boundary Q) := by rw [hyz]
      _ = z := add2_add2_cancel z (actualD3Boundary Q)

def actualHomologySetoid (Q : FiniteSimplicialPair 4) : Setoid (ActualCycleSpace Q) where
  r x y := ActualHomologous Q x.1 y.1
  iseqv := ⟨
    fun x => actual_homologous_refl Q x.1,
    fun h => actual_homologous_symm h,
    fun h₁ h₂ => actual_homologous_trans h₁ h₂⟩

abbrev InducedRelativeH2 (Q : FiniteSimplicialPair 4) :=
  Quotient (actualHomologySetoid Q)
def ActualHomologyDimensionAtMostOne (Q : FiniteSimplicialPair 4) : Prop :=
  ∀ q₀ q₁ q₂ : InducedRelativeH2 Q, q₀ = q₁ ∨ q₀ = q₂ ∨ q₁ = q₂

/-- Lemma 7.1 for the actual induced pair. -/
theorem encoded_induced_four_pair_admissible
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    Admissible (encodePair (inducedPair P L)) := by
  sorry

/-- Exact identification of the actual and Boolean coordinate complexes. -/
theorem induced_four_coordinate_chain_identification
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    let Q := inducedPair P L
    let c := encodePair Q
    actualRelativeFaces Q = relativeFaces c ∧
      (∀ z, ActualRelativeCycle Q z ↔ RelativeCycle c z) ∧
      actualD3Boundary Q = d3Boundary c ∧
      (∀ x y, ActualHomologous Q x y ↔ Homologous c x y) := by
  sorry

/-- Lemma 4.3 for the actual quotient of the induced relative chain complex. -/
theorem induced_four_clique_relative_homology_bound
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    ActualHomologyDimensionAtMostOne (inducedPair P L) := by
  sorry

end Ambient
end K331Tutte.FiniteHomology

namespace K331Tutte.Cockades

open SimpleGraph

variable {V : Type*}

/-- Delete a vertex set: keep only edges with both endpoints outside `S`. -/
def deleteVerts (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- All edges of `G` lie inside the vertex set `s`. -/
def EdgesWithin (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ s ∧ v ∈ s

/-- `R` is a four-clique of `G`. -/
def IsFourClique (G : SimpleGraph V) (R : Finset V) : Prop :=
  R.card = 4 ∧ G.IsClique (↑R : Set V)

/-- After deleting `S`, the vertices of `s` fall into at most two connected
components: of any three, some two are joined. -/
def TwoComponentsAfterDeletion (G : SimpleGraph V) (s : Set V) (S : Set V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ∀ w ∈ s, u ∉ S → v ∉ S → w ∉ S →
    ((deleteVerts G S).Reachable u v ∨ (deleteVerts G S).Reachable u w ∨
      (deleteVerts G S).Reachable v w)

/-- A K₄-attachment: the new part `A` (supported on `t`) meets the old part `X`
(supported on `s`) exactly in a four-clique `R` of both. This is the
disjoint-copies-before-identification clique-sum step of Definition 2.3. -/
structure K4Attachment (X A : SimpleGraph V) (s t : Set V) (R : Finset V) : Prop where
  edgesX : EdgesWithin X s
  edgesA : EdgesWithin A t
  inter : s ∩ t = (↑R : Set V)
  cliqueX : IsFourClique X R
  cliqueA : IsFourClique A R

/-- MP₁-cockades over an abstract atom family: recursively generated from atoms
by K₄-attachments (Definition 2.3 / Jørgensen). -/
inductive IsCockade (Atom : SimpleGraph V → Set V → Prop) :
    SimpleGraph V → Set V → Prop
  | atom {A : SimpleGraph V} {s : Set V} : Atom A s → IsCockade Atom A s
  | glue {X A : SimpleGraph V} {s t : Set V} {R : Finset V} :
      IsCockade Atom X s → Atom A t → K4Attachment X A s t R →
      IsCockade Atom (X ⊔ A) (s ∪ t)

/-- Lemma 5.2 (attachments do not merge old components): a K₄-attachment
cannot create new connections between vertices of the old support, even after
an arbitrary vertex set has been deleted. -/
theorem attachment_reachable_transfer
    (X A : SimpleGraph V) (s t : Set V) (R : Finset V)
    (h : K4Attachment X A s t R) (S : Set V) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hus : u ∉ S) (hvs : v ∉ S)
    (hreach : (deleteVerts (X ⊔ A) S).Reachable u v) :
    (deleteVerts X S).Reachable u v := by sorry

/-- Proposition 5.3 (the safe clique-sum induction): every MP₁-cockade whose
four-cliques all leave at most two components on the support is `nIL`, given
that the atoms are `nIL` and the Holst-Lovasz-Schrijver four-clique rule
(`hHLS`, paper Corollary 2.5) is available; `hsep` is the separator bound
(paper Theorem 4.4) for the final graph. -/
theorem safe_cockade_linkless
    (Atom : SimpleGraph V → Set V → Prop) (nIL : SimpleGraph V → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph V) (s : Set V), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph V) (s : Set V), Atom A s →
      ∃ T : Finset V, (↑T : Set V) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph V) (s t : Set V) (R : Finset V),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set V) → nIL (X ⊔ A))
    {G : SimpleGraph V} {s : Set V} (hG : IsCockade Atom G s)
    (hsep : ∀ R : Finset V, IsFourClique G R → (∃ x ∈ s, x ∉ (↑R : Set V)) →
      TwoComponentsAfterDeletion G s (↑R : Set V)) :
    nIL G := by sorry

end K331Tutte.Cockades

namespace K331Tutte.Bridge

open K331Tutte.FiniteHomology K331Tutte.FiniteHomology.Ambient K331Tutte.Cockades

variable {n : Nat}

/-- The 1-skeleton of a finite simplicial complex: two distinct vertices are
adjacent exactly when the edge between them is a simplex. -/
def skeleton (C : FiniteSimplicialComplex n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ C.simplex (EdgeVertexSet u v) = true
  symm := ⟨fun u v h => ⟨h.1.symm, by
    rw [C.extensional (a := EdgeVertexSet v u) (b := EdgeVertexSet u v)
      (fun w => show (w = v ∨ w = u) ↔ (w = u ∨ w = v) from or_comm)]
    exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

/-- Theorem 1.1 (structural theorem), combinatorial core. `P` is the finite
simplicial pair `(T, ∂T)` on `n` vertices and `hBT` is (BT). The hypotheses
are the paper's cited inputs, one each: `hatom_nIL` is Lemma 5.1 (atoms are
linklessly embeddable), `hatom_big` records that atoms have at least five
vertices, `hHLS` is Corollary 2.5 (the four-clique Holst–Lovász–Schrijver
criterion), `hcockade` is Corollary 3.6 (rigidity, Mader, and Jørgensen make
the skeleton an MP₁-cockade), and `hduality` is the relative ball duality of
Propositions 4.1 and 4.2 with universal coefficients, which turns the relative
homology bound into the component bound. The proved content is Lemma 4.3 for
every four-clique of the skeleton, Lemma 5.2, and Proposition 5.3, composed
into the conclusion that the skeleton is linklessly embeddable. -/
theorem structural_theorem (P : FiniteSimplicialPair n)
    (hBT : BoundaryTriangleCondition P)
    (Atom : SimpleGraph (Fin n) → Set (Fin n) → Prop) (nIL : SimpleGraph (Fin n) → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph (Fin n)) (s : Set (Fin n)), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph (Fin n)) (s : Set (Fin n)), Atom A s →
      ∃ T : Finset (Fin n), (↑T : Set (Fin n)) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph (Fin n)) (s t : Set (Fin n)) (R : Finset (Fin n)),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set (Fin n)) → nIL (X ⊔ A))
    (hcockade : IsCockade Atom (skeleton P.ambient) Set.univ)
    (hduality : ∀ L : LabelledFourClique P, (∃ x : Fin n, x ∉ Set.range L.label) →
      ActualHomologyDimensionAtMostOne (inducedPair P L) →
      TwoComponentsAfterDeletion (skeleton P.ambient) Set.univ (Set.range L.label)) :
    nIL (skeleton P.ambient) := by sorry

end K331Tutte.Bridge
