/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Preprint published: 2026-08-14. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Init

set_option maxHeartbeats 4000000

namespace K331Tutte.FiniteHomology

/-!
# A transparent F₂ relative-chain model

These common definitions model the pair `(K,K∂)` induced by a four-clique:
four possible triangular faces, the possible tetrahedron, and the boundary
vertices and edges. They are shared verbatim by the challenge and solution.
-/

/-- A relative 2-chain: coefficients of faces 012, 013, 023, and 123. -/
structure Chain2 where
  t012 : Bool
  t013 : Bool
  t023 : Bool
  t123 : Bool
  deriving Repr, DecidableEq

/-- A relative 1-chain: coefficients of edges 01, 02, 03, 12, 13, and 23. -/
structure Chain1 where
  e01 : Bool
  e02 : Bool
  e03 : Bool
  e12 : Bool
  e13 : Bool
  e23 : Bool
  deriving Repr, DecidableEq

/-- Flags for the four vertices. -/
structure VertexFlags where
  v0 : Bool
  v1 : Bool
  v2 : Bool
  v3 : Bool
  deriving Repr, DecidableEq

/-- Addition in F₂. -/
def f2add : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

/-- Componentwise addition of 2-chains. -/
def add2 (x y : Chain2) : Chain2 :=
  ⟨f2add x.t012 y.t012, f2add x.t013 y.t013,
    f2add x.t023 y.t023, f2add x.t123 y.t123⟩

/-- The zero 2-chain. -/
def zero2 : Chain2 := ⟨false, false, false, false⟩

/-- Componentwise addition of 1-chains. -/
def add1 (x y : Chain1) : Chain1 :=
  ⟨f2add x.e01 y.e01, f2add x.e02 y.e02, f2add x.e03 y.e03,
    f2add x.e12 y.e12, f2add x.e13 y.e13, f2add x.e23 y.e23⟩

/-- The zero 1-chain. -/
def zero1 : Chain1 := ⟨false, false, false, false, false, false⟩

/-- The tetrahedral `d₂`: each edge is incident with exactly two faces. -/
def d2 (z : Chain2) : Chain1 :=
  ⟨f2add z.t012 z.t013,
    f2add z.t012 z.t023,
    f2add z.t013 z.t023,
    f2add z.t012 z.t123,
    f2add z.t013 z.t123,
    f2add z.t023 z.t123⟩

/-- Concrete local data for `(K,K∂)` on four labelled vertices. -/
structure FourVertexPair where
  faces : Chain2
  tetrahedron : Bool
  boundaryVertices : VertexFlags
  boundaryEdges : Chain1
  deriving Repr, DecidableEq

/-- Faces all of whose vertices are boundary vertices. -/
def allBoundaryFaceFlags (v : VertexFlags) : Chain2 :=
  ⟨v.v0 && v.v1 && v.v2,
    v.v0 && v.v1 && v.v3,
    v.v0 && v.v2 && v.v3,
    v.v1 && v.v2 && v.v3⟩

/-- Faces surviving in the relative group `C₂(K,K∂;F₂)`. -/
def relativeFaces (c : FourVertexPair) : Chain2 :=
  let b := allBoundaryFaceFlags c.boundaryVertices
  ⟨c.faces.t012 && !b.t012,
    c.faces.t013 && !b.t013,
    c.faces.t023 && !b.t023,
    c.faces.t123 && !b.t123⟩

/-- The sum of every face not forced into the boundary by (BT). -/
def nonBoundaryFaceSum (c : FourVertexPair) : Chain2 :=
  let b := allBoundaryFaceFlags c.boundaryVertices
  ⟨!b.t012, !b.t013, !b.t023, !b.t123⟩

/-- A coefficient can occur only on a present relative face. -/
def Supported2 (available z : Chain2) : Prop :=
  (z.t012 = true → available.t012 = true) ∧
  (z.t013 = true → available.t013 = true) ∧
  (z.t023 = true → available.t023 = true) ∧
  (z.t123 = true → available.t123 = true)

/-- A 1-chain is zero after quotienting by the boundary subcomplex. -/
def SupportedOnBoundaryEdges (boundary z : Chain1) : Prop :=
  (z.e01 = true → boundary.e01 = true) ∧
  (z.e02 = true → boundary.e02 = true) ∧
  (z.e03 = true → boundary.e03 = true) ∧
  (z.e12 = true → boundary.e12 = true) ∧
  (z.e13 = true → boundary.e13 = true) ∧
  (z.e23 = true → boundary.e23 = true)

/-- Relative 2-cycles over F₂. -/
def RelativeCycle (c : FourVertexPair) (z : Chain2) : Prop :=
  Supported2 (relativeFaces c) z ∧
  SupportedOnBoundaryEdges c.boundaryEdges (d2 z)

/-- Simplicial closure and the boundary-triangle condition used in Lemma 4.3. -/
def Admissible (c : FourVertexPair) : Prop :=
  (c.tetrahedron = true →
    c.faces = ⟨true, true, true, true⟩) ∧
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
    c.faces.t012 = true →
      c.boundaryEdges.e01 = true ∧ c.boundaryEdges.e02 = true ∧
        c.boundaryEdges.e12 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t013 = true →
    c.faces.t013 = true →
      c.boundaryEdges.e01 = true ∧ c.boundaryEdges.e03 = true ∧
        c.boundaryEdges.e13 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t023 = true →
    c.faces.t023 = true →
      c.boundaryEdges.e02 = true ∧ c.boundaryEdges.e03 = true ∧
        c.boundaryEdges.e23 = true) ∧
  ((allBoundaryFaceFlags c.boundaryVertices).t123 = true →
    c.faces.t123 = true →
      c.boundaryEdges.e12 = true ∧ c.boundaryEdges.e13 = true ∧
        c.boundaryEdges.e23 = true)

/-- Image generator of relative `d₃`; there is at most one tetrahedron. -/
def d3Boundary (c : FourVertexPair) : Chain2 :=
  if c.tetrahedron then relativeFaces c else zero2

/-- Two relative cycles represent the same `H₂` class iff they differ by `im d₃`. -/
def Homologous (c : FourVertexPair) (x y : Chain2) : Prop :=
  x = y ∨ x = add2 y (d3Boundary c)

@[simp] theorem f2add_false (a : Bool) : f2add a false = a := by
  cases a <;> rfl

@[simp] theorem f2add_self (a : Bool) : f2add a a = false := by
  cases a <;> rfl

theorem f2add_comm (a b : Bool) : f2add a b = f2add b a := by
  cases a <;> cases b <;> rfl

theorem f2add_assoc (a b d : Bool) :
    f2add (f2add a b) d = f2add a (f2add b d) := by
  cases a <;> cases b <;> cases d <;> rfl

private theorem f2add_left_cancel {a b d : Bool}
    (h : f2add a b = f2add a d) : b = d := by
  cases a <;> cases b <;> cases d <;> simp_all [f2add]

private theorem f2add_medial (a b d e : Bool) :
    f2add (f2add a b) (f2add d e) =
      f2add (f2add a d) (f2add b e) := by
  cases a <;> cases b <;> cases d <;> cases e <;> rfl

@[simp] theorem add2_zero (x : Chain2) : add2 x zero2 = x := by
  rcases x with ⟨a, b, d, e⟩
  simp [add2, zero2]

@[simp] theorem add2_self (x : Chain2) : add2 x x = zero2 := by
  rcases x with ⟨a, b, d, e⟩
  simp [add2, zero2]

theorem add2_comm (x y : Chain2) : add2 x y = add2 y x := by
  rcases x with ⟨a, b, d, e⟩
  rcases y with ⟨f, g, h, i⟩
  simp [add2, f2add_comm]

theorem add2_assoc (x y z : Chain2) :
    add2 (add2 x y) z = add2 x (add2 y z) := by
  rcases x with ⟨a, b, d, e⟩
  rcases y with ⟨f, g, h, i⟩
  rcases z with ⟨j, k, l, m⟩
  simp [add2, f2add_assoc]

theorem add2_left_cancel {x y z : Chain2} (h : add2 x y = add2 x z) : y = z := by
  have h₀ := f2add_left_cancel (congrArg Chain2.t012 h)
  have h₁ := f2add_left_cancel (congrArg Chain2.t013 h)
  have h₂ := f2add_left_cancel (congrArg Chain2.t023 h)
  have h₃ := f2add_left_cancel (congrArg Chain2.t123 h)
  cases y
  cases z
  simp only [Chain2.mk.injEq]
  exact ⟨h₀, h₁, h₂, h₃⟩

theorem d2_add (x y : Chain2) : d2 (add2 x y) = add1 (d2 x) (d2 y) := by
  rcases x with ⟨a, b, d, e⟩
  rcases y with ⟨f, g, h, i⟩
  simp [d2, add2, add1, f2add_medial]

theorem homologous_refl (c : FourVertexPair) (x : Chain2) : Homologous c x x :=
  Or.inl rfl

theorem homologous_symm {c : FourVertexPair} {x y : Chain2}
    (h : Homologous c x y) : Homologous c y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    calc
      y = add2 (add2 y (d3Boundary c)) (d3Boundary c) := by
        rw [add2_assoc, add2_self, add2_zero]
      _ = add2 x (d3Boundary c) := by rw [← h]

theorem homologous_trans {c : FourVertexPair} {x y z : Chain2}
    (hxy : Homologous c x y) (hyz : Homologous c y z) : Homologous c x z := by
  rcases hxy with rfl | hxy
  · exact hyz
  rcases hyz with rfl | hyz
  · exact Or.inr hxy
  · left
    calc
      x = add2 y (d3Boundary c) := hxy
      _ = add2 (add2 z (d3Boundary c)) (d3Boundary c) := by rw [hyz]
      _ = z := by rw [add2_assoc, add2_self, add2_zero]

/-- The relative cycle space as an explicit subtype. -/
abbrev CycleSpace (c : FourVertexPair) := {z : Chain2 // RelativeCycle c z}

/-- Boundary equivalence on relative cycles. -/
def homologySetoid (c : FourVertexPair) : Setoid (CycleSpace c) where
  r x y := Homologous c x.1 y.1
  iseqv := ⟨
    fun x => homologous_refl c x.1,
    fun h => homologous_symm h,
    fun h₁ h₂ => homologous_trans h₁ h₂⟩

/-- `H₂(K,K∂;F₂)` as relative cycles modulo the one-dimensional `d₃` image. -/
abbrev RelativeH2 (c : FourVertexPair) := Quotient (homologySetoid c)

/-- A quotient-cardinality formulation of `dim_F₂ H₂ ≤ 1`. -/
def HomologyDimensionAtMostOne (c : FourVertexPair) : Prop :=
  ∀ q₀ q₁ q₂ : RelativeH2 c, q₀ = q₁ ∨ q₀ = q₂ ∨ q₁ = q₂

/-- A transparent cardinality bound on the relative cycle space. -/
def CycleCountAtMost (c : FourVertexPair) (n : Nat) : Prop :=
  ∀ chains : List Chain2,
    chains.Nodup →
    (∀ z, z ∈ chains → RelativeCycle c z) →
    chains.length ≤ n

/-- Remark 7.2's cycle-count threshold. -/
def CycleCountCriterion (c : FourVertexPair) : Prop :=
  (d3Boundary c = zero2 ∧ CycleCountAtMost c 2) ∨
  (d3Boundary c ≠ zero2 ∧ CycleCountAtMost c 4)

end K331Tutte.FiniteHomology
