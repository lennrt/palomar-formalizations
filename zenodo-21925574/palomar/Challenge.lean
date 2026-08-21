/- Simpler Graph Conditions for Embedding Tetrahedral Meshes.
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
https://doi.org/10.5281/zenodo.21925574 -/
import Init
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

theorem actual_homologous_symm {Q : FiniteSimplicialPair 4} {x y : Chain2}
    (h : ActualHomologous Q x y) : ActualHomologous Q y x := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · right
    calc
      y = add2 (add2 y (actualD3Boundary Q)) (actualD3Boundary Q) := by
        rcases y with ⟨a, b, d, e⟩
        rcases actualD3Boundary Q with ⟨f, g, k, i⟩
        cases a <;> cases b <;> cases d <;> cases e <;>
          cases f <;> cases g <;> cases k <;> cases i <;> rfl
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
      _ = z := by
        rcases z with ⟨a, b, d, e⟩
        rcases actualD3Boundary Q with ⟨f, g, k, i⟩
        cases a <;> cases b <;> cases d <;> cases e <;>
          cases f <;> cases g <;> cases k <;> cases i <;> rfl

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
