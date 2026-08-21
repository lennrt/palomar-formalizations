/-
Authors: Lennart Rudolph, Sol, Fable
-/

import K331Tutte.FiniteHomologyProofs

set_option autoImplicit true

/-!
Paper-faithful ambient bridge for Lemmas 7.1 and 4.3.

An `n`-vertex simplex is represented extensionally by a predicate on `Fin n`.
Thus the ambient object below is an actual finite abstract simplicial complex,
not a list of preselected local outputs.  The labelled four-clique induces the
pair `(K,K∂)` by pullback along its injective vertex labelling.
-/

namespace K331Tutte.FiniteHomology.Ambient

open K331Tutte.FiniteHomology

abbrev VertexSet (n : Nat) := Fin n → Prop

def EmptyVertexSet : VertexSet n := fun _ => False

def SingletonVertexSet (a : Fin n) : VertexSet n := fun v => v = a

def EdgeVertexSet (a b : Fin n) : VertexSet n := fun v => v = a ∨ v = b

def TriangleVertexSet (a b d : Fin n) : VertexSet n :=
  fun v => v = a ∨ v = b ∨ v = d

def FullVertexSet : VertexSet n := fun _ => True

def VertexSet.Subset (a b : VertexSet n) : Prop := ∀ ⦃v⦄, a v → b v

/-- A finite abstract simplicial complex on the vertex type `Fin n`. -/
structure FiniteSimplicialComplex (n : Nat) where
  simplex : VertexSet n → Bool
  extensional : ∀ {a b}, (∀ v, a v ↔ b v) → simplex a = simplex b
  empty_mem : simplex EmptyVertexSet = true
  downward_closed : ∀ {a b}, simplex b = true → a.Subset b → simplex a = true

/-- An ambient complex together with an actual boundary subcomplex. -/
structure FiniteSimplicialPair (n : Nat) where
  ambient : FiniteSimplicialComplex n
  boundary : FiniteSimplicialComplex n
  boundary_subcomplex : ∀ {s}, boundary.simplex s = true → ambient.simplex s = true

def FiniteSimplicialPair.IsBoundaryVertex
    (P : FiniteSimplicialPair n) (v : Fin n) : Prop :=
  P.boundary.simplex (SingletonVertexSet v) = true

/-- The manuscript's (BT), stated for actual triangular simplices. -/
def BoundaryTriangleCondition (P : FiniteSimplicialPair n) : Prop :=
  ∀ (a b d : Fin n), a ≠ b → a ≠ d → b ≠ d →
    P.ambient.simplex (TriangleVertexSet a b d) = true →
    P.IsBoundaryVertex a → P.IsBoundaryVertex b → P.IsBoundaryVertex d →
    P.boundary.simplex (TriangleVertexSet a b d) = true

/-- An injectively labelled four-clique in the ambient one-skeleton. -/
structure LabelledFourClique (P : FiniteSimplicialPair n) where
  label : Fin 4 → Fin n
  injective : ∀ {i j}, label i = label j → i = j
  clique : ∀ i j, i ≠ j →
    P.ambient.simplex (EdgeVertexSet (label i) (label j)) = true

variable {n : Nat} {P : FiniteSimplicialPair n}

/-- Image of a simplex under the labelled inclusion `Fin 4 ↪ Fin n`. -/
def imageVertexSet (L : LabelledFourClique P) (s : VertexSet 4) : VertexSet n :=
  fun v => ∃ i, s i ∧ v = L.label i

/-- Restriction along the labelled inclusion; this is the induced complex. -/
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

/-- The actual induced pair `K = T[S]`, `K∂ = K ∩ ∂T`. -/
def inducedPair (P : FiniteSimplicialPair n)
    (L : LabelledFourClique P) : FiniteSimplicialPair 4 where
  ambient := inducedComplex P.ambient L
  boundary := inducedComplex P.boundary L
  boundary_subcomplex := fun h => P.boundary_subcomplex h

private theorem image_singleton (L : LabelledFourClique P) (i : Fin 4) :
    (inducedPair P L).boundary.simplex (SingletonVertexSet i) =
      P.boundary.simplex (SingletonVertexSet (L.label i)) := by
  apply P.boundary.extensional
  intro v
  simp [imageVertexSet, SingletonVertexSet]

private theorem image_triangle (C : FiniteSimplicialComplex n)
    (L : LabelledFourClique P) (i j k : Fin 4) :
    (inducedComplex C L).simplex (TriangleVertexSet i j k) =
      C.simplex (TriangleVertexSet (L.label i) (L.label j) (L.label k)) := by
  apply C.extensional
  intro v
  simp [imageVertexSet, TriangleVertexSet]

private theorem label_ne (L : LabelledFourClique P) {i j : Fin 4}
    (h : i ≠ j) : L.label i ≠ L.label j := by
  intro hij
  exact h (L.injective hij)

private theorem induced_bt (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    BoundaryTriangleCondition (inducedPair P L) := by
  intro i j k hij hik hjk hface hi hj hk
  change (inducedComplex P.ambient L).simplex
      (TriangleVertexSet i j k) = true at hface
  rw [image_triangle P.ambient L i j k] at hface
  change (inducedPair P L).boundary.simplex (SingletonVertexSet i) = true at hi
  change (inducedPair P L).boundary.simplex (SingletonVertexSet j) = true at hj
  change (inducedPair P L).boundary.simplex (SingletonVertexSet k) = true at hk
  rw [image_singleton L i] at hi
  rw [image_singleton L j] at hj
  rw [image_singleton L k] at hk
  change (inducedComplex P.boundary L).simplex
      (TriangleVertexSet i j k) = true
  rw [image_triangle P.boundary L i j k]
  apply hBT (L.label i) (L.label j) (L.label k)
      (label_ne L hij) (label_ne L hik) (label_ne L hjk)
  · exact hface
  · exact hi
  · exact hj
  · exact hk

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

/-- The paper's Boolean record extracted from the actual induced pair. -/
def encodePair (Q : FiniteSimplicialPair 4) : FourVertexPair where
  faces :=
    ⟨Q.ambient.simplex f012, Q.ambient.simplex f013,
      Q.ambient.simplex f023, Q.ambient.simplex f123⟩
  tetrahedron := Q.ambient.simplex FullVertexSet
  boundaryVertices :=
    ⟨Q.boundary.simplex (SingletonVertexSet v0),
      Q.boundary.simplex (SingletonVertexSet v1),
      Q.boundary.simplex (SingletonVertexSet v2),
      Q.boundary.simplex (SingletonVertexSet v3)⟩
  boundaryEdges :=
    ⟨Q.boundary.simplex e01, Q.boundary.simplex e02,
      Q.boundary.simplex e03, Q.boundary.simplex e12,
      Q.boundary.simplex e13, Q.boundary.simplex e23⟩

private theorem face_of_tetra (Q : FiniteSimplicialPair 4)
    {f : VertexSet 4} (hf : f.Subset FullVertexSet)
    (ht : Q.ambient.simplex FullVertexSet = true) :
    Q.ambient.simplex f = true :=
  Q.ambient.downward_closed ht hf

private theorem boundary_vertex_of_edge (Q : FiniteSimplicialPair 4)
    {a b : Fin 4} (he : Q.boundary.simplex (EdgeVertexSet a b) = true) :
    Q.boundary.simplex (SingletonVertexSet a) = true ∧
      Q.boundary.simplex (SingletonVertexSet b) = true := by
  constructor
  · exact Q.boundary.downward_closed he (by
      intro v hv
      exact Or.inl hv)
  · exact Q.boundary.downward_closed he (by
      intro v hv
      exact Or.inr hv)

private theorem boundary_edges_of_face (Q : FiniteSimplicialPair 4)
    {a b d : Fin 4}
    (hf : Q.boundary.simplex (TriangleVertexSet a b d) = true) :
    Q.boundary.simplex (EdgeVertexSet a b) = true ∧
      Q.boundary.simplex (EdgeVertexSet a d) = true ∧
      Q.boundary.simplex (EdgeVertexSet b d) = true := by
  constructor
  · exact Q.boundary.downward_closed hf (by
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inl hv))
  constructor
  · exact Q.boundary.downward_closed hf (by
      intro v hv
      rcases hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inr hv))
  · exact Q.boundary.downward_closed hf (by
      intro v hv
      rcases hv with hv | hv
      · exact Or.inr (Or.inl hv)
      · exact Or.inr (Or.inr hv))

private theorem encodePair_admissible (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) : Admissible (encodePair Q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ht
    simp only [encodePair, Chain2.mk.injEq]
    exact ⟨face_of_tetra Q (by intro _ _; trivial) ht,
      face_of_tetra Q (by intro _ _; trivial) ht,
      face_of_tetra Q (by intro _ _; trivial) ht,
      face_of_tetra Q (by intro _ _; trivial) ht⟩
  · exact boundary_vertex_of_edge Q
  · exact boundary_vertex_of_edge Q
  · exact boundary_vertex_of_edge Q
  · exact boundary_vertex_of_edge Q
  · exact boundary_vertex_of_edge Q
  · exact boundary_vertex_of_edge Q
  · intro hv hf
    have hv' :
        (Q.boundary.simplex (SingletonVertexSet v0) = true ∧
        Q.boundary.simplex (SingletonVertexSet v1) = true) ∧
        Q.boundary.simplex (SingletonVertexSet v2) = true := by
      simpa [encodePair, allBoundaryFaceFlags] using hv
    exact boundary_edges_of_face Q
      (hBT v0 v1 v2 (by decide) (by decide) (by decide)
        hf hv'.1.1 hv'.1.2 hv'.2)
  · intro hv hf
    have hv' :
        (Q.boundary.simplex (SingletonVertexSet v0) = true ∧
        Q.boundary.simplex (SingletonVertexSet v1) = true) ∧
        Q.boundary.simplex (SingletonVertexSet v3) = true := by
      simpa [encodePair, allBoundaryFaceFlags] using hv
    exact boundary_edges_of_face Q
      (hBT v0 v1 v3 (by decide) (by decide) (by decide)
        hf hv'.1.1 hv'.1.2 hv'.2)
  · intro hv hf
    have hv' :
        (Q.boundary.simplex (SingletonVertexSet v0) = true ∧
        Q.boundary.simplex (SingletonVertexSet v2) = true) ∧
        Q.boundary.simplex (SingletonVertexSet v3) = true := by
      simpa [encodePair, allBoundaryFaceFlags] using hv
    exact boundary_edges_of_face Q
      (hBT v0 v2 v3 (by decide) (by decide) (by decide)
        hf hv'.1.1 hv'.1.2 hv'.2)
  · intro hv hf
    have hv' :
        (Q.boundary.simplex (SingletonVertexSet v1) = true ∧
        Q.boundary.simplex (SingletonVertexSet v2) = true) ∧
        Q.boundary.simplex (SingletonVertexSet v3) = true := by
      simpa [encodePair, allBoundaryFaceFlags] using hv
    exact boundary_edges_of_face Q
      (hBT v1 v2 v3 (by decide) (by decide) (by decide)
        hf hv'.1.1 hv'.1.2 hv'.2)

/-- Lemma 7.1: the actual induced pair has an admissible Boolean encoding. -/
theorem encoded_induced_four_pair_admissible_source
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    Admissible (encodePair (inducedPair P L)) := by
  exact encodePair_admissible (inducedPair P L) (induced_bt L hBT)

/-- Actual non-boundary triangular generators of `C₂(K,K∂;F₂)`. -/
def actualRelativeFaces (Q : FiniteSimplicialPair 4) : Chain2 :=
  ⟨Q.ambient.simplex f012 && (!Q.boundary.simplex f012),
    Q.ambient.simplex f013 && (!Q.boundary.simplex f013),
    Q.ambient.simplex f023 && (!Q.boundary.simplex f023),
    Q.ambient.simplex f123 && (!Q.boundary.simplex f123)⟩

/-- Quotient a 1-chain by the actual boundary edges. -/
def quotientBoundaryEdges (Q : FiniteSimplicialPair 4) (x : Chain1) : Chain1 :=
  let b := (encodePair Q).boundaryEdges
  ⟨x.e01 && (!b.e01), x.e02 && (!b.e02), x.e03 && (!b.e03),
    x.e12 && (!b.e12), x.e13 && (!b.e13), x.e23 && (!b.e23)⟩

/-- Relative `d₂` in the actual induced coordinate complex. -/
def actualRelativeD2 (Q : FiniteSimplicialPair 4) (z : Chain2) : Chain1 :=
  quotientBoundaryEdges Q (d2 z)

/-- Relative `d₃(1)` in the actual induced coordinate complex. -/
def actualD3Boundary (Q : FiniteSimplicialPair 4) : Chain2 :=
  if Q.ambient.simplex FullVertexSet then actualRelativeFaces Q else zero2

def ActualRelativeCycle (Q : FiniteSimplicialPair 4) (z : Chain2) : Prop :=
  Supported2 (actualRelativeFaces Q) z ∧ actualRelativeD2 Q z = zero1

def ActualHomologous (Q : FiniteSimplicialPair 4) (x y : Chain2) : Prop :=
  x = y ∨ x = add2 y (actualD3Boundary Q)

private theorem boundary_face_flags_iff (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) (a b d : Fin 4)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hface : Q.ambient.simplex (TriangleVertexSet a b d) = true) :
    Q.boundary.simplex (TriangleVertexSet a b d) = true ↔
      Q.boundary.simplex (SingletonVertexSet a) = true ∧
      Q.boundary.simplex (SingletonVertexSet b) = true ∧
      Q.boundary.simplex (SingletonVertexSet d) = true := by
  constructor
  · intro h
    have habd := boundary_edges_of_face Q h
    exact ⟨(boundary_vertex_of_edge Q habd.1).1,
      (boundary_vertex_of_edge Q habd.1).2,
      (boundary_vertex_of_edge Q habd.2.2).2⟩
  · rintro ⟨ha, hb, hd⟩
    exact hBT a b d hab had hbd hface ha hb hd

private theorem relative_face_bit
    (Q : FiniteSimplicialPair 4) (hBT : BoundaryTriangleCondition Q)
    (a b d : Fin 4) (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) :
    (Q.ambient.simplex (TriangleVertexSet a b d) &&
        (!Q.boundary.simplex (TriangleVertexSet a b d))) =
      (Q.ambient.simplex (TriangleVertexSet a b d) &&
        (!(Q.boundary.simplex (SingletonVertexSet a) &&
          Q.boundary.simplex (SingletonVertexSet b) &&
          Q.boundary.simplex (SingletonVertexSet d)))) := by
  cases hface : Q.ambient.simplex (TriangleVertexSet a b d) with
  | false => simp
  | true =>
      have hiff := boundary_face_flags_iff Q hBT a b d hab had hbd hface
      cases htri : Q.boundary.simplex (TriangleVertexSet a b d) <;>
        cases ha : Q.boundary.simplex (SingletonVertexSet a) <;>
        cases hb : Q.boundary.simplex (SingletonVertexSet b) <;>
        cases hd : Q.boundary.simplex (SingletonVertexSet d) <;>
        simp_all

private theorem actualRelativeFaces_eq (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) :
    actualRelativeFaces Q = relativeFaces (encodePair Q) := by
  simp only [actualRelativeFaces, relativeFaces, encodePair,
    allBoundaryFaceFlags, Chain2.mk.injEq]
  exact ⟨relative_face_bit Q hBT v0 v1 v2 (by decide) (by decide) (by decide),
    relative_face_bit Q hBT v0 v1 v3 (by decide) (by decide) (by decide),
    relative_face_bit Q hBT v0 v2 v3 (by decide) (by decide) (by decide),
    relative_face_bit Q hBT v1 v2 v3 (by decide) (by decide) (by decide)⟩

private theorem bit_quotient_zero_iff (x b : Bool) :
    (x && (!b)) = false ↔ (x = true → b = true) := by
  cases x <;> cases b <;> decide

private theorem quotientBoundaryEdges_eq_zero_iff
    (Q : FiniteSimplicialPair 4) (x : Chain1) :
    quotientBoundaryEdges Q x = zero1 ↔
      SupportedOnBoundaryEdges (encodePair Q).boundaryEdges x := by
  rcases x with ⟨x01, x02, x03, x12, x13, x23⟩
  let b := (encodePair Q).boundaryEdges
  change
    (⟨x01 && (!b.e01), x02 && (!b.e02), x03 && (!b.e03),
      x12 && (!b.e12), x13 && (!b.e13), x23 && (!b.e23)⟩ : Chain1) = zero1 ↔
      SupportedOnBoundaryEdges b ⟨x01, x02, x03, x12, x13, x23⟩
  rcases b with ⟨b01, b02, b03, b12, b13, b23⟩
  simp only [zero1, Chain1.mk.injEq, SupportedOnBoundaryEdges]
  exact and_congr (bit_quotient_zero_iff x01 b01)
    (and_congr (bit_quotient_zero_iff x02 b02)
      (and_congr (bit_quotient_zero_iff x03 b03)
        (and_congr (bit_quotient_zero_iff x12 b12)
          (and_congr (bit_quotient_zero_iff x13 b13)
            (bit_quotient_zero_iff x23 b23)))))

private theorem actualRelativeCycle_iff (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) (z : Chain2) :
    ActualRelativeCycle Q z ↔ RelativeCycle (encodePair Q) z := by
  rw [ActualRelativeCycle, RelativeCycle, actualRelativeD2,
    actualRelativeFaces_eq Q hBT, quotientBoundaryEdges_eq_zero_iff]

private theorem actualD3Boundary_eq (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) :
    actualD3Boundary Q = d3Boundary (encodePair Q) := by
  unfold actualD3Boundary d3Boundary
  rw [actualRelativeFaces_eq Q hBT]
  rfl

private theorem actualHomologous_iff (Q : FiniteSimplicialPair 4)
    (hBT : BoundaryTriangleCondition Q) (x y : Chain2) :
    ActualHomologous Q x y ↔ Homologous (encodePair Q) x y := by
  rw [ActualHomologous, Homologous, actualD3Boundary_eq Q hBT]

/-- Exact coordinate identification of the actual relative `C₂ → C₁` map,
the `d₃` generator, cycles, and boundary equivalence with `FourVertexPair`. -/
theorem induced_four_coordinate_chain_identification_source
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    let Q := inducedPair P L
    let c := encodePair Q
    actualRelativeFaces Q = relativeFaces c ∧
      (∀ z, ActualRelativeCycle Q z ↔ RelativeCycle c z) ∧
      actualD3Boundary Q = d3Boundary c ∧
      (∀ x y, ActualHomologous Q x y ↔ Homologous c x y) := by
  dsimp
  let hBTQ := induced_bt L hBT
  exact ⟨actualRelativeFaces_eq _ hBTQ,
    actualRelativeCycle_iff _ hBTQ,
    actualD3Boundary_eq _ hBTQ,
    actualHomologous_iff _ hBTQ⟩

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

/-- Actual `H₂(K,K∂;F₂)` of the induced coordinate complex. -/
abbrev InducedRelativeH2 (Q : FiniteSimplicialPair 4) :=
  Quotient (actualHomologySetoid Q)

def ActualHomologyDimensionAtMostOne (Q : FiniteSimplicialPair 4) : Prop :=
  ∀ q₀ q₁ q₂ : InducedRelativeH2 Q,
    q₀ = q₁ ∨ q₀ = q₂ ∨ q₁ = q₂

/-- Lemma 4.3 at the ambient level: the actual pair induced by a labelled
four-clique under (BT) has at most two F₂ relative-homology classes. -/
theorem induced_four_clique_relative_homology_bound_source
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    ActualHomologyDimensionAtMostOne (inducedPair P L) := by
  let Q := inducedPair P L
  let c := encodePair Q
  have hBTQ : BoundaryTriangleCondition Q := induced_bt L hBT
  have hadm : Admissible c := encodePair_admissible Q hBTQ
  have hmodel : HomologyDimensionAtMostOne c :=
    admissible_four_vertex_relative_homology_bound c hadm
  intro q₀ q₁ q₂
  refine Quotient.inductionOn₃ q₀ q₁ q₂ ?_
  intro x y z
  let xm : CycleSpace c := ⟨x.1, (actualRelativeCycle_iff Q hBTQ x.1).1 x.2⟩
  let ym : CycleSpace c := ⟨y.1, (actualRelativeCycle_iff Q hBTQ y.1).1 y.2⟩
  let zm : CycleSpace c := ⟨z.1, (actualRelativeCycle_iff Q hBTQ z.1).1 z.2⟩
  rcases hmodel (Quotient.mk _ xm) (Quotient.mk _ ym) (Quotient.mk _ zm) with
    hxy | hxz | hyz
  · left
    apply Quotient.sound
    exact (actualHomologous_iff Q hBTQ x.1 y.1).2 (Quotient.exact hxy)
  · right; left
    apply Quotient.sound
    exact (actualHomologous_iff Q hBTQ x.1 z.1).2 (Quotient.exact hxz)
  · right; right
    apply Quotient.sound
    exact (actualHomologous_iff Q hBTQ y.1 z.1).2 (Quotient.exact hyz)

#print axioms encoded_induced_four_pair_admissible_source
#print axioms induced_four_coordinate_chain_identification_source
#print axioms induced_four_clique_relative_homology_bound_source

end K331Tutte.FiniteHomology.Ambient
