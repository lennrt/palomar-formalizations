/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ExtremalFlagBetti
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

set_option maxHeartbeats 2000000

open Finset SimpleGraph

namespace ExtremalFlagBetti.Homology

open ExtremalFlagBetti

/-! ## The actual flag complex and its five-vertex normal form -/

/-- A face of the flag complex of the paper's graph `Gₙ`. -/
def FamilyFlagFace (n : ℕ) (s : Finset (Fin n)) : Prop :=
  (FamilyG n).IsClique s

/-- The five vertices of the suspension core: the three vertices of the
`K₃` remainder and the two suspension vertices `4` and `5`. -/
def CoreVertex {n : ℕ} (v : Fin n) : Prop :=
  v.val < 3 ∨ v.val = 4 ∨ v.val = 5

instance coreVertexDecidable {n : ℕ} (v : Fin n) : Decidable (CoreVertex v) := by
  unfold CoreVertex
  infer_instance

/-- The two sides of the core `K₂,₃`. -/
def BaseVertex {n : ℕ} (v : Fin n) : Prop := v.val < 3
def ApexVertex {n : ℕ} (v : Fin n) : Prop := v.val = 4 ∨ v.val = 5

/-- The vertex retraction used by the leaf reduction. It fixes
`0,1,2,4,5` and sends every other vertex to the leaf `5`. -/
def familyRetract {n : ℕ} (hn : 7 ≤ n) (v : Fin n) : Fin n :=
  if CoreVertex v then v else ⟨5, by omega⟩

@[simp] theorem familyRetract_of_core {n : ℕ} (hn : 7 ≤ n)
    {v : Fin n} (hv : CoreVertex v) : familyRetract hn v = v := by
  simp [familyRetract, hv]

theorem familyRetract_is_core {n : ℕ} (hn : 7 ≤ n) (v : Fin n) :
    CoreVertex (familyRetract hn v) := by
  by_cases hv : CoreVertex v
  · rw [familyRetract_of_core hn hv]
    exact hv
  · have hr : familyRetract hn v = (⟨5, by omega⟩ : Fin n) := by
      simp [familyRetract, hv]
    rw [hr]
    exact Or.inr (Or.inr rfl)

/-- Equation (2), specialized to the concrete family. -/
theorem family_flag_face_iff_independent {n : ℕ} (s : Finset (Fin n)) :
    FamilyFlagFace n s ↔ (FamilyH n).IsIndepSet s := by
  simp [FamilyFlagFace, FamilyG]

private theorem family_independent_original_retract
    {n : ℕ} (hn : 7 ≤ n) {s : Finset (Fin n)}
    (hs : (FamilyH n).IsIndepSet s)
    {x z : Fin n} (hx : x ∈ s) (hz : z ∈ s)
    (hne : x ≠ familyRetract hn z) :
    ¬(FamilyH n).Adj x (familyRetract hn z) := by
  by_cases hcore : CoreVertex z
  · rw [familyRetract_of_core hn hcore] at hne ⊢
    exact hs hx hz hne
  · have hzshape : z.val = 3 ∨ 6 ≤ z.val := by
      simp only [CoreVertex] at hcore
      omega
    have hr : familyRetract hn z = (⟨5, by omega⟩ : Fin n) := by
      simp [familyRetract, hcore]
    rw [hr] at hne ⊢
    have hx4 : x.val ≠ 4 := by
      intro hxv
      have hxz : x ≠ z := by
        intro heq
        have := congrArg Fin.val heq
        omega
      have hadj : (FamilyH n).Adj x z := by
        simp only [FamilyH]
        omega
      exact hs hx hz hxz hadj
    simp only [FamilyH]
    omega

/-- A concrete simplicial contiguity certificate: every flag face remains a
flag face after adjoining its image under `familyRetract`. Together with the
fixed-point and image properties above, this is the standard explicit
strong-deformation-retraction certificate from `Cl(Gₙ)=Ind(Hₙ)` onto the
five-vertex suspension core. -/
theorem family_flag_contiguous_retraction
    {n : ℕ} (hn : 7 ≤ n) (s : Finset (Fin n))
    (hs : FamilyFlagFace n s) :
    FamilyFlagFace n (s ∪ s.image (familyRetract hn)) := by
  rw [family_flag_face_iff_independent] at hs ⊢
  intro x hx y hy hxy
  simp only [Finset.mem_coe, mem_union, mem_image] at hx hy
  rcases hx with hx | ⟨a, ha, rfl⟩
  · rcases hy with hy | ⟨b, hb, rfl⟩
    · exact hs hx hy hxy
    · exact family_independent_original_retract hn hs hx hb hxy
  · rcases hy with hy | ⟨b, hb, rfl⟩
    · intro hadj
      exact family_independent_original_retract hn hs hy ha hxy.symm
        ((FamilyH n).symm hadj)
    · by_cases hacore : CoreVertex a
      · rw [familyRetract_of_core hn hacore] at hxy ⊢
        exact family_independent_original_retract hn hs ha hb hxy
      · by_cases hbcore : CoreVertex b
        · rw [familyRetract_of_core hn hbcore] at hxy ⊢
          intro hadj
          exact family_independent_original_retract hn hs hb ha hxy.symm
            ((FamilyH n).symm hadj)
        · have hra : familyRetract hn a = (⟨5, by omega⟩ : Fin n) := by
            simp [familyRetract, hacore]
          have hrb : familyRetract hn b = (⟨5, by omega⟩ : Fin n) := by
            simp [familyRetract, hbcore]
          exact (hxy (hra.trans hrb.symm)).elim

/-- On the retraction core, adjacency in `Gₙ` is exactly the complete
bipartite graph between `{0,1,2}` and `{4,5}`. -/
theorem family_core_adj_iff
    {n : ℕ} (hn : 7 ≤ n) {u v : Fin n}
    (hu : CoreVertex u) (hv : CoreVertex v) :
    (FamilyG n).Adj u v ↔
      (BaseVertex u ∧ ApexVertex v) ∨
      (ApexVertex u ∧ BaseVertex v) := by
  by_cases hbad : n < 7
  · omega
  · simp only [FamilyG, compl_adj, FamilyH, CoreVertex, BaseVertex, ApexVertex] at *
    omega

/-- The `K₂,₃` core has no triangular flag face, so its degree-two boundary
group is zero. -/
theorem family_core_triangle_free
    {n : ℕ} (hn : 7 ≤ n) {u v w : Fin n}
    (hu : CoreVertex u) (hv : CoreVertex v) (hw : CoreVertex w) :
    ¬((FamilyG n).Adj u v ∧ (FamilyG n).Adj u w ∧
      (FamilyG n).Adj v w) := by
  rw [family_core_adj_iff hn hu hv,
    family_core_adj_iff hn hu hw,
    family_core_adj_iff hn hv hw]
  simp only [BaseVertex, ApexVertex]
  omega

/-! ## Explicit F₂ first homology of the `K₂,₃` core -/

/-- Addition in F₂, represented by Booleans. -/
def f2add : Bool → Bool → Bool
  | false, b => b
  | true, false => true
  | true, true => false

/-- A 1-chain on the six edges `40,41,42,50,51,52` of the core. -/
structure CoreChain1 where
  e40 : Bool
  e41 : Bool
  e42 : Bool
  e50 : Bool
  e51 : Bool
  e52 : Bool
  deriving Repr, DecidableEq, Fintype

/-- A 0-chain on core vertices `0,1,2,4,5`. -/
structure CoreChain0 where
  v0 : Bool
  v1 : Bool
  v2 : Bool
  v4 : Bool
  v5 : Bool
  deriving Repr, DecidableEq, Fintype

/-- The F₂ boundary of a core 1-chain. -/
def coreD1 (z : CoreChain1) : CoreChain0 :=
  ⟨f2add z.e40 z.e50,
    f2add z.e41 z.e51,
    f2add z.e42 z.e52,
    f2add (f2add z.e40 z.e41) z.e42,
    f2add (f2add z.e50 z.e51) z.e52⟩

def coreZero0 : CoreChain0 := ⟨false, false, false, false, false⟩

/-- The F₂ cycle space. Since the core is triangle-free, this is its H₁. -/
def CoreCycle (z : CoreChain1) : Prop := coreD1 z = coreZero0

instance coreCycleDecidable (z : CoreChain1) : Decidable (CoreCycle z) := by
  unfold CoreCycle
  infer_instance

abbrev CoreH1 := {z : CoreChain1 // CoreCycle z}

/-- The cycle with free coefficients `a,b`; its third coefficient is `a+b`. -/
def coreCycleOf (a b : Bool) : CoreChain1 :=
  ⟨a, b, f2add a b, a, b, f2add a b⟩

theorem coreCycleOf_is_cycle (a b : Bool) : CoreCycle (coreCycleOf a b) := by
  cases a <;> cases b <;> rfl

/-- The first homology of the suspension core has two independent F₂
coordinates. -/
def coreH1EquivBoolPair : CoreH1 ≃ Bool × Bool where
  toFun z := (z.1.e40, z.1.e41)
  invFun p := ⟨coreCycleOf p.1 p.2, coreCycleOf_is_cycle p.1 p.2⟩
  left_inv := by
    rintro ⟨⟨a, b, c, d, e, f⟩, hz⟩
    simp only [CoreCycle, coreD1, coreZero0, CoreChain0.mk.injEq] at hz
    apply Subtype.ext
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;>
      simp_all [f2add, coreCycleOf]
  right_inv := by
    rintro ⟨a, b⟩
    rfl

theorem core_h1_equiv_bool_pair : Nonempty (CoreH1 ≃ Bool × Bool) :=
  ⟨coreH1EquivBoolPair⟩

/-- Equivalently, the F₂ first homology of the core has exactly four
elements, hence dimension two. -/
theorem core_h1_cardinality : Fintype.card CoreH1 = 4 := by
  rw [Fintype.card_congr coreH1EquivBoolPair]
  decide

/-- The complete paper-faithful normal-form certificate: every family flag
complex has the explicit contiguous retraction onto a triangle-free `K₂,₃`
core, and that core's F₂ first homology is `F₂²`. -/
theorem family_flag_h1_normal_form {n : ℕ} (hn : 7 ≤ n) :
    (∀ v : Fin n, CoreVertex (familyRetract hn v)) ∧
    (∀ v : Fin n, CoreVertex v → familyRetract hn v = v) ∧
    (∀ s : Finset (Fin n), FamilyFlagFace n s →
      FamilyFlagFace n (s ∪ s.image (familyRetract hn))) ∧
    (∀ u v : Fin n, CoreVertex u → CoreVertex v →
      ((FamilyG n).Adj u v ↔
        (BaseVertex u ∧ ApexVertex v) ∨
        (ApexVertex u ∧ BaseVertex v))) ∧
    Nonempty (CoreH1 ≃ Bool × Bool) := by
  refine ⟨familyRetract_is_core hn, ?_, family_flag_contiguous_retraction hn,
    ?_, ⟨coreH1EquivBoolPair⟩⟩
  · intro v hv
    exact familyRetract_of_core hn hv
  · intro u v hu hv
    exact family_core_adj_iff hn hu hv

#print axioms family_flag_face_iff_independent
#print axioms family_flag_contiguous_retraction
#print axioms family_core_adj_iff
#print axioms family_core_triangle_free
#print axioms core_h1_equiv_bool_pair
#print axioms coreH1EquivBoolPair
#print axioms core_h1_cardinality
#print axioms family_flag_h1_normal_form

end ExtremalFlagBetti.Homology
