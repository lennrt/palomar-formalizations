/-
Algebraic core of the degree-one join calculation over F₂.

For augmented vector spaces A and B, the tensors whose two marginals vanish
are exactly the tensors of their augmentation kernels.  In a flag-complex
join, A and B are the component-coordinate chain spaces obtained after mixed
triangle boundaries identify vertices inside each component.

Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import Mathlib

namespace ExtremalJoinLemma

abbrev F₂ := ZMod 2

noncomputable section

variable {A B : Type*}
variable [AddCommGroup A] [Module F₂ A]
variable [AddCommGroup B] [Module F₂ B]

lemma f2_add_self {M : Type*} [AddCommGroup M] [Module F₂ M] (x : M) : x + x = 0 := by
  calc
    x + x = (1 : F₂) • x + (1 : F₂) • x := by simp
    _ = ((1 : F₂) + 1) • x := by rw [add_smul]
    _ = 0 := by
      have htwo : (1 : F₂) + 1 = 0 := by decide
      rw [htwo, zero_smul]

/-- Contract the right tensor factor with its augmentation. -/
def rightMarginal (εB : B →ₗ[F₂] F₂) : TensorProduct F₂ A B →ₗ[F₂] A :=
  (TensorProduct.rid F₂ A).toLinearMap.comp (εB.lTensor A)

/-- Contract the left tensor factor with its augmentation. -/
def leftMarginal (εA : A →ₗ[F₂] F₂) : TensorProduct F₂ A B →ₗ[F₂] B :=
  (TensorProduct.lid F₂ B).toLinearMap.comp (εA.rTensor B)

@[simp] lemma rightMarginal_tmul (εB : B →ₗ[F₂] F₂) (a : A) (b : B) :
    rightMarginal εB (a ⊗ₜ b) = εB b • a := by
  simp [rightMarginal]

@[simp] lemma leftMarginal_tmul (εA : A →ₗ[F₂] F₂) (a : A) (b : B) :
    leftMarginal εA (a ⊗ₜ b) = εA a • b := by
  simp [leftMarginal]

/-- Tensors satisfying both joined-graph cycle equations. -/
def DoubleMarginalSubmodule (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    Submodule F₂ (TensorProduct F₂ A B) :=
  LinearMap.ker (rightMarginal εB) ⊓ LinearMap.ker (leftMarginal εA)

/-- Projection onto the augmentation kernel, using a vector of augmentation one.
Over F₂ subtraction is addition. -/
def toAugmentationKernel (ε : A →ₗ[F₂] F₂) (a₀ : A) (ha₀ : ε a₀ = 1) :
    A →ₗ[F₂] LinearMap.ker ε where
  toFun a := ⟨a + ε a • a₀, by
    change ε (a + ε a • a₀) = 0
    rw [map_add, map_smul, ha₀, smul_eq_mul, mul_one]
    exact f2_add_self (ε a)⟩
  map_add' a a' := by
    apply Subtype.ext
    change (a + a') + ε (a + a') • a₀ =
      (a + ε a • a₀) + (a' + ε a' • a₀)
    rw [map_add, add_smul]
    abel
  map_smul' r a := by
    apply Subtype.ext
    change r • a + ε (r • a) • a₀ = r • (a + ε a • a₀)
    simp only [map_smul, smul_eq_mul, smul_add, smul_smul]

@[simp] lemma toAugmentationKernel_coe
    (ε : A →ₗ[F₂] F₂) (a₀ : A) (ha₀ : ε a₀ = 1) (a : LinearMap.ker ε) :
    ((toAugmentationKernel ε a₀ ha₀ a : LinearMap.ker ε) : A) = a := by
  change (a : A) + ε a • a₀ = a
  rw [a.property, zero_smul, add_zero]

/-- Include a tensor of augmentation-zero vectors into the ambient tensor product. -/
def includeReducedTensor (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB) →ₗ[F₂]
      TensorProduct F₂ A B :=
  TensorProduct.map (LinearMap.ker εA).subtype (LinearMap.ker εB).subtype

lemma rightMarginal_includeReducedTensor
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (t : TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB)) :
    rightMarginal εB (includeReducedTensor εA εB t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [includeReducedTensor]
  | add x y hx hy => simp [hx, hy]

lemma leftMarginal_includeReducedTensor
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (t : TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB)) :
    leftMarginal εA (includeReducedTensor εA εB t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [includeReducedTensor]
  | add x y hx hy => simp [hx, hy]

/-- The canonical inclusion, with codomain restricted to the two cycle equations. -/
def reducedTensorToDoubleMarginal
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB) →ₗ[F₂]
      DoubleMarginalSubmodule εA εB where
  toFun t := ⟨includeReducedTensor εA εB t,
    ⟨rightMarginal_includeReducedTensor εA εB t,
      leftMarginal_includeReducedTensor εA εB t⟩⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

/-- Explicit inverse candidate obtained by projecting each tensor factor. -/
def doubleMarginalToReducedTensor
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1) :
    DoubleMarginalSubmodule εA εB →ₗ[F₂]
      TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB) :=
  (TensorProduct.map (toAugmentationKernel εA a₀ ha₀)
    (toAugmentationKernel εB b₀ hb₀)).comp
      (DoubleMarginalSubmodule εA εB).subtype

lemma doubleMarginalToReducedTensor_leftInverse
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1)
    (t : TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB)) :
    doubleMarginalToReducedTensor εA εB a₀ ha₀ b₀ hb₀
        (reducedTensorToDoubleMarginal εA εB t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      change (toAugmentationKernel εA a₀ ha₀ (a : A)) ⊗ₜ
        (toAugmentationKernel εB b₀ hb₀ (b : B)) = a ⊗ₜ b
      have ha : toAugmentationKernel εA a₀ ha₀ (a : A) = a := by
        apply Subtype.ext
        exact toAugmentationKernel_coe εA a₀ ha₀ a
      have hb : toAugmentationKernel εB b₀ hb₀ (b : B) = b := by
        apply Subtype.ext
        exact toAugmentationKernel_coe εB b₀ hb₀ b
      rw [ha, hb]
  | add x y hx hy => simp [hx, hy]

lemma include_projection_expansion
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1)
    (t : TensorProduct F₂ A B) :
    includeReducedTensor εA εB
        (TensorProduct.map (toAugmentationKernel εA a₀ ha₀)
          (toAugmentationKernel εB b₀ hb₀) t) =
      t + (rightMarginal εB t ⊗ₜ b₀) +
        (a₀ ⊗ₜ leftMarginal εA t) +
        εA (rightMarginal εB t) • (a₀ ⊗ₜ b₀) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      simp only [TensorProduct.map_tmul, includeReducedTensor,
        toAugmentationKernel, rightMarginal_tmul, leftMarginal_tmul,
        LinearMap.coe_mk, AddHom.coe_mk]
      simp only [Submodule.coe_subtype,
        TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.tmul_smul, map_smul, smul_eq_mul,
        TensorProduct.smul_add, TensorProduct.smul_tmul', smul_smul]
      rw [mul_comm (εB b) (εA a)]
      abel
  | add x y hx hy =>
      simp only [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
      module

lemma doubleMarginalToReducedTensor_rightInverse
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1)
    (t : DoubleMarginalSubmodule εA εB) :
    reducedTensorToDoubleMarginal εA εB
        (doubleMarginalToReducedTensor εA εB a₀ ha₀ b₀ hb₀ t) = t := by
  ext
  change includeReducedTensor εA εB
      (TensorProduct.map (toAugmentationKernel εA a₀ ha₀)
        (toAugmentationKernel εB b₀ hb₀) (t : TensorProduct F₂ A B)) = t
  rw [include_projection_expansion]
  have hr : rightMarginal εB (t : TensorProduct F₂ A B) = 0 := t.property.1
  have hl : leftMarginal εA (t : TensorProduct F₂ A B) = 0 := t.property.2
  simp [hr, hl]

/-- The algebraic Künneth calculation in degree one for a join, after the
mixed-triangle component normalization.  The equivalence is explicit and
uses only a choice of augmentation-one vectors. -/
def tensor_reduced_equiv_doubleMarginalKernel
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1) :
    TensorProduct F₂ (LinearMap.ker εA) (LinearMap.ker εB) ≃ₗ[F₂]
      DoubleMarginalSubmodule εA εB where
  toFun := reducedTensorToDoubleMarginal εA εB
  invFun := doubleMarginalToReducedTensor εA εB a₀ ha₀ b₀ hb₀
  map_add' := map_add _
  map_smul' := map_smul _
  left_inv := doubleMarginalToReducedTensor_leftInverse εA εB a₀ ha₀ b₀ hb₀
  right_inv := doubleMarginalToReducedTensor_rightInverse εA εB a₀ ha₀ b₀ hb₀

section AbstractJoinedChains

variable {EA EB : Type*}
variable [AddCommGroup EA] [Module F₂ EA]
variable [AddCommGroup EB] [Module F₂ EB]

/-- Degree-one chains of a join, split into left internal edges, cross edges,
and right internal edges. -/
abbrev AbstractJoinChain1 :=
  EA × (TensorProduct F₂ A B × EB)

/-- The mixed two-simplices needed in degree one: a left edge with a right
vertex, or a left vertex with a right edge. -/
abbrev AbstractJoinMixedChain2 :=
  TensorProduct F₂ EA B × TensorProduct F₂ A EB

/-- The joined boundary on the split chain coordinates. -/
def abstractJoinD1
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    AbstractJoinChain1 (A := A) (B := B) (EA := EA) (EB := EB) →ₗ[F₂] A × B where
  toFun c :=
    (dA c.1 + rightMarginal εB c.2.1,
      leftMarginal εA c.2.1 + dB c.2.2)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    all_goals abel
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
      RingHom.id_apply]

/-- Boundary of mixed triangles in the split chain coordinates. -/
def abstractJoinMixedD2
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    AbstractJoinMixedChain2 (A := A) (B := B) (EA := EA) (EB := EB) →ₗ[F₂]
      AbstractJoinChain1 (A := A) (B := B) (EA := EA) (EB := EB) where
  toFun c :=
    (rightMarginal εB c.1,
      (TensorProduct.map dA LinearMap.id c.1 +
        TensorProduct.map LinearMap.id dB c.2,
       leftMarginal εA c.2))
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, map_add]
    all_goals abel
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, map_smul, smul_add,
      RingHom.id_apply]

lemma rightMarginal_map_left
    (dA : EA →ₗ[F₂] A) (εB : B →ₗ[F₂] F₂)
    (t : TensorProduct F₂ EA B) :
    rightMarginal εB (TensorProduct.map dA LinearMap.id t) =
      dA (rightMarginal εB t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e b => simp
  | add x y hx hy => simp [hx, hy]

lemma leftMarginal_map_right
    (dB : EB →ₗ[F₂] B) (εA : A →ₗ[F₂] F₂)
    (t : TensorProduct F₂ A EB) :
    leftMarginal εA (TensorProduct.map LinearMap.id dB t) =
      dB (leftMarginal εA t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp
  | add x y hx hy => simp [hx, hy]

lemma rightMarginal_map_right_eq_zero
    (dB : EB →ₗ[F₂] B) (εB : B →ₗ[F₂] F₂)
    (hB : ∀ e, εB (dB e) = 0) (t : TensorProduct F₂ A EB) :
    rightMarginal εB (TensorProduct.map LinearMap.id dB t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [hB e]
  | add x y hx hy => simp [hx, hy]

lemma leftMarginal_map_left_eq_zero
    (dA : EA →ₗ[F₂] A) (εA : A →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (t : TensorProduct F₂ EA B) :
    leftMarginal εA (TensorProduct.map dA LinearMap.id t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e b => simp [hA e]
  | add x y hx hy => simp [hx, hy]

lemma abstractJoinD1_mixedD2
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0)
    (c : AbstractJoinMixedChain2 (A := A) (B := B) (EA := EA) (EB := EB)) :
    abstractJoinD1 dA dB εA εB (abstractJoinMixedD2 dA dB εA εB c) = 0 := by
  apply Prod.ext
  · change dA (rightMarginal εB c.1) +
      rightMarginal εB (TensorProduct.map dA LinearMap.id c.1 +
        TensorProduct.map LinearMap.id dB c.2) = 0
    rw [map_add, rightMarginal_map_left,
      rightMarginal_map_right_eq_zero dB εB hB, add_zero]
    exact f2_add_self _
  · change leftMarginal εA (TensorProduct.map dA LinearMap.id c.1 +
        TensorProduct.map LinearMap.id dB c.2) +
      dB (leftMarginal εA c.2) = 0
    rw [map_add, leftMarginal_map_left_eq_zero dA εA hA,
      leftMarginal_map_right, zero_add]
    exact f2_add_self _

def AbstractJoinCycleSubmodule
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :
    Submodule F₂ (AbstractJoinChain1 (A := A) (B := B) (EA := EA) (EB := EB)) :=
  LinearMap.ker (abstractJoinD1 dA dB εA εB)

abbrev AbstractJoinCycle
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂) :=
  AbstractJoinCycleSubmodule dA dB εA εB

def abstractJoinMixedD2Cycle
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :
    AbstractJoinMixedChain2 (A := A) (B := B) (EA := EA) (EB := EB) →ₗ[F₂]
      AbstractJoinCycle dA dB εA εB where
  toFun c := ⟨abstractJoinMixedD2 dA dB εA εB c,
    abstractJoinD1_mixedD2 dA dB εA εB hA hB c⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp

def AbstractJoinBoundarySubmodule
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :
    Submodule F₂ (AbstractJoinCycle dA dB εA εB) :=
  LinearMap.range (abstractJoinMixedD2Cycle dA dB εA εB hA hB)

abbrev AbstractJoinH1
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :=
  AbstractJoinCycle dA dB εA εB ⧸
    AbstractJoinBoundarySubmodule dA dB εA εB hA hB

/-- The augmentation induced on the quotient by internal edge boundaries. -/
def quotientAugmentation
    (dA : EA →ₗ[F₂] A) (εA : A →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) :
    (A ⧸ LinearMap.range dA) →ₗ[F₂] F₂ :=
  Submodule.liftQ (LinearMap.range dA) εA (by
    rintro _ ⟨e, rfl⟩
    exact hA e)

@[simp] lemma quotientAugmentation_mk
    (dA : EA →ₗ[F₂] A) (εA : A →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (a : A) :
    quotientAugmentation dA εA hA (Submodule.Quotient.mk a) = εA a := by
  rfl

lemma rightMarginal_map_quotients
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εB : B →ₗ[F₂] F₂) (hB : ∀ e, εB (dB e) = 0)
    (t : TensorProduct F₂ A B) :
    rightMarginal (quotientAugmentation dB εB hB)
        (TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ t) =
      (LinearMap.range dA).mkQ (rightMarginal εB t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

lemma leftMarginal_map_quotients
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (hA : ∀ e, εA (dA e) = 0)
    (t : TensorProduct F₂ A B) :
    leftMarginal (quotientAugmentation dA εA hA)
        (TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ t) =
      (LinearMap.range dB).mkQ (leftMarginal εA t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp [hx, hy]

lemma mkQ_range_apply (dA : EA →ₗ[F₂] A) (e : EA) :
    (LinearMap.range dA).mkQ (dA e) = 0 := by
  change (Submodule.Quotient.mk (dA e) : A ⧸ LinearMap.range dA) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact LinearMap.mem_range_self dA e

/-- Component-normalized cross-edge matrix of an abstract joined cycle. -/
def abstractJoinNormal
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :
    AbstractJoinCycle dA dB εA εB →ₗ[F₂]
      DoubleMarginalSubmodule (quotientAugmentation dA εA hA)
        (quotientAugmentation dB εB hB) where
  toFun c :=
    ⟨TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ c.1.2.1,
      by
        constructor
        · change rightMarginal (quotientAugmentation dB εB hB)
              (TensorProduct.map (LinearMap.range dA).mkQ
                (LinearMap.range dB).mkQ c.1.2.1) = 0
          rw [rightMarginal_map_quotients]
          have hc := congrArg Prod.fst c.2
          change dA c.1.1 + rightMarginal εB c.1.2.1 = 0 at hc
          have hq := congrArg (LinearMap.range dA).mkQ hc
          simpa only [map_add, map_zero, mkQ_range_apply, zero_add] using hq
        · change leftMarginal (quotientAugmentation dA εA hA)
              (TensorProduct.map (LinearMap.range dA).mkQ
                (LinearMap.range dB).mkQ c.1.2.1) = 0
          rw [leftMarginal_map_quotients]
          have hc := congrArg Prod.snd c.2
          change leftMarginal εA c.1.2.1 + dB c.1.2.2 = 0 at hc
          have hq := congrArg (LinearMap.range dB).mkQ hc
          simpa only [map_add, map_zero, mkQ_range_apply, add_zero] using hq⟩
  map_add' _ _ := by
    apply Subtype.ext
    simp
  map_smul' _ _ := by
    apply Subtype.ext
    simp

lemma quotientTensor_kills_left
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (t : TensorProduct F₂ EA B) :
    TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ
        (TensorProduct.map dA LinearMap.id t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul e b =>
      have he : (Submodule.Quotient.mk (dA e) :
          A ⧸ LinearMap.range dA) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact LinearMap.mem_range_self dA e
      change (Submodule.Quotient.mk (dA e) : A ⧸ LinearMap.range dA) ⊗ₜ[F₂]
        (Submodule.Quotient.mk b : B ⧸ LinearMap.range dB) = 0
      rw [he, TensorProduct.zero_tmul]
  | add x y hx hy => simp [hx, hy]

lemma quotientTensor_kills_right
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (t : TensorProduct F₂ A EB) :
    TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ
        (TensorProduct.map LinearMap.id dB t) = 0 := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
      have he : (Submodule.Quotient.mk (dB e) :
          B ⧸ LinearMap.range dB) = 0 := by
        rw [Submodule.Quotient.mk_eq_zero]
        exact LinearMap.mem_range_self dB e
      change (Submodule.Quotient.mk a : A ⧸ LinearMap.range dA) ⊗ₜ[F₂]
        (Submodule.Quotient.mk (dB e) : B ⧸ LinearMap.range dB) = 0
      rw [he, TensorProduct.tmul_zero]
  | add x y hx hy => simp [hx, hy]

lemma abstractJoinNormal_mixedD2
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0)
    (c : AbstractJoinMixedChain2 (A := A) (B := B) (EA := EA) (EB := EB)) :
    abstractJoinNormal dA dB εA εB hA hB
        (abstractJoinMixedD2Cycle dA dB εA εB hA hB c) = 0 := by
  ext
  change TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ
      (TensorProduct.map dA LinearMap.id c.1 +
        TensorProduct.map LinearMap.id dB c.2) = 0
  rw [map_add, quotientTensor_kills_left, quotientTensor_kills_right, add_zero]

lemma abstractJoinBoundary_le_normal_ker
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :
    AbstractJoinBoundarySubmodule dA dB εA εB hA hB ≤
      LinearMap.ker (abstractJoinNormal dA dB εA εB hA hB) := by
  rintro _ ⟨c, rfl⟩
  exact abstractJoinNormal_mixedD2 dA dB εA εB hA hB c

lemma quotientMap_exact (dA : EA →ₗ[F₂] A) :
    Function.Exact dA (LinearMap.range dA).mkQ := by
  rw [LinearMap.exact_iff, Submodule.ker_mkQ]

lemma quotientTensor_ker
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B) :
    LinearMap.ker
        (TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ) =
      LinearMap.range (dB.lTensor A) ⊔ LinearMap.range (dA.rTensor B) := by
  exact TensorProduct.map_ker (quotientMap_exact dA)
    (Submodule.mkQ_surjective _) (quotientMap_exact dB)
    (Submodule.mkQ_surjective _)

lemma quotientTensor_surjective
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B) :
    Function.Surjective
      (TensorProduct.map (LinearMap.range dA).mkQ (LinearMap.range dB).mkQ) :=
  TensorProduct.map_surjective (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)

/-- The normal cross matrix detects mixed-boundary classes exactly.  The two
augmentation-one vectors are the algebraic form of choosing one vertex in
each nonempty side of the graph join. -/
lemma ker_abstractJoinNormal_eq_mixedBoundary
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1) :
    LinearMap.ker (abstractJoinNormal dA dB εA εB hA hB) =
      AbstractJoinBoundarySubmodule dA dB εA εB hA hB := by
  apply le_antisymm
  · intro c hc
    have ht : c.1.2.1 ∈ LinearMap.ker
        (TensorProduct.map (LinearMap.range dA).mkQ
          (LinearMap.range dB).mkQ) := by
      exact LinearMap.mem_ker.mpr (congrArg Subtype.val
        (LinearMap.mem_ker.mp hc))
    rw [quotientTensor_ker] at ht
    obtain ⟨tB, htB, tA, htA, hsum⟩ := Submodule.mem_sup.mp ht
    obtain ⟨y, rfl⟩ := htB
    obtain ⟨x, rfl⟩ := htA
    have hcross :
        TensorProduct.map dA LinearMap.id x +
            TensorProduct.map LinearMap.id dB y = c.1.2.1 := by
      change (dA.rTensor B) x + (dB.lTensor A) y = c.1.2.1
      simpa [add_comm] using hsum
    let rA : EA := c.1.1 + rightMarginal εB x
    let rB : EB := c.1.2.2 + leftMarginal εA y
    have hcA : dA c.1.1 + rightMarginal εB c.1.2.1 = 0 := by
      exact congrArg Prod.fst c.2
    have hcB : leftMarginal εA c.1.2.1 + dB c.1.2.2 = 0 := by
      exact congrArg Prod.snd c.2
    have hmargA :
        rightMarginal εB c.1.2.1 = dA (rightMarginal εB x) := by
      rw [← hcross, map_add, rightMarginal_map_left,
        rightMarginal_map_right_eq_zero dB εB hB, add_zero]
    have hmargB :
        leftMarginal εA c.1.2.1 = dB (leftMarginal εA y) := by
      rw [← hcross, map_add,
        leftMarginal_map_left_eq_zero dA εA hA, zero_add,
        leftMarginal_map_right]
    have hrA : dA rA = 0 := by
      simp only [rA, map_add, ← hmargA]
      exact hcA
    have hrB : dB rB = 0 := by
      simp only [rB, map_add, ← hmargB]
      simpa [add_comm] using hcB
    refine ⟨(x + rA ⊗ₜ[F₂] b₀, y + a₀ ⊗ₜ[F₂] rB), ?_⟩
    apply Subtype.ext
    change abstractJoinMixedD2 dA dB εA εB
      (x + rA ⊗ₜ[F₂] b₀, y + a₀ ⊗ₜ[F₂] rB) = c.1
    apply Prod.ext
    · change rightMarginal εB (x + rA ⊗ₜ[F₂] b₀) = c.1.1
      simp only [map_add, rightMarginal_tmul, hb₀, one_smul, rA]
      calc
        rightMarginal εB x + (c.1.1 + rightMarginal εB x) =
            c.1.1 + (rightMarginal εB x + rightMarginal εB x) := by abel
        _ = c.1.1 := by rw [f2_add_self]; simp
    · apply Prod.ext
      · change TensorProduct.map dA LinearMap.id
              (x + rA ⊗ₜ[F₂] b₀) +
            TensorProduct.map LinearMap.id dB
              (y + a₀ ⊗ₜ[F₂] rB) = c.1.2.1
        simpa only [map_add, TensorProduct.map_tmul, LinearMap.id_apply,
          hrA, hrB, TensorProduct.zero_tmul, TensorProduct.tmul_zero,
          add_zero] using hcross
      · change leftMarginal εA (y + a₀ ⊗ₜ[F₂] rB) = c.1.2.2
        simp only [map_add, leftMarginal_tmul, ha₀, one_smul, rB]
        calc
          leftMarginal εA y + (c.1.2.2 + leftMarginal εA y) =
              c.1.2.2 + (leftMarginal εA y + leftMarginal εA y) := by abel
          _ = c.1.2.2 := by rw [f2_add_self]; simp
  · exact abstractJoinBoundary_le_normal_ker dA dB εA εB hA hB

/-- Every double-marginal class on the vertex quotients has a joined-cycle
representative: lift its cross matrix and solve the two internal boundary
equations supplied by its marginal conditions. -/
lemma abstractJoinNormal_surjective
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0) :
    Function.Surjective (abstractJoinNormal dA dB εA εB hA hB) := by
  intro q
  obtain ⟨t, ht⟩ := quotientTensor_surjective dA dB q.1
  have hrightQ : (LinearMap.range dA).mkQ (rightMarginal εB t) = 0 := by
    rw [← rightMarginal_map_quotients dA dB εB hB, ht]
    exact q.2.1
  have hleftQ : (LinearMap.range dB).mkQ (leftMarginal εA t) = 0 := by
    rw [← leftMarginal_map_quotients dA dB εA hA, ht]
    exact q.2.2
  have hrightRange : rightMarginal εB t ∈ LinearMap.range dA := by
    change (Submodule.Quotient.mk (rightMarginal εB t) :
      A ⧸ LinearMap.range dA) = 0 at hrightQ
    rwa [Submodule.Quotient.mk_eq_zero] at hrightQ
  have hleftRange : leftMarginal εA t ∈ LinearMap.range dB := by
    change (Submodule.Quotient.mk (leftMarginal εA t) :
      B ⧸ LinearMap.range dB) = 0 at hleftQ
    rwa [Submodule.Quotient.mk_eq_zero] at hleftQ
  obtain ⟨eA, heA⟩ := hrightRange
  obtain ⟨eB, heB⟩ := hleftRange
  let c : AbstractJoinCycle dA dB εA εB :=
    ⟨(eA, (t, eB)), by
      apply Prod.ext
      · change dA eA + rightMarginal εB t = 0
        rw [heA]
        exact f2_add_self _
      · change leftMarginal εA t + dB eB = 0
        rw [heB]
        exact f2_add_self _⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  exact ht

/-- Complete abstract degree-one join calculation, before graph-specific basis
coordinates are substituted. -/
noncomputable def abstractJoinH1EquivDoubleMarginal
    (dA : EA →ₗ[F₂] A) (dB : EB →ₗ[F₂] B)
    (εA : A →ₗ[F₂] F₂) (εB : B →ₗ[F₂] F₂)
    (hA : ∀ e, εA (dA e) = 0) (hB : ∀ e, εB (dB e) = 0)
    (a₀ : A) (ha₀ : εA a₀ = 1) (b₀ : B) (hb₀ : εB b₀ = 1) :
    AbstractJoinH1 dA dB εA εB hA hB ≃ₗ[F₂]
      DoubleMarginalSubmodule (quotientAugmentation dA εA hA)
        (quotientAugmentation dB εB hB) := by
  let qEquiv : AbstractJoinH1 dA dB εA εB hA hB ≃ₗ[F₂]
      AbstractJoinCycle dA dB εA εB ⧸
        LinearMap.ker (abstractJoinNormal dA dB εA εB hA hB) :=
    Submodule.Quotient.equiv _ _
      (LinearEquiv.refl F₂ (AbstractJoinCycle dA dB εA εB)) (by
        simpa using (ker_abstractJoinNormal_eq_mixedBoundary
          dA dB εA εB hA hB a₀ ha₀ b₀ hb₀).symm)
  exact qEquiv.trans <| LinearMap.quotKerEquivOfSurjective
    (abstractJoinNormal dA dB εA εB hA hB)
    (abstractJoinNormal_surjective dA dB εA εB hA hB)

end AbstractJoinedChains

end

end ExtremalJoinLemma
