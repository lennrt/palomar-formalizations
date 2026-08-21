/- Exact Spectra of Generalized Cubic Subdivision Matrices.
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925578 -/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

/-! Every outer row literally translates source rows `2,...,29`; the selected
results prove the reindexing, triangular block, and characteristic polynomial. -/

noncomputable section

open Polynomial

namespace PalomarCubicHalfSpectrum

inductive ZeroRole
  | r02 | r03 | r04 | r05 | r06 | r07 | r08 | r09 | r10 | r11 | r12 | r13 | r14 | r15
  | r20 | r21 | r26 | r27
  | r16 | r17 | r18 | r19 | r22 | r28
  deriving Repr, DecidableEq, Fintype

inductive OuterRole
  | zero (role : ZeroRole)
  | r23 | r24 | r25 | r29
  deriving Repr, DecidableEq, Fintype

abbrev ReleasedOuterIndex (n : ℕ) := Fin n × OuterRole

def zeroRank : ZeroRole → Fin 24
  | .r02 => 0  | .r03 => 1  | .r04 => 2  | .r05 => 3
  | .r06 => 4  | .r07 => 5  | .r08 => 6  | .r09 => 7
  | .r10 => 8  | .r11 => 9  | .r12 => 10 | .r13 => 11
  | .r14 => 12 | .r15 => 13
  | .r20 => 14 | .r21 => 15 | .r26 => 16 | .r27 => 17
  | .r16 => 18 | .r17 => 19 | .r18 => 20 | .r19 => 21
  | .r22 => 22 | .r28 => 23

def zeroRoleOfFin (k : Fin 24) : ZeroRole :=
  match k.val with
  | 0 => .r02  | 1 => .r03  | 2 => .r04  | 3 => .r05
  | 4 => .r06  | 5 => .r07  | 6 => .r08  | 7 => .r09
  | 8 => .r10  | 9 => .r11  | 10 => .r12 | 11 => .r13
  | 12 => .r14 | 13 => .r15 | 14 => .r20 | 15 => .r21
  | 16 => .r26 | 17 => .r27 | 18 => .r16 | 19 => .r17
  | 20 => .r18 | 21 => .r19 | 22 => .r22 | 23 => .r28
  | _ => .r02

def zeroRoleEquivFin : ZeroRole ≃ Fin 24 where
  toFun := zeroRank
  invFun := zeroRoleOfFin
  left_inv z := by cases z <;> rfl
  right_inv k := by fin_cases k <;> rfl

def zeroIndexEquivFin (n : ℕ) : ZeroRole × Fin n ≃ Fin (24 * n) :=
  (zeroRoleEquivFin.prodCongr (Equiv.refl (Fin n))).trans finProdFinEquiv

def nextSector (s : Fin n) : Fin n := finRotate n s
def prevSector (s : Fin n) : Fin n := (finRotate n).symm s

@[simp] theorem nextSector_prevSector (s : Fin n) :
    nextSector (prevSector s) = s :=
  (finRotate n).apply_symm_apply s

@[simp] theorem prevSector_nextSector (s : Fin n) :
    prevSector (nextSector s) = s :=
  (finRotate n).symm_apply_apply s

@[simp] theorem nextSector_inj {s t : Fin n} :
    nextSector s = nextSector t ↔ s = t :=
  (finRotate n).injective.eq_iff

@[simp] theorem prevSector_inj {s t : Fin n} :
    prevSector s = prevSector t ↔ s = t :=
  (finRotate n).symm.injective.eq_iff

def sourceSpike {n : ℕ} (sector : Fin n) (role : OuterRole) (weight : ℝ)
    (column : ReleasedOuterIndex n) : ℝ :=
  if column = (sector, role) then weight else 0

/-- The released outer matrix, translated row-by-row from the authenticated
source after restricting away the central rows and columns. -/
def releasedOuterQ (n : ℕ) :
    Matrix (ReleasedOuterIndex n) (ReleasedOuterIndex n) ℝ := fun row column =>
  let s := row.1
  let p := prevSector s
  let q := nextSector s
  let put := fun t r w => sourceSpike t r w column
  match row.2 with
  | .zero .r02 =>
      put s (.zero .r16) (1/4) + put s (.zero .r17) (1/4) +
      put s (.zero .r22) (1/4) + put s .r23 (1/4)
  | .zero .r03 =>
      put s (.zero .r16) (1/16) + put s (.zero .r17) (3/8) +
      put s (.zero .r18) (1/16) + put s (.zero .r22) (1/16) +
      put s .r23 (3/8) + put s .r24 (1/16)
  | .zero .r04 =>
      put s (.zero .r17) (1/4) + put s (.zero .r18) (1/4) +
      put s .r23 (1/4) + put s .r24 (1/4)
  | .zero .r05 =>
      put s (.zero .r17) (1/16) + put s (.zero .r18) (3/8) +
      put s (.zero .r19) (1/16) + put s .r23 (1/16) +
      put s .r24 (3/8) + put s .r25 (1/16)
  | .zero .r06 =>
      put s (.zero .r18) (1/4) + put s (.zero .r19) (1/4) +
      put s .r24 (1/4) + put s .r25 (1/4)
  | .zero .r07 =>
      put s (.zero .r18) (1/16) + put s (.zero .r19) (3/8) +
      put q (.zero .r28) (1/16) + put s .r24 (1/16) +
      put s .r25 (3/8) + put q .r29 (1/16)
  | .zero .r08 =>
      put s (.zero .r16) (1/16) + put s (.zero .r17) (1/16) +
      put s (.zero .r22) (3/8) + put s .r23 (3/8) +
      put s (.zero .r28) (1/16) + put s .r29 (1/16)
  | .zero .r09 =>
      put s (.zero .r16) (1/64) + put s (.zero .r17) (3/32) +
      put s (.zero .r18) (1/64) + put s (.zero .r22) (3/32) +
      put s .r23 (9/16) + put s .r24 (3/32) +
      put s (.zero .r28) (1/64) + put s .r29 (3/32)
  | .zero .r10 =>
      put s (.zero .r17) (1/16) + put s (.zero .r18) (1/16) +
      put s .r23 (3/8) + put s .r24 (3/8) + put s .r29 (1/16)
  | .zero .r11 =>
      put s (.zero .r17) (1/64) + put s (.zero .r18) (3/32) +
      put s (.zero .r19) (1/64) + put s .r23 (3/32) +
      put s .r24 (9/16) + put s .r25 (3/32) + put s .r29 (1/64)
  | .zero .r12 =>
      put s (.zero .r18) (1/16) + put s (.zero .r19) (1/16) +
      put s .r24 (3/8) + put s .r25 (3/8)
  | .zero .r13 =>
      put s (.zero .r18) (1/64) + put s (.zero .r19) (3/32) +
      put q (.zero .r28) (1/64) + put s .r24 (3/32) +
      put s .r25 (9/16) + put q .r29 (3/32)
  | .zero .r14 =>
      put s (.zero .r22) (1/4) + put s .r23 (1/4) +
      put s (.zero .r28) (1/4) + put s .r29 (1/4)
  | .zero .r15 =>
      put s (.zero .r22) (1/16) + put s .r23 (3/8) +
      put s .r24 (1/16) + put s (.zero .r28) (1/16) + put s .r29 (3/8)
  | .zero .r20 =>
      put s (.zero .r22) (1/16) + put s .r23 (1/16) +
      put s (.zero .r28) (3/8) + put s .r29 (3/8) +
      put p (.zero .r19) (1/16) + put p .r25 (1/16)
  | .zero .r21 =>
      put s (.zero .r22) (1/64) + put s .r23 (3/32) +
      put s .r24 (1/64) + put s (.zero .r28) (3/32) +
      put s .r29 (9/16) + put p (.zero .r19) (1/64) + put p .r25 (3/32)
  | .zero .r26 =>
      put s (.zero .r28) (1/4) + put s .r29 (1/4) +
      put p (.zero .r19) (1/4) + put p .r25 (1/4)
  | .zero .r27 =>
      put s (.zero .r28) (1/16) + put s .r29 (3/8) +
      put p (.zero .r19) (1/16) + put p .r25 (3/8)
  | .zero .r16 =>
      put s .r23 (1/4) + put s .r24 (1/4) + put s .r29 (1/4)
  | .zero .r17 =>
      put s .r23 (1/16) + put s .r24 (3/8) +
      put s .r25 (1/16) + put s .r29 (1/16)
  | .zero .r18 => put s .r24 (1/4) + put s .r25 (1/4)
  | .zero .r19 =>
      put s .r24 (1/16) + put s .r25 (3/8) + put q .r29 (1/16)
  | .zero .r22 =>
      put s .r23 (1/16) + put s .r24 (1/16) +
      put s .r29 (3/8) + put p .r25 (1/16)
  | .zero .r28 => put s .r29 (1/4) + put p .r25 (1/4)
  | .r23 =>
      put s .r23 (1/64) + put s .r24 (3/32) + put s .r25 (1/64) +
      put s .r29 (3/32) + put p .r25 (1/64)
  | .r24 => put s .r24 (1/16) + put s .r25 (1/16)
  | .r25 => put s .r24 (1/64) + put s .r25 (3/32) + put q .r29 (1/64)
  | .r29 => put s .r29 (1/16) + put p .r25 (1/16)

def outerCore : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1 / 16, 1 / 16, 0;
     1 / 64, 3 / 32, 1 / 64;
     0,      1 / 16, 1 / 16]

def outerCoreCopies (n : ℕ) :
    Matrix (Fin 3 × Fin n) (Fin 3 × Fin n) ℝ :=
  Matrix.blockDiagonal (fun _ : Fin n => outerCore)

def singletonBlock (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.scalar (Fin n) (1 / 64)

abbrev OuterNormalIndex (n : ℕ) :=
  Fin (24 * n) ⊕ (Fin n ⊕ (Fin 3 × Fin n))

def sourceToNormal (n : ℕ) : ReleasedOuterIndex n ≃ OuterNormalIndex n where
  toFun x := match x.2 with
    | .zero z => Sum.inl (zeroIndexEquivFin n (z, x.1))
    | .r23 => Sum.inr (Sum.inl x.1)
    | .r24 => Sum.inr (Sum.inr (0, x.1))
    | .r25 => Sum.inr (Sum.inr (1, x.1))
    | .r29 => Sum.inr (Sum.inr (2, prevSector x.1))
  invFun x := match x with
    | Sum.inl k =>
        let zs := (zeroIndexEquivFin n).symm k
        (zs.2, .zero zs.1)
    | Sum.inr (Sum.inl s) => (s, .r23)
    | Sum.inr (Sum.inr (k, s)) =>
        if k = 0 then (s, .r24)
        else if k = 1 then (s, .r25)
        else (nextSector s, .r29)
  left_inv x := by
    rcases x with ⟨s, r⟩
    cases r with
    | zero z => simp
    | r23 => rfl
    | r24 => simp
    | r25 => simp
    | r29 =>
        change (nextSector (prevSector s), OuterRole.r29) = (s, .r29)
        exact congrArg (fun t => (t, OuterRole.r29))
          (nextSector_prevSector s)
  right_inv x := by
    rcases x with k | x
    · simp
    · rcases x with s | ks
      · rfl
      · rcases ks with ⟨k, s⟩
        fin_cases k
        · rfl
        · rfl
        · change Sum.inr (Sum.inr (2, prevSector (nextSector s))) =
            Sum.inr (Sum.inr (2, s))
          rw [prevSector_nextSector]

def reindexedReleasedOuterQ (n : ℕ) :
    Matrix (OuterNormalIndex n) (OuterNormalIndex n) ℝ :=
  Matrix.reindex (sourceToNormal n) (sourceToNormal n) (releasedOuterQ n)

def releasedZeroBlock (n : ℕ) :
    Matrix (Fin (24 * n)) (Fin (24 * n)) ℝ :=
  fun i j => reindexedReleasedOuterQ n (Sum.inl i) (Sum.inl j)

def releasedUpperBlock (n : ℕ) :
    Matrix (Fin (24 * n)) (Fin n ⊕ (Fin 3 × Fin n)) ℝ :=
  fun i j => reindexedReleasedOuterQ n (Sum.inl i) (Sum.inr j)

def releasedSingletonCoreBlock (n : ℕ) :
    Matrix (Fin n) (Fin 3 × Fin n) ℝ :=
  fun i j => reindexedReleasedOuterQ n (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr j))

def outerNormalForm (n : ℕ)
    (N : Matrix (Fin (24 * n)) (Fin (24 * n)) ℝ)
    (U : Matrix (Fin (24 * n)) (Fin n ⊕ (Fin 3 × Fin n)) ℝ)
    (V : Matrix (Fin n) (Fin 3 × Fin n) ℝ) :
    Matrix (OuterNormalIndex n) (OuterNormalIndex n) ℝ :=
  Matrix.fromBlocks N U 0
    (Matrix.fromBlocks (singletonBlock n) V 0 (outerCoreCopies n))

def StrictlyUpper {m : ℕ} (N : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∀ i j, j ≤ i → N i j = 0

/-- The explicit permutation puts the exact source matrix in the paper's
three-block upper-triangular normal form. -/
theorem released_outer_source_normal_form (n : ℕ) :
    reindexedReleasedOuterQ n =
      outerNormalForm n (releasedZeroBlock n) (releasedUpperBlock n)
        (releasedSingletonCoreBlock n) := by
  sorry

/-- The first `24n` source rows, ordered by the displayed topological rank,
form a strictly upper-triangular block. -/
theorem released_zero_block_strictly_upper (n : ℕ) (_hn : 3 ≤ n) :
    StrictlyUpper (releasedZeroBlock n) := by
  sorry

theorem outer_core_charpoly :
    outerCore.charpoly =
      (X - C (1 / 8 : ℝ)) * (X - C (1 / 16 : ℝ)) *
        (X - C (1 / 32 : ℝ)) := by
  sorry

theorem outer_normal_form_charpoly (n : ℕ)
    (N : Matrix (Fin (24 * n)) (Fin (24 * n)) ℝ)
    (U : Matrix (Fin (24 * n)) (Fin n ⊕ (Fin 3 × Fin n)) ℝ)
    (V : Matrix (Fin n) (Fin 3 × Fin n) ℝ)
    (hN : StrictlyUpper N) :
    (outerNormalForm n N U V).charpoly =
      X ^ (24 * n) * (X - C (1 / 64 : ℝ)) ^ n *
        (X - C (1 / 32 : ℝ)) ^ n *
        (X - C (1 / 16 : ℝ)) ^ n *
        (X - C (1 / 8 : ℝ)) ^ n := by
  sorry

/-- Theorem 7.2 for the naturally source-indexed released outer matrix. -/
theorem released_outer_charpoly (n : ℕ) (hn : 3 ≤ n) :
    (releasedOuterQ n).charpoly =
      X ^ (24 * n) * (X - C (1 / 64 : ℝ)) ^ n *
        (X - C (1 / 32 : ℝ)) ^ n *
        (X - C (1 / 16 : ℝ)) ^ n *
        (X - C (1 / 8 : ℝ)) ^ n := by
  sorry

end PalomarCubicHalfSpectrum
