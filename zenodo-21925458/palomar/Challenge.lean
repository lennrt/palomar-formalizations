/-
Paper: Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925458
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Multiset.MapFold
import Mathlib.Data.Multiset.ZeroCons
import Mathlib.Data.Nat.Dist
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 4000000

/-!
# The displayed resolving set for the even cylindrical family

This file states the cycle-distance locus from Lemma 1 and the resolving-set
part of Theorem 2 for the concrete cylinder `P_m □ C_(6m)`.  It does not state
the general lower bound on multiset dimension, so it does not claim that the
displayed resolving set is minimal.
-/

namespace PalomarMSET25

/-- Vertices of the cylindrical graph `P_m □ C_(6m)`, represented by row and column. -/
abbrev CylinderVertex (m : ℕ) := Fin m × Fin (6 * m)

/-- Distance in the cycle of order `N`. -/
def cycleDistance {N : ℕ} (a b : Fin N) : ℕ :=
  min (Nat.dist a.val b.val) (N - Nat.dist a.val b.val)

/-- The standard Cartesian-product distance on `P_m □ C_(6m)`. -/
def cylinderDistance {m : ℕ} (u v : CylinderVertex m) : ℕ :=
  Nat.dist u.1.val v.1.val + cycleDistance u.2 v.2

/-- The paper's displayed landmark multiset `{(0,0), (0,2m), (m-1,0)}`. -/
def displayedEvenCylinderLandmarks (m : ℕ) (hm : 1 ≤ m) :
    Multiset (CylinderVertex m) :=
  {(⟨0, hm⟩, ⟨0, by omega⟩),
    (⟨0, hm⟩, ⟨2 * m, by omega⟩),
    (⟨m - 1, by omega⟩, ⟨0, by omega⟩)}

/-- The unordered multiset of distances from `v` to the landmarks in `W`. -/
def multisetCode {m : ℕ} (W : Multiset (CylinderVertex m))
    (v : CylinderVertex m) : Multiset ℕ :=
  W.map (cylinderDistance v)

/-- A landmark multiset is resolving when its multiset-code map is injective. -/
def IsMultisetResolving {m : ℕ} (W : Multiset (CylinderVertex m)) : Prop :=
  Function.Injective (multisetCode W)

/-- The four affine pieces of the paper's cycle distance-pair locus. -/
def CyclePairLocus (m j a b : ℕ) : Prop :=
  (j ≤ 2 * m ∧ a = j ∧ b = 2 * m - j) ∨
  (2 * m ≤ j ∧ j ≤ 3 * m ∧ a = j ∧ b = j - 2 * m) ∨
  (3 * m ≤ j ∧ j ≤ 5 * m ∧ a = 6 * m - j ∧ b = j - 2 * m) ∨
  (5 * m ≤ j ∧ a = 6 * m - j ∧ b = 8 * m - j)

/-- Equation (5) / Lemma 1: the distances from `j` to columns `0` and `2m`. -/
theorem cycle_distance_pair_locus (m : ℕ) (j : Fin (6 * m)) :
    let a := cycleDistance j ⟨0, by have := j.isLt; omega⟩
    let b := cycleDistance j ⟨2 * m, by have := j.isLt; omega⟩
    CyclePairLocus m j.val a b := by
  sorry

/-- The injectivity conclusion of Lemma 1: the two cycle distances determine the column. -/
theorem cycle_distance_pair_injective (m : ℕ) (j₁ j₂ : Fin (6 * m))
    (h₀ : cycleDistance j₁ ⟨0, by have := j₁.isLt; omega⟩ =
      cycleDistance j₂ ⟨0, by have := j₂.isLt; omega⟩)
    (h₂m : cycleDistance j₁ ⟨2 * m, by have := j₁.isLt; omega⟩ =
      cycleDistance j₂ ⟨2 * m, by have := j₂.isLt; omega⟩) :
    j₁ = j₂ := by
  sorry

/-- Resolving-set half of Theorem 2 for every even `m ≥ 2`. -/
theorem even_cylinder_three_landmarks_resolve
    (m : ℕ) (hm : 2 ≤ m) (heven : 2 ∣ m) :
    IsMultisetResolving (displayedEvenCylinderLandmarks m (by omega)) := by
  sorry

end PalomarMSET25
