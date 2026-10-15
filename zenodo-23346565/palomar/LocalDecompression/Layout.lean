module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

/-! A finite root-marked partition layout.
The layout is derived from an ordinary partition map and one root in each
fiber. Its sites are the actual non-root vertices, rather than abstract slots.
-/
namespace LocalDecompression

abbrev Fiber {V C : Type*} (part : V → C) (c : C) := {v : V // part v = c}

abbrev Sites {V C : Type*} (part : V → C) (root : C → V) (c : C) :=
  {v : V // part v = c ∧ v ≠ root c}

variable {V C : Type*} [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C]

/-- A cell is exactly one root together with its actual non-root vertices. -/
def fiberOptionEquiv (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C) :
    Fiber part c ≃ Option (Sites part root c) where
  toFun v := if h : v.val = root c then none else some ⟨v.val, v.property, h⟩
  invFun o := match o with
    | none => ⟨root c, hroot c⟩
    | some v => ⟨v.val, v.property.1⟩
  left_inv := by
    intro v
    by_cases h : v.val = root c
    · simp only [h, dite_true]
      exact Subtype.ext h.symm
    · simp only [h, dite_false]
  right_inv := by
    intro o
    cases o with
    | none => simp
    | some v => simp [v.property.2]

/-- A partition is a disjoint collection of marked blocks, derived bijectively
from its original vertex set. -/
def markedLayoutEquiv (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) :
    V ≃ Σ c, Option (Sites part root c) :=
  (Equiv.sigmaFiberEquiv part).symm.trans
    (Equiv.sigmaCongrRight (fun c => fiberOptionEquiv part root hroot c))

theorem card_sites_add_one (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C) :
    Fintype.card (Sites part root c) + 1 = Fintype.card (Fiber part c) := by
  have hc := Fintype.card_congr (fiberOptionEquiv part root hroot c)
  simpa using hc.symm

theorem card_sites (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C) :
    Fintype.card (Sites part root c) = Fintype.card (Fiber part c) - 1 := by
  have h := card_sites_add_one part root hroot c
  omega

/-- One root per cell is not an extra stored label: root status is exactly
None in the block layout, and every other vertex supplies one data digit. -/
theorem layout_root (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C) :
    (fiberOptionEquiv part root hroot c) ⟨root c, hroot c⟩ = none := by
  simp [fiberOptionEquiv]

theorem layout_nonroot (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C) (v : Sites part root c) :
    (fiberOptionEquiv part root hroot c) ⟨v.val, v.property.1⟩ = some v := by
  simp [fiberOptionEquiv, v.property.2]

end LocalDecompression
