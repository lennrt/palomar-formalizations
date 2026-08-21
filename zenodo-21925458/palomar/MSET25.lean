/-
Paper: Multiset Dimension of Cylindrical Graphs: An Infinite Family and a Certified Census
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925458
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Nat.Lattice
import Mathlib.Tactic.Ring

namespace MSET25

/-- An unordered two-entry numerical code represented canonically by `(min,max)`. -/
def pairCode (a b : ℕ) : ℕ × ℕ := (min a b, max a b)

@[simp] theorem pairCode_swap (a b : ℕ) : pairCode a b = pairCode b a := by
  simp [pairCode, min_comm, max_comm]

/-- The special case of unordered-pair symmetry with entries `0` and `d`. -/
theorem pairCode_zero_swap (d : ℕ) : pairCode 0 d = pairCode d 0 := by
  simp

/-- First rational identity obtained when the two same-parity entries are interchanged. -/
theorem swappedRowIdentity (m i a b : ℚ) :
    (m - 1 - (m - 1 - i + a) + (i + b)) / 2 = i + (b - a) / 2 := by
  ring

/-- Second rational identity obtained under the same interchange. -/
theorem swappedFirstDistanceIdentity (m i a b : ℚ) :
    (i + b) - ((m - 1 - (m - 1 - i + a) + (i + b)) / 2)
      = (a + b) / 2 := by
  ring

/-- Third rational identity obtained under the same interchange. -/
theorem swappedSecondDistanceIdentity (m i a b : ℚ) :
    (i + a) - ((m - 1 - (m - 1 - i + a) + (i + b)) / 2)
      = (3 * a - b) / 2 := by
  ring

#print axioms MSET25.pairCode_zero_swap
#print axioms MSET25.swappedRowIdentity
#print axioms MSET25.swappedFirstDistanceIdentity
#print axioms MSET25.swappedSecondDistanceIdentity

end MSET25
