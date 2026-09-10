import ZombieMain.MainDefinitions
import ZombieDamage.EventualGame
import Mathlib.Data.Finset.Max

/-!
Randy Davila introduced the zombie damage number in Definition 1 of
arXiv:2607.16382v1. This numerical interface is its formalization by
Lennart Rudolph, with the AI assistance disclosed in SOURCE_THEORY.md.
It uses the actual damaged set and the existing adversarial game semantics.
-/
namespace ZombieDamage.FullGame
variable {V : Type} [Fintype V]

/-- The number of distinct vertices already damaged. -/
noncomputable def damageCount (s : State V) : Nat := by
  classical
  exact (Finset.univ.filter s.damaged).card

/-- The survivor can guarantee at least k damaged vertices against every
zombie start and every legal geodesic reply, with one finite move bound. -/
def CanForceDamage (G : Graph V) (k : Nat) : Prop :=
  k ≤ Fintype.card V ∧ ∃ b, ∀ z, ∃ v, z ≠ v ∧
    ForcesWithin G (fun _ s => k ≤ damageCount s) b .zombie (initial z v)

/-- Feasible scores are bounded by the graph order; zero is always an
available payoff, including graphs with no distinct pair of starting vertices. -/
noncomputable def forceableScores (G : Graph V) : Finset Nat := by
  classical
  exact (Finset.range (Fintype.card V + 1)).filter (fun k => k = 0 ∨ CanForceDamage G k)

/-- Davila's zombie damage number: the largest score the survivor can
guarantee against the minimizing zombie, with zero as the default payoff. -/
noncomputable def zombieDamageNumber (G : Graph V) : Nat :=
  (forceableScores G).sup id

end ZombieDamage.FullGame
