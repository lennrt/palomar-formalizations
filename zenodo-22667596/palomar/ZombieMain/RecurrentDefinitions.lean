import ZombieDamage.FullGame

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame
variable {V : Type}

/-- A fixed survivor strategy with private memory, sampled just after each
zombie turn. Every legal zombie reply is admitted, preserves the actual
positions, and avoids capture. The reply set is explicitly nonempty. -/
structure SurvivorController (G : Graph V) where
  Memory : Type
  zombie : Memory → V
  survivor : Memory → V
  move : Memory → V
  live : ∀ m, zombie m ≠ survivor m
  legal : ∀ m, LegalSurvivor G (initial (zombie m) (survivor m)) (move m)
  replies : ∀ m, ∃ y, G.GeodesicReply (zombie m) (move m) y
  safe : ∀ m y, G.GeodesicReply (zombie m) (move m) y → y ≠ move m
  next : ∀ m y, G.GeodesicReply (zombie m) (move m) y → Memory
  next_zombie : ∀ m y h, zombie (next m y h) = y
  next_survivor : ∀ m y h, survivor (next m y h) = move m

namespace SurvivorController
variable {G : Graph V}

/-- Infinite plays include every choice of legal geodesic replies. One index
is one completed survivor move and its ensuing safe zombie turn. -/
def Runs (C : SurvivorController G) (m : Nat → C.Memory) : Prop :=
  ∀ t, ∃ y, ∃ h : G.GeodesicReply (C.zombie (m t)) (C.move (m t)) y,
    C.next (m t) y h = m (t+1)

/-- Actual departure sources, rather than a cumulative damage flag, recur
beyond every finite time on every play of the fixed controller. -/
def Recurrent (C : SurvivorController G) : Prop :=
  ∀ m, C.Runs m → ∀ x N, ∃ t, N ≤ t ∧ C.survivor (m t) = x

/-- The zombie chooses first. Finite initialization starts with the zombie's
turn and ends at actual positions represented by the infinite controller. -/
def InitializedWithin (C : SurvivorController G) (budget : Nat) : Prop :=
  ∀ z, ∃ v, z ≠ v ∧ ForcesWithin G
    (fun phase s => phase = .survivor ∧
      ∃ m, C.zombie m = s.zombie ∧ C.survivor m = s.survivor)
    budget .zombie (initial z v)

theorem run_exists (C : SurvivorController G) (start : C.Memory) :
    ∃ m, m 0 = start ∧ C.Runs m := by
  classical
  let next : C.Memory → C.Memory := fun m =>
    C.next m (Classical.choose (C.replies m)) (Classical.choose_spec (C.replies m))
  let m : Nat → C.Memory := fun n => Nat.rec start (fun _ s => next s) n
  exact ⟨m, rfl, fun t => ⟨_, Classical.choose_spec (C.replies (m t)), rfl⟩⟩

end SurvivorController

/-- One fixed strategy, valid from every original zombie start, safely
departs from every vertex infinitely often against every legal zombie play. -/
def RecurrentCoverageWithin (G : Graph V) (initialBudget : Nat) : Prop :=
  ∃ C : SurvivorController G, C.Recurrent ∧ C.InitializedWithin initialBudget

end ZombieMain
