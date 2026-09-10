import ZombieMain.ShortCycles
import Mathlib.Data.Real.Basic

namespace ZombieMain
variable {V : Type}

/-- The inside-to-outside orientations of crossing edges count each
undirected boundary edge exactly once. -/
def cutPairs (G : SimpleGraph V) (S : Set V) : Set (V×V) :=
  {p | p.1∈S ∧ p.2∉S ∧ G.Adj p.1 p.2}

/-- A lower bound for the usual edge-expansion constant. -/
def HasEdgeExpansion [Fintype V] (G : SimpleGraph V) (η : ℝ) : Prop :=
  ∀ S : Set V, S.Nonempty → 2*S.ncard≤Fintype.card V →
    η*(S.ncard : ℝ) ≤ ((cutPairs G S).ncard : ℝ)

end ZombieMain
