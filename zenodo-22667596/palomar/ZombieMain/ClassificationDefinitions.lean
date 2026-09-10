import ZombieMain.Families

namespace ZombieMain
variable {V : Type*} {G : SimpleGraph V}

def portVertices (H : G.Subgraph) : Set V :=
  {v | v ∈ H.verts ∧ (H.neighborSet v).ncard = 2}

/-- Either the unclassified one-port case, or an exact labelled catalogue
member. The embedding includes bijective vertex coverage and exact adjacency. -/
def ClassifiedSubgraph (H : G.Subgraph) : Prop :=
  (portVertices H).ncard = 1 ∨
    ∃ f : Family, f.Admissible ∧ Nonempty (f.diagram.Embedding H)

end ZombieMain
