import ZombieMain.AttachOldEdges
import ZombieMain.AttachTwoVertices
import ZombieMain.AttachmentCapacity
import ZombieMain.CycleFrames
import ZombieMain.ReachabilityFacts

namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {H J : G.Subgraph} {D : Diagram}

/-- A realized attachment specifies an exact copy of the enlarged subgraph,
as well as the port and old-path conditions used by the transition table. -/
def RealizedAttachment (D : Diagram) (H J : G.Subgraph) : Prop :=
  J=H ∨
  (∃ p q r, D.LegalPath p q r ∧ Nonempty ((D.adjoinPath p q r).Embedding J)) ∨
  ∃ a b c d, D.LegalMatching a b c d ∧
    Nonempty ((D.adjoinMatching a b c d).Embedding J)

theorem Diagram.Embedding.label_port [Fintype V] [DecidableRel G.Adj]
    (e : D.Embedding H) (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (p : Fin D.order) {w : V}
    (hpw : G.Adj (e.vertices p) w) (hnew : ¬ H.Adj (e.vertices p) w) :
    D.degree p.val = 2 := by
  rw [e.degree]
  exact new_edge_endpoint_degree (hmin _ (e.mem p)) (hmax _) hpw hnew

end ZombieMain
