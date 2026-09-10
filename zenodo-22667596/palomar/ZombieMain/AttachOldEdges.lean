import ZombieMain.EmbeddingFacts
import ZombieMain.PathAdjacency

namespace ZombieMain.Diagram.Embedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {H J : G.Subgraph} {D : Diagram}

def attachEdge (e : D.Embedding H) (p q : Fin D.order)
    (hv : J.verts = H.verts)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=e.vertices q) ∨ (v=e.vertices p ∧ u=e.vertices q)) :
    (D.adjoinPath p.val q.val 1).Embedding J := by
  refine ⟨e.vertices, e.injective, e.range_eq.trans hv.symm, ?_⟩
  intro u v
  change Fin D.order at u v
  rw [Diagram.adjoinPath_one, ha]
  simp [u.isLt, v.isLt, e.injective.eq_iff, Fin.ext_iff, e.adjacency]

def attachMatching (e : D.Embedding H) (a b c d : Fin D.order)
    (hv : J.verts = H.verts)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices a ∧ v=e.vertices c) ∨ (u=e.vertices c ∧ v=e.vertices a) ∨
      (u=e.vertices b ∧ v=e.vertices d) ∨ (u=e.vertices d ∧ v=e.vertices b)) :
    (D.adjoinMatching a.val b.val c.val d.val).Embedding J := by
  refine ⟨e.vertices, e.injective, e.range_eq.trans hv.symm, ?_⟩
  intro u v
  change Fin D.order at u v
  rw [ha]
  simp [Diagram.adjoinMatching, e.injective.eq_iff, Fin.ext_iff, e.adjacency]
  tauto

end ZombieMain.Diagram.Embedding
