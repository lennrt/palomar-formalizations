import ZombieMain.EmbeddingFacts

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At an old vertex of minimum internal degree two, subcubicity leaves
room for at most one new neighbor. -/
theorem new_neighbors_subsingleton {H : G.Subgraph} {v : V}
    (hmin : 2 ≤ (H.neighborSet v).ncard) (hmax : G.degree v ≤ 3) :
    (G.neighborSet v \ H.neighborSet v).Subsingleton := by
  classical
  have hs : H.neighborSet v ⊆ G.neighborSet v := fun _ h => h.adj_sub
  have hcount := Set.ncard_sdiff_add_ncard_of_subset hs
  have hcard : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree v]
  rw [hcard] at hcount
  exact Set.ncard_le_one_iff_subsingleton.mp (by omega)

theorem old_vertex_cycle_has_old_edge {H : G.Subgraph} {v a b : V}
    (hmin : 2 ≤ (H.neighborSet v).ncard) (hmax : G.degree v ≤ 3)
    (ha : G.Adj v a) (hb : G.Adj v b) (hab : a ≠ b) :
    H.Adj v a ∨ H.Adj v b := by
  classical
  by_contra hn
  simp only [not_or] at hn
  exact hab (new_neighbors_subsingleton hmin hmax ⟨ha,hn.1⟩ ⟨hb,hn.2⟩)

/-- Any endpoint of a genuinely new edge is a port of the old union. -/
theorem new_edge_endpoint_degree {H : G.Subgraph} {v w : V}
    (hmin : 2 ≤ (H.neighborSet v).ncard) (hmax : G.degree v ≤ 3)
    (hvw : G.Adj v w) (hnew : ¬ H.Adj v w) :
    (H.neighborSet v).ncard = 2 := by
  classical
  have hs : H.neighborSet v ⊆ G.neighborSet v := fun _ h => h.adj_sub
  have hcount := Set.ncard_sdiff_add_ncard_of_subset hs
  have hcard : (G.neighborSet v).ncard = G.degree v := by
    rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree v]
  rw [hcard] at hcount
  have hpos : 0 < (G.neighborSet v \ H.neighborSet v).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨w,hvw,hnew⟩
  omega

end ZombieMain
