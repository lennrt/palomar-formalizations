import ZombieMain.RealizeCases

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H C : G.Subgraph} {D : Diagram}
set_option maxHeartbeats 1000000

/-- Every actual triangle sharing an old edge has precisely a permitted
path attachment, or contributes no edge. -/
theorem triangle_realized (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) {a b c : V}
    (hf : TriangleFrame C a b c) (hab : H.Adj a b) :
    RealizedAttachment D H (H ⊔ C) := by
  classical
  obtain ⟨p,rfl⟩ := e.exists_label hab.fst_mem
  obtain ⟨q,rfl⟩ := e.exists_label hab.snd_mem
  have hba := hab.symm
  have hp := e.mem p
  have hq := e.mem q
  by_cases hc : c ∈ H.verts
  · obtain ⟨r,rfl⟩ := e.exists_label hc
    have hr := e.mem r
    have hverts : (H ⊔ C).verts = H.verts := by
      rw [Subgraph.verts_sup]
      apply Set.union_eq_left.mpr
      intro v hv
      rcases hf.verts.mp hv with rfl | rfl | rfl <;> assumption
    by_cases hbc : H.Adj (e.vertices q) (e.vertices r)
    · have hcb := hbc.symm
      by_cases hca : H.Adj (e.vertices r) (e.vertices p)
      · have hac := hca.symm
        apply Or.inl
        apply sup_eq_left.mpr
        constructor
        · intro v hv
          rcases hf.verts.mp hv with rfl | rfl | rfl <;> assumption
        · intro u v huv
          rw [hf.adjacency] at huv
          aesop
      · have hn : ¬ H.Adj (e.vertices p) (e.vertices r) := fun h => hca h.symm
        apply realize_edge e hmin hmax p r hf.ca.symm hn
          (D.reach_two 1 q.isLt r.isLt ((e.adjacency p q).mpr hab)
            ((e.adjacency q r).mpr hbc)) hverts
        intro u v
        simp only [Subgraph.sup_adj, hf.adjacency]
        aesop
    · have hca : H.Adj (e.vertices r) (e.vertices p) := by
        rcases old_vertex_cycle_has_old_edge (hmin _ hr) (hmax _)
          hf.bc.symm hf.ca hf.ab.ne.symm with hcb | hca
        · exact False.elim (hbc hcb.symm)
        · exact hca
      have hac := hca.symm
      apply realize_edge e hmin hmax q r hf.bc hbc
        (D.reach_two 1 p.isLt r.isLt ((e.adjacency q p).mpr hba)
          ((e.adjacency p r).mpr hac)) hverts
      intro u v
      simp only [Subgraph.sup_adj, hf.adjacency]
      aesop
  · apply realize_one e hmin hmax p q c hab.ne hc hf.ca.symm hf.bc.symm
      (D.reach_adj 1 q.isLt ((e.adjacency p q).mpr hab))
    · intro v
      simp only [Subgraph.verts_sup, Set.mem_union, hf.verts]
      aesop
    · intro u v
      simp only [Subgraph.sup_adj, hf.adjacency]
      aesop

end ZombieMain
