import ZombieMain.RealizeCases

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H C : G.Subgraph} {D : Diagram}
set_option maxHeartbeats 3000000

/-- An actual square sharing an old edge has a permitted path or matching
attachment, or contributes no edge. The two other vertices may already be old. -/
theorem square_realized (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) {a b c d : V}
    (hf : SquareFrame C a b c d) (hab : H.Adj a b) :
    RealizedAttachment D H (H ⊔ C) := by
  classical
  obtain ⟨p,rfl⟩ := e.exists_label hab.fst_mem
  obtain ⟨q,rfl⟩ := e.exists_label hab.snd_mem
  have hba := hab.symm
  have hp := e.mem p
  have hq := e.mem q
  have hdiag : e.vertices p ≠ c ∧ e.vertices q ≠ d := by
    have hn := hf.distinct
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true, not_or] at hn
    exact ⟨hn.1.2.1,hn.2.1.2⟩
  by_cases hc : c ∈ H.verts
  · obtain ⟨r,rfl⟩ := e.exists_label hc
    have hr := e.mem r
    by_cases hd : d ∈ H.verts
    · obtain ⟨s,rfl⟩ := e.exists_label hd
      have hs := e.mem s
      have hverts : (H ⊔ C).verts = H.verts := by
        rw [Subgraph.verts_sup]
        apply Set.union_eq_left.mpr
        intro v hv
        rcases hf.verts.mp hv with rfl | rfl | rfl | rfl <;> assumption
      by_cases hbc : H.Adj (e.vertices q) (e.vertices r)
      · have hcb := hbc.symm
        by_cases hcd : H.Adj (e.vertices r) (e.vertices s)
        · have hdc := hcd.symm
          by_cases hda : H.Adj (e.vertices s) (e.vertices p)
          · have had := hda.symm
            apply Or.inl
            apply sup_eq_left.mpr
            constructor
            · intro v hv
              rcases hf.verts.mp hv with rfl | rfl | rfl | rfl <;> assumption
            · intro u v huv
              rw [hf.adjacency] at huv
              aesop
          · apply realize_edge e hmin hmax s p hf.da hda
              (D.reach_three r.isLt q.isLt p.isLt ((e.adjacency s r).mpr hdc)
                ((e.adjacency r q).mpr hcb) ((e.adjacency q p).mpr hba)) hverts
            intro u v
            simp only [Subgraph.sup_adj, hf.adjacency]
            aesop
        · have hda : H.Adj (e.vertices s) (e.vertices p) := by
            rcases old_vertex_cycle_has_old_edge (hmin _ hs) (hmax _)
              hf.cd.symm hf.da hdiag.1.symm with hdc | hda
            · exact False.elim (hcd hdc.symm)
            · exact hda
          have had := hda.symm
          apply realize_edge e hmin hmax r s hf.cd hcd
            (D.reach_three q.isLt p.isLt s.isLt ((e.adjacency r q).mpr hcb)
              ((e.adjacency q p).mpr hba) ((e.adjacency p s).mpr had)) hverts
          intro u v
          simp only [Subgraph.sup_adj, hf.adjacency]
          aesop
      · have hcd : H.Adj (e.vertices r) (e.vertices s) := by
          rcases old_vertex_cycle_has_old_edge (hmin _ hr) (hmax _)
            hf.bc.symm hf.cd hdiag.2 with hcb | hcd
          · exact False.elim (hbc hcb.symm)
          · exact hcd
        have hdc := hcd.symm
        by_cases hda : H.Adj (e.vertices s) (e.vertices p)
        · have had := hda.symm
          apply realize_edge e hmin hmax q r hf.bc hbc
            (D.reach_three p.isLt s.isLt r.isLt ((e.adjacency q p).mpr hba)
              ((e.adjacency p s).mpr had) ((e.adjacency s r).mpr hdc)) hverts
          intro u v
          simp only [Subgraph.sup_adj, hf.adjacency]
          aesop
        · have hlabels : [q,p,r,s].Nodup := by
            have hn := hf.distinct
            simp [List.nodup_cons, e.injective.eq_iff, @eq_comm (Fin D.order)] at hn ⊢
            tauto
          apply realize_matching e hmin hmax q p r s hlabels hba hcd
            hf.bc hf.da.symm hbc (fun h => hda h.symm) hverts
          intro u v
          simp only [Subgraph.sup_adj, hf.adjacency]
          aesop
    · have hbc : H.Adj (e.vertices q) (e.vertices r) := by
        rcases old_vertex_cycle_has_old_edge (hmin _ hr) (hmax _)
          hf.bc.symm hf.cd hdiag.2 with hcb | hcd
        · exact hcb.symm
        · exact False.elim (hd hcd.snd_mem)
      have hcb := hbc.symm
      apply realize_one e hmin hmax r p d hdiag.1.symm hd hf.cd hf.da
        (D.reach_two 0 q.isLt p.isLt ((e.adjacency r q).mpr hcb)
          ((e.adjacency q p).mpr hba))
      · intro v
        simp only [Subgraph.verts_sup, Set.mem_union, hf.verts]
        aesop
      · intro u v
        simp only [Subgraph.sup_adj, hf.adjacency]
        aesop
  · by_cases hd : d ∈ H.verts
    · obtain ⟨s,rfl⟩ := e.exists_label hd
      have hs := e.mem s
      have hda : H.Adj (e.vertices s) (e.vertices p) := by
        rcases old_vertex_cycle_has_old_edge (hmin _ hs) (hmax _)
          hf.cd.symm hf.da hdiag.1.symm with hdc | hda
        · exact False.elim (hc hdc.snd_mem)
        · exact hda
      have had := hda.symm
      apply realize_one e hmin hmax q s c hdiag.2 hc hf.bc hf.cd
        (D.reach_two 0 p.isLt s.isLt ((e.adjacency q p).mpr hba)
          ((e.adjacency p s).mpr had))
      · intro v
        simp only [Subgraph.verts_sup, Set.mem_union, hf.verts]
        aesop
      · intro u v
        simp only [Subgraph.sup_adj, hf.adjacency]
        aesop
    · apply realize_two e hmin hmax q p c d hab.ne.symm hc hd hf.cd.ne
        hf.bc hf.da (D.reach_adj 0 p.isLt ((e.adjacency q p).mpr hba))
      · intro v
        simp only [Subgraph.verts_sup, Set.mem_union, hf.verts]
        aesop
      · intro u v
        simp only [Subgraph.sup_adj, hf.adjacency]
        aesop

end ZombieMain
