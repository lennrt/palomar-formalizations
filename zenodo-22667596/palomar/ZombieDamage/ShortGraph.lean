import ZombieDamage.Graph

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

theorem clean_symm {u v : V} (h : G.Clean u v) : G.Clean v u := by
  refine ⟨G.symm h.1,?_,?_⟩
  · intro c hc
    exact h.2.1 c ⟨G.symm hc.2,G.symm hc.1⟩
  · intro c d hvc hud hpath
    exact h.2.2 d c hud hvc ⟨G.symm hpath.2.2,G.symm hpath.2.1,G.symm hpath.1⟩

theorem short_symm {u v : V} (h : G.ShortAdj u v) : G.ShortAdj v u :=
  ⟨G.symm h.1,fun hc => h.2 (G.clean_symm hc)⟩

theorem twoApart_symm {u v : V} (h : G.TwoApart u v) : G.TwoApart v u := by
  obtain ⟨hne,hno,x,hux,hxv⟩ := h
  exact ⟨hne.symm,fun hvu => hno (G.symm hvu),x,G.symm hxv,G.symm hux⟩

theorem clean_first_twoApart {u v w : V} (hc : G.Clean u v)
    (hvw : G.adj v w) (hne : u ≠ w) : G.TwoApart u w :=
  G.twoApart_symm (G.cleanEdge_twoApart (G.clean_symm hc) (G.symm hvw) hne.symm)

theorem clean_first_reply {u v w x : V} (hc : G.Clean u v)
    (hvw : G.adj v w) (hne : u ≠ w)
    (h : G.GeodesicReply u w x) : x=v := by
  have ht := G.clean_first_twoApart hc hvw hne
  obtain ⟨hux,hxw⟩ := (G.geodesicReply_iff_commonNeighbor ht).1 h
  have hback := (G.geodesicReply_iff_commonNeighbor (G.twoApart_symm ht)).2
    ⟨G.symm hxw,G.symm hux⟩
  exact (G.cleanEdge_forces_reply (G.clean_symm hc) (G.symm hvw) hne.symm).1 hback

def shortGraph : Graph V where
  adj := G.ShortAdj
  symm := G.short_symm
  loopless := fun v h => G.loopless v h.1

end ZombieDamage.Graph
