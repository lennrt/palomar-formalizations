import ZombieMain.UniversalRouting

namespace ZombieMain
open SimpleGraph ZombieDamage
variable {V : Type} {G : SimpleGraph V}

/-- The simple component quotient after deleting one specified original edge.
Parallel original edges remain available as witnesses; loops are irrelevant
for travel between components and remain covered by local routing. -/
def componentQuotient (G : SimpleGraph V) (avoid : Sym2 V) :
    SimpleGraph (shortGraph G).ConnectedComponent where
  Adj K L := K≠L ∧ ∃ u v,u∈K.supp ∧ v∈L.supp ∧ G.Adj u v ∧ s(u,v)≠avoid
  symm := ⟨by
    rintro K L ⟨hne,u,v,hu,hv,huv,ha⟩
    exact ⟨Ne.symm hne,v,u,hv,hu,huv.symm,by simpa only [Sym2.eq_swap] using ha⟩⟩
  loopless := ⟨fun K h => h.1 rfl⟩

theorem different_components_clean (K L : (shortGraph G).ConnectedComponent)
    (hne : K≠L) {u v : V} (hu : u∈K.supp) (hv : v∈L.supp) (ha : G.Adj u v) :
    (gameGraph G).Clean u v := by
  classical
  by_contra hn
  have hs := (shortEdge_iff_gameShort G u v).mpr ⟨ha,hn⟩
  have hvK := K.mem_supp_of_adj_mem_supp hu hs
  exact hne ((K.mem_supp_iff v).mp hvK |>.symm.trans ((L.mem_supp_iff v).mp hv))

theorem quotient_reachable (avoid : Sym2 V) {u v : V}
    (p : (G.deleteEdges {avoid}).Walk u v) :
    (componentQuotient G avoid).Reachable
      ((shortGraph G).connectedComponentMk u) ((shortGraph G).connectedComponentMk v) := by
  classical
  induction p with
  | nil => exact .refl _
  | @cons u w v huw tail ih =>
    apply Reachable.trans (v := (shortGraph G).connectedComponentMk w) _ ih
    by_cases he : (shortGraph G).connectedComponentMk u=(shortGraph G).connectedComponentMk w
    · exact he ▸ Reachable.refl _
    · apply Adj.reachable
      refine ⟨he,u,w,rfl,rfl,huw.1,?_⟩
      intro ha
      exact huw.2 (by simpa [ha] using huw.1.ne)

theorem quotient_path (hconn : G.Connected) (z p x : V)
    (hn : ¬G.IsBridge s(z,p)) :
    ∃ Q : (componentQuotient G s(z,p)).Walk
      ((shortGraph G).connectedComponentMk p) ((shortGraph G).connectedComponentMk x),Q.IsPath := by
  have hc := hconn.connected_delete_edge_of_not_isBridge hn
  obtain ⟨w⟩ := hc.preconnected p x
  exact (quotient_reachable s(z,p) w).exists_isPath

end ZombieMain
