import ZombieMain.ShortComponents
import ZombieMain.BridgePorts

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem shortComponent_min_degree (K : (shortGraph G).ConnectedComponent)
    [Nontrivial K] :
    ∀ v ∈ (shortComponent G K).verts,
      2 ≤ ((shortComponent G K).neighborSet v).ncard := by
  classical
  intro v hv
  obtain ⟨w,hvw⟩ := K.connected_toSimpleGraph.preconnected.exists_adj_of_nontrivial ⟨v,hv⟩
  have hQ : (shortGraph G).Adj v w.val := hvw
  obtain ⟨C,hC,hCv⟩ := shortGraph_edge_cycle hQ
  have hd := (hC.shortEdge hCv).degree_lower
  have he : (shortComponent G K).neighborSet v = (shortGraph G).neighborSet v := by
    ext w
    change (v ∈ K.supp ∧ ShortEdge G v w) ↔ ShortEdge G v w
    exact and_iff_right hv
  rw [he, ← Set.fintypeCard_eq_ncard, (shortGraph G).card_neighborSet_eq_degree v]
  exact hd

/-- Bridgelessness excludes the unspecified one-port class for every
nontrivial component of the actual short-edge graph. -/
theorem shortComponent_catalogue [DecidableRel G.Adj]
    (hcubic : ∀ v, G.degree v = 3)
    (hbridge : ∀ v w, G.Adj v w → ¬ G.IsBridge s(v,w))
    (K : (shortGraph G).ConnectedComponent) [Nontrivial K] :
    ∃ f : Family, f.Admissible ∧ Nonempty (f.diagram.Embedding (shortComponent G K)) := by
  have hmax : ∀ v, G.degree v ≤ 3 := fun v => (hcubic v).le
  obtain hp | hf := shortComponent_classified hmax K
  · exact False.elim (no_one_port_in_bridgeless (shortComponent_min_degree K) hcubic hbridge hp)
  · exact hf

end ZombieMain

namespace ZombieMain
open SimpleGraph
variable {V : Type} {G : SimpleGraph V}

/-- Every original edge at an internal vertex which is absent from the
short component is clean, even when its other endpoint is internal too. -/
theorem shortComponent_missing_clean (K : (shortGraph G).ConnectedComponent)
    {u v : V} (hu : u ∈ K.supp) (hG : G.Adj u v)
    (hH : ¬ (shortComponent G K).Adj u v) : (gameGraph G).Clean u v := by
  classical
  by_contra hn
  have hshort := (shortEdge_iff_gameShort G u v).mpr ⟨hG,hn⟩
  exact hH ⟨hu,hshort⟩

theorem shortComponent_clean_missing (K : (shortGraph G).ConnectedComponent)
    {u v : V} (h : (gameGraph G).Clean u v) :
    ¬ (shortComponent G K).Adj u v := by
  intro hH
  exact ((shortEdge_iff_gameShort G u v).mp hH.2).2 h

end ZombieMain
