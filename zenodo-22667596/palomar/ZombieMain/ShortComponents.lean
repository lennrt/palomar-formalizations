import ZombieMain.ShortGraph
import ZombieMain.Classification

namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- A connected component of the short-edge graph, viewed as a subgraph
of the original graph. Clean edges with both endpoints here are excluded. -/
def shortComponent (G : SimpleGraph V) (K : (shortGraph G).ConnectedComponent) :
    G.Subgraph where
  verts := K.supp
  Adj u v := u ∈ K.supp ∧ ShortEdge G u v
  adj_sub h := h.2.1
  edge_vert h := h.1
  symm := ⟨fun u v h => ⟨K.mem_supp_of_adj_mem_supp h.1 h.2,
    (shortGraph G).adj_symm h.2⟩⟩

theorem component_shortEdge (K : (shortGraph G).ConnectedComponent)
    {u v : K} (h : K.toSimpleGraph.Adj u v) : ShortEdge K.toSimpleGraph u v := by
  have hQ : ShortEdge (shortGraph G) u.val v.val := by
    obtain ⟨C,hC,hCv⟩ := shortGraph_edge_cycle h
    exact hC.shortEdge hCv
  refine ⟨h,?_⟩
  rcases hQ.2 with ⟨c,hvc,hcu⟩ | ⟨c,d,huc,hvd,hvc,hcd,hdu⟩
  · have hc : c ∈ K.supp := K.mem_supp_of_adj_mem_supp v.property hvc
    exact Or.inl ⟨⟨c,hc⟩,hvc,hcu⟩
  · have hc : c ∈ K.supp := K.mem_supp_of_adj_mem_supp v.property hvc
    have hd : d ∈ K.supp := K.mem_supp_of_adj_mem_supp hc hcd
    exact Or.inr ⟨⟨c,hc⟩,⟨d,hd⟩,fun hh => huc (congrArg Subtype.val hh),
      fun hh => hvd (congrArg Subtype.val hh),hvc,hcd,hdu⟩

theorem ShortEdge.degree_lower [Fintype V] [DecidableRel G.Adj] {u v : V}
    (h : ShortEdge G u v) : 2 ≤ G.degree u := by
  classical
  obtain ⟨C,hC,hCu⟩ := shortEdge_exists_cycle h
  have hn := hC.neighbor_card hCu.fst_mem
  have hb := Set.ncard_le_ncard (C.neighborSet_subset u)
  rw [hn, ← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree u] at hb
  exact hb

def Diagram.Embedding.toShortComponent (K : (shortGraph G).ConnectedComponent)
    {D : Diagram} (e : D.Embedding (⊤ : K.toSimpleGraph.Subgraph)) :
    D.Embedding (shortComponent G K) := by
  refine ⟨fun u => (e.vertices u).val,
    Subtype.val_injective.comp e.injective,?_,?_⟩
  · ext v
    constructor
    · rintro ⟨u,rfl⟩
      exact (e.vertices u).property
    · intro hv
      obtain ⟨u,hu⟩ := e.exists_label (v := ⟨v,hv⟩) (by trivial)
      exact ⟨u,congrArg Subtype.val hu⟩
  · intro u v
    rw [e.adjacency]
    change K.toSimpleGraph.Adj (e.vertices u) (e.vertices v) ↔
      (e.vertices u).val ∈ K.supp ∧ ShortEdge G (e.vertices u).val (e.vertices v).val
    exact ⟨fun h => ⟨(e.vertices u).property,h⟩,fun h => h.2⟩

/-- Every nontrivial actual short-edge component belongs to the universal
catalogue, with its original vertex labels and reflected adjacency. -/
theorem shortComponent_classified [Fintype V] [DecidableRel G.Adj]
    (hmax : ∀ v, G.degree v ≤ 3) (K : (shortGraph G).ConnectedComponent)
    [Nontrivial K] : ClassifiedSubgraph (shortComponent G K) := by
  classical
  have hminK : ∀ v : K, 2 ≤ K.toSimpleGraph.degree v := by
    intro v
    obtain ⟨w,hvw⟩ := K.connected_toSimpleGraph.preconnected.exists_adj_of_nontrivial v
    exact (component_shortEdge K hvw).degree_lower
  have hmaxK : ∀ v : K, K.toSimpleGraph.degree v ≤ 3 := by
    intro v
    have h1 : K.toSimpleGraph.degree v ≤ G.degree v.val := by
      rw [← K.toSimpleGraph.card_neighborSet_eq_degree v, ← G.card_neighborSet_eq_degree v.val]
      let f : K.toSimpleGraph.neighborSet v → G.neighborSet v.val :=
        fun w => ⟨w.val.val, (show ShortEdge G v.val w.val.val from w.property).1⟩
      apply Fintype.card_le_of_injective f
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun w : G.neighborSet v.val => w.val) hab
    exact h1.trans (hmax v.val)
  have hc := cycle_union_classification K.connected_toSimpleGraph hminK hmaxK
    (fun _ _ h => shortEdge_exists_cycle (component_shortEdge K h))
  rcases hc with hp | ⟨f,hf,⟨e⟩⟩
  · let e := canonicalEmbedding (⊤ : K.toSimpleGraph.Subgraph)
    have hd : (canonicalDiagram (⊤ : K.toSimpleGraph.Subgraph)).Classified :=
      Or.inl (e.port_count.trans hp)
    exact (e.toShortComponent K).classified hd
  · exact Or.inr ⟨f,hf,⟨e.toShortComponent K⟩⟩

end ZombieMain
