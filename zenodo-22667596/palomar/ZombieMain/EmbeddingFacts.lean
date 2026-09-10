import ZombieMain.Diagram
import ZombieMain.CycleCapacity

namespace ZombieMain
open SimpleGraph

namespace Diagram.Embedding
variable {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} {D : Diagram}

theorem mem (e : D.Embedding H) (u : Fin D.order) : e.vertices u ∈ H.verts := by
  rw [← e.range_eq]
  exact Set.mem_range_self u

theorem exists_label (e : D.Embedding H) {v : V} (hv : v ∈ H.verts) :
    ∃ u, e.vertices u = v := by
  rw [← e.range_eq] at hv
  exact hv

theorem vertex_count (e : D.Embedding H) : H.verts.ncard = D.order := by
  rw [← e.range_eq, Set.ncard_range_of_injective e.injective]
  simp

/-- An exact diagram copy preserves degrees, including the distinction
between the degree-two ports and saturated internal vertices. -/
theorem degree (e : D.Embedding H) (u : Fin D.order) :
    D.degree u.val = (H.neighborSet (e.vertices u)).ncard := by
  classical
  let neighbors := Finset.univ.filter (fun w : Fin D.order => D.adj u.val w.val)
  have hset : (↑(neighbors.image e.vertices) : Set V) = H.neighborSet (e.vertices u) := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have ha : D.adj u.val w.val = true := (Finset.mem_filter.mp hw).2
      exact (e.adjacency u w).mp ha
    · intro hv
      have ha : H.Adj (e.vertices u) v := hv
      obtain ⟨w,rfl⟩ := e.exists_label ha.snd_mem
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.adjacency u w).mpr ha⟩, rfl⟩
  rw [← hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ e.injective]
  rfl

end Diagram.Embedding

theorem CycleGenerated.minimum_degree [Fintype V] {G : SimpleGraph V}
    {H : G.Subgraph} (hH : CycleGenerated G H) {v : V} (hv : v ∈ H.verts) :
    2 ≤ (H.neighborSet v).ncard := by
  obtain ⟨C,hC,hCH,hvC⟩ := hH.vertex_cycle hv
  rw [← hC.neighbor_card hvC]
  exact Set.ncard_le_ncard (fun _ hw => hCH.2 hw)

end ZombieMain
