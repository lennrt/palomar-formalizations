import ZombieMain.PortTransport
import ZombieMain.AttachmentCapacity

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : G.Subgraph}

/-- A degree-two port in a cubic graph has exactly one additional neighbor.
That neighbor may belong to the same short-edge component. -/
theorem port_neighbor_unique {v : V} (hH : (H.neighborSet v).ncard = 2)
    (hG : G.degree v = 3) : ∃! w, G.Adj v w ∧ ¬ H.Adj v w := by
  classical
  have hsub : H.neighborSet v ⊆ G.neighborSet v := fun _ h => h.adj_sub
  have hcount := Set.ncard_sdiff_add_ncard_of_subset hsub
  have hcard : (G.neighborSet v).ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard, G.card_neighborSet_eq_degree v, hG]
  rw [hH,hcard] at hcount
  have hpos : 0 < (G.neighborSet v \ H.neighborSet v).ncard := by omega
  obtain ⟨w,hwG,hwH⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
  refine ⟨w,⟨hwG,hwH⟩,?_⟩
  intro u hu
  exact new_neighbors_subsingleton (by omega) (by omega) hu ⟨hwG,hwH⟩

/-- A one-port subgraph of minimum degree two in a cubic graph forces an
actual bridge. No connectivity or catalogue assumption is needed. -/
theorem one_port_forces_bridge
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hcubic : ∀ v, G.degree v = 3) (hport : (portVertices H).ncard = 1) :
    ∃ v w, G.Adj v w ∧ G.IsBridge s(v,w) := by
  classical
  obtain ⟨v,hset⟩ := Set.ncard_eq_one.mp hport
  have hv : v ∈ portVertices H := by rw [hset]; simp
  have hunique : ∀ a, a ∈ H.verts → (H.neighborSet a).ncard = 2 → a=v := by
    intro a ha hd
    have hp : a ∈ portVertices H := ⟨ha,hd⟩
    simpa [hset] using hp
  obtain ⟨w,⟨hvw,hnvw⟩,hwunique⟩ := port_neighbor_unique hv.2 (hcubic v)
  have hw : w ∉ H.verts := by
    intro hw
    have hd := new_edge_endpoint_degree (hmin w hw) (by rw [hcubic])
      hvw.symm (fun h => hnvw h.symm)
    have heq := hunique w hw hd
    exact hvw.ne heq.symm
  have hclosed : ∀ a b, a ∈ H.verts → (G.deleteEdges {s(v,w)}).Adj a b → b ∈ H.verts := by
    intro a b ha hab
    by_contra hb
    have hnab : ¬ H.Adj a b := fun h => hb h.snd_mem
    have hd := new_edge_endpoint_degree (hmin a ha) (by rw [hcubic]) hab.1 hnab
    have hav := hunique a ha hd
    subst a
    have hbw := hwunique b ⟨hab.1,hnab⟩
    subst b
    exact hab.2 (by simp [hvw.ne])
  refine ⟨v,w,hvw,?_⟩
  rw [SimpleGraph.isBridge_iff]
  rintro ⟨p⟩
  have propagate : ∀ {a b : V}, (G.deleteEdges {s(v,w)}).Walk a b →
      a ∈ H.verts → b ∈ H.verts := by
    intro a b p
    induction p with
    | nil => exact id
    | cons hab tail ih => exact fun ha => ih (hclosed _ _ ha hab)
  exact hw (propagate p hv.1)

theorem no_one_port_in_bridgeless
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hcubic : ∀ v, G.degree v = 3)
    (hbridge : ∀ v w, G.Adj v w → ¬ G.IsBridge s(v,w)) :
    (portVertices H).ncard ≠ 1 := by
  intro hp
  obtain ⟨v,w,hvw,hb⟩ := one_port_forces_bridge hmin hcubic hp
  exact hbridge v w hvw hb

end ZombieMain
