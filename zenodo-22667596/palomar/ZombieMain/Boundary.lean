import ZombieMain.ComponentPorts
import ZombieMain.BoundaryDefinitions

namespace ZombieMain
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem subgraph_port_bound (H : G.Subgraph) (hconn : H.coe.Connected)
    (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard) (hmax : ∀v,G.degree v≤3)
    (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v) :
    (portVertices H).ncard≤4 := by
  classical
  have hdeg : ∀v : H.verts,H.coe.degree v=(H.neighborSet v.val).ncard := by
    intro v
    rw [H.coe_degree,Subgraph.degree,Set.fintypeCard_eq_ncard]
  have hf := (four_port_principle hconn (fun v => by
    rw [H.coe_degree,Subgraph.degree,Set.fintypeCard_eq_ncard]
    exact hmin _ v.property)
    (fun v => by rw [H.coe_degree]; exact (H.degree_le v.val).trans (hmax v.val)) hshort).2
  have hset : Subtype.val '' {v : H.verts | H.coe.degree v=2}=portVertices H := by
    ext v
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.property,(hdeg w).symm.trans hw⟩
    · rintro ⟨hv,hd⟩
      exact ⟨⟨v,hv⟩,(hdeg ⟨v,hv⟩).trans hd,rfl⟩
  rw [← hset,Set.ncard_image_of_injective _ Subtype.val_injective]
  simpa [Set.ncard_eq_toFinset_card'] using hf

theorem cut_bound_by_ports (H : G.Subgraph)
    (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard) (hmax : ∀v,G.degree v≤3) :
    (cutPairs G H.verts).ncard≤(portVertices H).ncard := by
  classical
  have himage : Prod.fst '' cutPairs G H.verts ⊆ portVertices H := by
    rintro v ⟨⟨u,w⟩,⟨hu,hw,ha⟩,rfl⟩
    exact ⟨hu,new_edge_endpoint_degree (hmin u hu) (hmax u) ha (fun h => hw h.snd_mem)⟩
  have hinj : Set.InjOn Prod.fst (cutPairs G H.verts) := by
    rintro ⟨u,v⟩ ⟨hu,hv,huv⟩ ⟨w,x⟩ ⟨hw,hx,hwx⟩ he
    change u=w at he
    subst w
    have hvx := new_neighbors_subsingleton (hmin u hu) (hmax u)
      ⟨huv,fun h => hv h.snd_mem⟩ ⟨hwx,fun h => hx h.snd_mem⟩
    exact Prod.ext rfl hvx
  calc
    (cutPairs G H.verts).ncard = (Prod.fst '' cutPairs G H.verts).ncard :=
      (Set.ncard_image_of_injOn hinj).symm
    _ ≤ (portVertices H).ncard := Set.ncard_le_ncard himage

/-- The exterior-edge clause of the four-port theorem, in every subcubic
supergraph, without any assumption that the subgraph is induced. -/
theorem four_boundary_edges (H : G.Subgraph) (hconn : H.coe.Connected)
    (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard) (hmax : ∀v,G.degree v≤3)
    (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v) :
    (cutPairs G H.verts).ncard≤4 :=
  (cut_bound_by_ports H hmin hmax).trans (subgraph_port_bound H hconn hmin hmax hshort)

end ZombieMain
