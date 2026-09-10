import ZombieMain.ShortCycles

namespace ZombieMain
open SimpleGraph
variable {V : Type*}

/-- The spanning graph consisting of precisely the edges that lie on an
actual triangle or quadrilateral of the original graph. -/
def shortGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj := ShortEdge G
  symm := ⟨fun a b h => by
    obtain ⟨C,hC,hab⟩ := shortEdge_exists_cycle h
    exact hC.shortEdge hab.symm⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

theorem shortGraph_le (G : SimpleGraph V) : shortGraph G ≤ G := fun _ _ h => h.1

theorem cycle_edges_short {G : SimpleGraph V} {a : V} (p : G.Walk a a)
    (hp : p.IsCycle) (hlen : p.length ≤ 4) :
    ∀ e ∈ p.edges, e ∈ (shortGraph G).edgeSet := by
  have hC : IsShortCycle p.toSubgraph := ⟨a,p,hp,hlen,rfl⟩
  intro e
  induction e using Sym2.inductionOn with
  | hf u v =>
    intro he
    have hadj : p.toSubgraph.Adj u v := p.mem_edges_toSubgraph.mpr he
    exact hC.shortEdge hadj

/-- Removing clean edges preserves every constituent short cycle. -/
theorem shortGraph_edge_cycle {G : SimpleGraph V} {u v : V}
    (h : (shortGraph G).Adj u v) :
    ∃ C : (shortGraph G).Subgraph, IsShortCycle C ∧ C.Adj u v := by
  obtain ⟨C,hC,hCu⟩ := shortEdge_exists_cycle h
  obtain ⟨a,p,hp,hlen,rfl⟩ := hC
  let q := p.transfer (shortGraph G) (cycle_edges_short p hp hlen)
  have hq : q.IsCycle := hp.transfer _
  have hlenq : q.length ≤ 4 := by simpa [q] using hlen
  refine ⟨q.toSubgraph,⟨a,q,hq,hlenq,rfl⟩,?_⟩
  have he : s(u,v) ∈ p.edges := p.mem_edges_toSubgraph.mp hCu
  change s(u,v) ∈ q.toSubgraph.edgeSet
  apply q.mem_edges_toSubgraph.mpr
  simpa [q] using he

end ZombieMain
