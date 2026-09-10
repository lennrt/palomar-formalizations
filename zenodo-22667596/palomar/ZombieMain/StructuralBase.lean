import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic

namespace ZombieStructure

/-- Two pairs of neighbors at a subcubic vertex share a neighbor. This is the
local fact upgrading vertex intersections of cycles to edge intersections. -/
theorem two_pairs_intersect {V : Type*} [DecidableEq V]
    (neighbors A B : Finset V) (hA : A ⊆ neighbors) (hB : B ⊆ neighbors)
    (hc : neighbors.card ≤ 3) (ha : A.card = 2) (hb : B.card = 2) :
    (A ∩ B).Nonempty := by
  have hU : (A ∪ B).card ≤ 3 :=
    (Finset.card_le_card (Finset.union_subset hA hB)).trans hc
  have hi := Finset.card_union_add_card_inter A B
  apply Finset.card_pos.mp
  omega

/-- Complete finite incidence calculation for a triangle meeting the old
union in an edge. An old edge has two old endpoints. -/
theorem triangle_attachment_density :
    ∀ oldV oldE : Fin 3 → Bool,
      (∀ i, oldE i = true → oldV i = true ∧ oldV (i+1) = true) →
      (∃ i, oldE i = true) →
      3 * (Finset.univ.filter (fun i => oldV i = false)).card ≤
        2 * (Finset.univ.filter (fun i => oldE i = false)).card := by decide

/-- The same exhaustive incidence calculation for a quadrilateral. This
finite lemma is independent of ambient graph order and labels. -/
theorem square_attachment_density :
    ∀ oldV oldE : Fin 4 → Bool,
      (∀ i, oldE i = true → oldV i = true ∧ oldV (i+1) = true) →
      (∃ i, oldE i = true) →
      3 * (Finset.univ.filter (fun i => oldV i = false)).card ≤
        2 * (Finset.univ.filter (fun i => oldE i = false)).card := by decide

section Graphs
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Vertex-intersecting cycles in a subcubic graph share an incident edge.
No bound on either cycle's length is needed for this local statement. -/
theorem cycles_share_edge [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) {a b v : V}
    (p : G.Walk a a) (q : G.Walk b b) (hp : p.IsCycle) (hq : q.IsCycle)
    (hvp : v ∈ p.support) (hvq : v ∈ q.support) :
    ∃ w, p.toSubgraph.Adj v w ∧ q.toSubgraph.Adj v w := by
  classical
  let A : Finset V := Finset.univ.filter (p.toSubgraph.Adj v)
  let B : Finset V := Finset.univ.filter (q.toSubgraph.Adj v)
  have hA : A ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr (p.toSubgraph.adj_sub (by simpa [A] using hw))
  have hB : B ⊆ G.neighborFinset v := by
    intro w hw
    exact (G.mem_neighborFinset v w).mpr (q.toSubgraph.adj_sub (by simpa [B] using hw))
  have ha : A.card=2 := by
    have hs : (A : Set V)=p.toSubgraph.neighborSet v := by ext w; simp [A]
    have hn := hp.ncard_neighborSet_toSubgraph_eq_two hvp
    rw [← hs, Set.ncard_coe_finset] at hn
    exact hn
  have hb : B.card=2 := by
    have hs : (B : Set V)=q.toSubgraph.neighborSet v := by ext w; simp [B]
    have hn := hq.ncard_neighborSet_toSubgraph_eq_two hvq
    rw [← hs, Set.ncard_coe_finset] at hn
    exact hn
  obtain ⟨w, hw⟩ := two_pairs_intersect (G.neighborFinset v) A B hA hB (hdeg v) ha hb
  refine ⟨w, ?_, ?_⟩
  · simpa [A] using (Finset.mem_inter.mp hw).1
  · simpa [B] using (Finset.mem_inter.mp hw).2

end Graphs
end ZombieStructure
