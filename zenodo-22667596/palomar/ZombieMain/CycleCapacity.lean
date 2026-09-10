import ZombieMain.CycleUnion
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

omit [Fintype V] in
theorem IsShortCycle.neighbor_card {C : G.Subgraph} (hC : IsShortCycle C)
    {v : V} (hv : v ∈ C.verts) : (C.neighborSet v).ncard = 2 := by
  obtain ⟨u, p, hp, _, rfl⟩ := hC
  exact hp.ncard_neighborSet_toSubgraph_eq_two (p.mem_verts_toSubgraph.mp hv)

theorem subgraph_degree_ncard (C : G.Subgraph) (v : V) :
    letI : DecidableRel C.spanningCoe.Adj := Classical.decRel _
    C.spanningCoe.degree v = (C.neighborSet v).ncard := by
  classical
  rw [← C.spanningCoe.card_neighborSet_eq_degree v, Set.fintypeCard_eq_ncard]
  rfl

theorem subgraph_incidence_ncard (C : G.Subgraph) (v : V) :
    (C.spanningCoe.incidenceSet v).ncard = (C.neighborSet v).ncard := by
  classical
  rw [← Set.fintypeCard_eq_ncard, C.spanningCoe.card_incidenceSet_eq_degree]
  exact subgraph_degree_ncard C v

theorem IsShortCycle.counts {C : G.Subgraph} (hC : IsShortCycle C) :
    C.verts.ncard = C.edgeSet.ncard ∧ C.verts.ncard ≤ 4 := by
  classical
  have hdeg : ∀ v, C.spanningCoe.degree v = if v ∈ C.verts then 2 else 0 := by
    intro v
    by_cases hv : v ∈ C.verts
    · rw [subgraph_degree_ncard, if_pos hv]
      exact hC.neighbor_card hv
    · rw [Subgraph.degree_spanningCoe, C.degree_of_notMem_verts hv, if_neg hv]
  have hsum := C.spanningCoe.sum_degrees_eq_twice_card_edges
  simp_rw [hdeg] at hsum
  have hsum' : 2 * C.verts.ncard = 2 * C.edgeSet.ncard := by
    simpa [Finset.sum_ite, Set.ncard_eq_toFinset_card',
      edgeFinset, Subgraph.edgeSet_spanningCoe, Finset.mul_sum, mul_comm] using hsum
  have hcard : C.verts.ncard = C.edgeSet.ncard := by omega
  refine ⟨hcard, ?_⟩
  obtain ⟨u, p, hp, hlen, rfl⟩ := hC
  have hset : p.toSubgraph.edgeSet = (p.edges.toFinset : Set (Sym2 V)) := by
    ext e
    simp
  rw [hcard, hset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup hp.isTrail.edges_nodup, Walk.length_edges]
  exact hlen

omit [Fintype V] in
/-- An edge touching a newly added vertex was not an edge of the old union. -/
theorem new_vertex_incidence_subset (H C : G.Subgraph) {v : V}
    (hv : v ∈ C.verts \ H.verts) :
    C.spanningCoe.incidenceSet v ⊆ C.edgeSet \ H.edgeSet := by
  intro e he
  refine ⟨he.1, ?_⟩
  intro heH
  exact hv.2 (H.mem_verts_of_mem_edge heH he.2)

/-- Adjoining a short cycle sharing an edge adds at most two vertices, and
adds enough new edges that unused cubic degree capacity cannot increase. -/
theorem shortCycle_attachment_density (H C : G.Subgraph) (hC : IsShortCycle C)
    (hshare : ∃ u v, H.Adj u v ∧ C.Adj u v) :
    3 * (C.verts \ H.verts).ncard ≤ 2 * (C.edgeSet \ H.edgeSet).ncard := by
  classical
  obtain ⟨u, v, huvH, huvC⟩ := hshare
  have hpair : ({u, v} : Set V) ⊆ C.verts ∩ H.verts := by
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨huvC.fst_mem, huvH.fst_mem⟩
    · rcases hx with rfl
      exact ⟨huvC.snd_mem, huvH.snd_mem⟩
  have hi : 2 ≤ (C.verts ∩ H.verts).ncard := by
    simpa [Set.ncard_pair huvH.ne] using Set.ncard_le_ncard hpair
  have hsplit := Set.ncard_sdiff_add_ncard_of_subset
    (Set.inter_subset_left : C.verts ∩ H.verts ⊆ C.verts)
  have heq : C.verts \ (C.verts ∩ H.verts) = C.verts \ H.verts := by ext x; simp
  rw [heq] at hsplit
  have hcv := hC.counts.2
  have hn : (C.verts \ H.verts).ncard ≤ 2 := by omega
  interval_cases hn' : (C.verts \ H.verts).ncard
  · omega
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.mp hn'
    have hav : a ∈ C.verts \ H.verts := by rw [ha]; simp
    have hiA := Set.ncard_le_ncard (new_vertex_incidence_subset H C hav)
    rw [subgraph_incidence_ncard, hC.neighbor_card hav.1] at hiA
    omega
  · obtain ⟨a, b, hab, habset⟩ := Set.ncard_eq_two.mp hn'
    have ha : a ∈ C.verts \ H.verts := by rw [habset]; simp
    have hb : b ∈ C.verts \ H.verts := by rw [habset]; simp
    have hA : (C.spanningCoe.incidenceSet a).ncard = 2 :=
      (subgraph_incidence_ncard C a).trans (hC.neighbor_card ha.1)
    have hB : (C.spanningCoe.incidenceSet b).ncard = 2 :=
      (subgraph_incidence_ncard C b).trans (hC.neighbor_card hb.1)
    have hI : (C.spanningCoe.incidenceSet a ∩ C.spanningCoe.incidenceSet b).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard (C.spanningCoe.incidenceSet_inter_incidenceSet_subset hab)
    have hU := Set.ncard_union_add_ncard_inter
      (C.spanningCoe.incidenceSet a) (C.spanningCoe.incidenceSet b)
    have hN := Set.ncard_le_ncard (Set.union_subset
      (new_vertex_incidence_subset H C ha) (new_vertex_incidence_subset H C hb))
    omega

/-- The four-port incidence inequality for an arbitrary edge-sharing union.
This is an induction over actual short cycles, with no finite-size cutoff. -/
theorem CycleGenerated.capacity_bound {H : G.Subgraph} (hH : CycleGenerated G H) :
    3 * H.verts.ncard ≤ 2 * H.edgeSet.ncard + 4 := by
  induction hH with
  | base hC =>
    obtain ⟨hcard, hfour⟩ := hC.counts
    omega
  | @attach H C hH hC hshare ih =>
    have hd := shortCycle_attachment_density H C hC hshare
    have hv := Set.ncard_sdiff_add_ncard C.verts H.verts
    have he := Set.ncard_sdiff_add_ncard C.edgeSet H.edgeSet
    simp only [Subgraph.verts_sup, Subgraph.edgeSet_sup]
    rw [Set.union_comm H.verts C.verts, Set.union_comm H.edgeSet C.edgeSet]
    omega

/-- The paper's four-port principle, stated for every finite simple connected
graph of minimum degree two and maximum degree three whose edges lie on
actual triangles or quadrilaterals. -/
theorem four_port_principle [DecidableRel G.Adj]
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hshort : ∀ u v, G.Adj u v → ∃ C : G.Subgraph,
      IsShortCycle C ∧ C.Adj u v) :
    (∑ v, (3 - G.degree v)) ≤ 4 ∧
      (Finset.univ.filter (fun v => G.degree v = 2)).card ≤ 4 := by
  classical
  have hedge : ∃ u v, G.Adj u v := by
    obtain ⟨u⟩ := hconn.nonempty
    have hpos : 0 < (G.neighborFinset u).card := by
      change 0 < G.degree u
      exact lt_of_lt_of_le (by decide : 0 < 2) (hmin u)
    obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
    exact ⟨u, v, (G.mem_neighborFinset u v).mp hv⟩
  have hcap := (cycleGenerated_top hconn hmax hedge hshort).capacity_bound
  have hcap' : 3 * Fintype.card V ≤ 2 * G.edgeFinset.card + 4 := by
    simpa [Set.ncard_eq_toFinset_card', edgeFinset] using hcap
  have hsum : (∑ v, (3 - G.degree v)) + ∑ v, G.degree v = 3 * Fintype.card V := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ v, (3 - G.degree v + G.degree v) = ∑ _v : V, 3 :=
        Finset.sum_congr rfl (fun v _ => Nat.sub_add_cancel (hmax v))
      _ = _ := by simp [mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges] at hsum
  have hbound : (∑ v, (3 - G.degree v)) ≤ 4 := by omega
  refine ⟨hbound, ?_⟩
  have hp : ∀ v, (if G.degree v = 2 then 1 else 0) = 3 - G.degree v := by
    intro v
    have hlow := hmin v
    have hhigh := hmax v
    split <;> omega
  have hports : (Finset.univ.filter (fun v => G.degree v = 2)).card =
      ∑ v, (3 - G.degree v) := by
    have hx : (∑ v, if G.degree v = 2 then (1 : ℕ) else 0) =
        (Finset.univ.filter (fun v => G.degree v = 2)).card := by simp
    rw [← hx]
    exact Finset.sum_congr rfl (fun v _ => hp v)
  omega

end ZombieMain
