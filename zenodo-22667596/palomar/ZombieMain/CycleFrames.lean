import ZombieMain.ShortCycles

namespace ZombieMain
open SimpleGraph
set_option maxHeartbeats 1000000
variable {V : Type*} {G : SimpleGraph V}

structure TriangleFrame (C : G.Subgraph) (a b c : V) : Prop where
  ab : G.Adj a b
  bc : G.Adj b c
  ca : G.Adj c a
  distinct : [a,b,c].Nodup
  exactGraph : C = (Walk.cons ab (.cons bc (.cons ca .nil))).toSubgraph

structure SquareFrame (C : G.Subgraph) (a b c d : V) : Prop where
  ab : G.Adj a b
  bc : G.Adj b c
  cd : G.Adj c d
  da : G.Adj d a
  distinct : [a,b,c,d].Nodup
  exactGraph : C = (Walk.cons ab (.cons bc (.cons cd (.cons da .nil)))).toSubgraph

/-- Every short cycle can be represented by its actual three or four
distinct vertices, starting with any specified edge. -/
theorem IsShortCycle.frame {C : G.Subgraph} (hC : IsShortCycle C)
    {a b : V} (hab : C.Adj a b) :
    (∃ c, TriangleFrame C a b c) ∨ (∃ c d, SquareFrame C a b c d) := by
  obtain ⟨p,hp,hlen,hgraph,hsnd⟩ := hC.orient hab
  have hlow := hp.three_le_length
  cases p with
  | nil => simp at hlow
  | @cons _ b' _ hab' q =>
    have hb : b' = b := by simpa using hsnd
    subst b'
    cases q with
    | nil => simp at hlow
    | @cons _ c _ hbc q =>
      cases q with
      | nil => simp at hlow
      | @cons _ d _ hcd q =>
        cases q with
        | nil =>
          refine Or.inl ⟨c, hab', hbc, hcd, ?_, hgraph.symm⟩
          simp [hab'.ne, hbc.ne, hcd.ne.symm]
        | @cons _ e _ hde q =>
          cases q with
          | nil =>
            refine Or.inr ⟨c,d,hab',hbc,hcd,hde,?_,hgraph.symm⟩
            have hn := hp.support_nodup
            simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
              List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
              not_false_eq_true, and_true, not_or] at hn ⊢
            exact ⟨⟨Ne.symm hn.1.2.2, Ne.symm hn.2.1.2, Ne.symm hn.2.2⟩,
              ⟨hn.1.1, hn.1.2.1⟩, hn.2.1.1⟩
          | cons _ _ => simp only [Walk.length_cons] at hlen; omega

theorem TriangleFrame.verts {C : G.Subgraph} {a b c : V}
    (h : TriangleFrame C a b c) {v : V} :
    v ∈ C.verts ↔ v=a ∨ v=b ∨ v=c := by
  rw [h.exactGraph, Walk.mem_verts_toSubgraph]
  simp
  tauto

theorem SquareFrame.verts {C : G.Subgraph} {a b c d : V}
    (h : SquareFrame C a b c d) {v : V} :
    v ∈ C.verts ↔ v=a ∨ v=b ∨ v=c ∨ v=d := by
  rw [h.exactGraph, Walk.mem_verts_toSubgraph]
  simp
  tauto

theorem TriangleFrame.adjacency {C : G.Subgraph} {a b c : V}
    (h : TriangleFrame C a b c) {u v : V} :
    C.Adj u v ↔ (u=a ∧ v=b) ∨ (u=b ∧ v=a) ∨
      (u=b ∧ v=c) ∨ (u=c ∧ v=b) ∨ (u=c ∧ v=a) ∨ (u=a ∧ v=c) := by
  rw [h.exactGraph]
  simp [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, eq_comm]
  tauto

theorem SquareFrame.adjacency {C : G.Subgraph} {a b c d : V}
    (h : SquareFrame C a b c d) {u v : V} :
    C.Adj u v ↔ (u=a ∧ v=b) ∨ (u=b ∧ v=a) ∨
      (u=b ∧ v=c) ∨ (u=c ∧ v=b) ∨ (u=c ∧ v=d) ∨ (u=d ∧ v=c) ∨
      (u=d ∧ v=a) ∨ (u=a ∧ v=d) := by
  rw [h.exactGraph]
  simp [Walk.toSubgraph, Subgraph.sup_adj, subgraphOfAdj_adj, eq_comm]
  tauto

end ZombieMain
