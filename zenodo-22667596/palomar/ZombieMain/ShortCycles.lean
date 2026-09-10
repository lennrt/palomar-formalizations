import ZombieMain.CycleUnion
import ZombieDamage.Graph

namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

/-- Orient an actual cycle so that a specified edge is its first edge. -/
theorem IsShortCycle.orient {C : G.Subgraph} (hC : IsShortCycle C)
    {a b : V} (hab : C.Adj a b) :
    ∃ p : G.Walk a a, p.IsCycle ∧ p.length ≤ 4 ∧
      p.toSubgraph = C ∧ p.snd = b := by
  classical
  obtain ⟨u, p, hp, hlen, rfl⟩ := hC
  have ha : a ∈ p.support := p.mem_verts_toSubgraph.mp hab.fst_mem
  let q := p.rotate a ha
  have hq : q.IsCycle := hp.rotate ha
  have hqC : q.toSubgraph = p.toSubgraph := p.toSubgraph_rotate ha
  have hqab : b ∈ q.toSubgraph.neighborSet a := by
    change q.toSubgraph.Adj a b
    simpa [hqC] using hab
  rw [hq.neighborSet_toSubgraph_endpoint] at hqab
  rcases hqab with hfirst | hlast
  · exact ⟨q, hq, by simpa [q] using hlen, hqC, hfirst.symm⟩
  · refine ⟨q.reverse, hq.reverse, ?_, ?_, ?_⟩
    · simpa [q] using hlen
    · simpa using hqC
    · simpa [Walk.snd_reverse] using hlast.symm

/-- The edge-local triangle/quadrilateral predicate, with both diagonal
inequalities explicit in the quadrilateral case. -/
def ShortEdge (G : SimpleGraph V) (a b : V) : Prop :=
  G.Adj a b ∧ ((∃ c, G.Adj b c ∧ G.Adj c a) ∨
    ∃ c d, a ≠ c ∧ b ≠ d ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)

theorem IsShortCycle.shortEdge {C : G.Subgraph} (hC : IsShortCycle C)
    {a b : V} (hab : C.Adj a b) : ShortEdge G a b := by
  obtain ⟨p, hp, hlen, _, hsnd⟩ := hC.orient hab
  refine ⟨hab.adj_sub, ?_⟩
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
        | nil => exact Or.inl ⟨c, hbc, hcd⟩
        | @cons _ e _ hde q =>
          cases q with
          | nil =>
            right
            have hn := hp.support_nodup
            simp only [Walk.support_cons, Walk.support_nil, List.tail_cons,
              List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
              not_false_eq_true, and_true, not_or] at hn
            exact ⟨c, d, fun h => hn.2.1.2 h.symm, hn.1.2.1, hbc, hcd, hde⟩
          | cons _ _ => simp only [Walk.length_cons] at hlen; omega

theorem shortEdge_exists_cycle {a b : V} (h : ShortEdge G a b) :
    ∃ C : G.Subgraph, IsShortCycle C ∧ C.Adj a b := by
  rcases h with ⟨hab, htri | hsquare⟩
  · obtain ⟨c, hbc, hca⟩ := htri
    let p : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
    have hp : p.IsCycle := by
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · simp [p, Walk.isPath_def, hbc.ne, hca.ne, hab.ne.symm]
      · simp [p]
    refine ⟨p.toSubgraph, ⟨a, p, hp, by simp [p], rfl⟩, ?_⟩
    simp [p]
  · obtain ⟨c, d, hac, hbd, hbc, hcd, hda⟩ := hsquare
    let p : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hda .nil)))
    have hp : p.IsCycle := by
      rw [Walk.isCycle_iff_isPath_tail_and_le_length]
      constructor
      · simp [p, Walk.isPath_def, hbc.ne, hcd.ne, hda.ne, hab.ne.symm, hac.symm, hbd]
      · simp [p]
    refine ⟨p.toSubgraph, ⟨a, p, hp, by simp [p], rfl⟩, ?_⟩
    simp [p]

theorem shortEdge_iff_cycle {a b : V} : ShortEdge G a b ↔
    ∃ C : G.Subgraph, IsShortCycle C ∧ C.Adj a b :=
  ⟨shortEdge_exists_cycle, fun ⟨_, hC, hab⟩ => hC.shortEdge hab⟩

end ZombieMain

namespace ZombieMain
open SimpleGraph
variable {V : Type}

/-- The Mathlib graph has exactly the adjacency used by the checked game. -/
def gameGraph (G : SimpleGraph V) : ZombieDamage.Graph V where
  adj := G.Adj
  symm := G.adj_symm
  loopless := fun _ => G.irrefl

theorem shortEdge_iff_gameShort (G : SimpleGraph V) (a b : V) :
    ShortEdge G a b ↔ (gameGraph G).ShortAdj a b := by
  classical
  change G.Adj a b ∧ _ ↔ G.Adj a b ∧ ¬ (gameGraph G).Clean a b
  constructor
  · rintro ⟨hab, htri | hquad⟩
    · refine ⟨hab, ?_⟩
      intro hc
      obtain ⟨c, hbc, hca⟩ := htri
      exact hc.2.1 c ⟨hbc, hca⟩
    · refine ⟨hab, ?_⟩
      intro hc
      obtain ⟨c, d, hac, hbd, hbc, hcd, hda⟩ := hquad
      exact hc.2.2 c d hac hbd ⟨hbc, hcd, hda⟩
  · rintro ⟨hab, hn⟩
    refine ⟨hab, ?_⟩
    by_contra hnone
    simp only [not_or, not_exists, not_and] at hnone
    apply hn
    refine ⟨hab, ?_, ?_⟩
    · intro c h
      exact hnone.1 c h.1 h.2
    · intro c d hac hbd h
      exact hnone.2 c d hac hbd h.1 h.2.1 h.2.2

end ZombieMain
