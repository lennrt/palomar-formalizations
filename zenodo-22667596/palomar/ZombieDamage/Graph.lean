import Std

/-!
Graph semantics for the local certificate language. This file is source, not
an assertion that a Lean build was run. See FORMALIZATION_STATUS.md.
-/
namespace ZombieDamage

structure Graph (V : Type) where
  adj : V → V → Prop
  symm : ∀ {u v}, adj u v → adj v u
  loopless : ∀ v, ¬ adj v v

namespace Graph
variable {V : Type} (G : Graph V)

inductive Walk : Nat → V → V → Prop where
  | nil (v : V) : Walk 0 v v
  | cons {k : Nat} {u v w : V} :
      G.adj u v → Walk k v w → Walk (Nat.succ k) u w

def Distance (k : Nat) (u v : V) : Prop :=
  G.Walk k u v ∧ ∀ j, G.Walk j u v → k ≤ j

def TwoApart (u w : V) : Prop :=
  u ≠ w ∧ ¬ G.adj u w ∧ ∃ v, G.adj u v ∧ G.adj v w

def GeodesicReply (u w x : V) : Prop :=
  G.adj u x ∧ ∃ d, G.Distance (Nat.succ d) u w ∧ G.Distance d x w

theorem walk_one_iff {u v : V} : G.Walk 1 u v ↔ G.adj u v := by
  constructor
  · intro h
    cases h with
    | cons huv tail =>
      cases tail
      exact huv
  · intro h
    exact Walk.cons h (Walk.nil v)

theorem adjacency_distance_one {u v : V} (h : G.adj u v) :
    G.Distance 1 u v := by
  constructor
  · exact (G.walk_one_iff).2 h
  · intro j hj
    cases j with
    | zero =>
      cases hj
      exact False.elim (G.loopless _ h)
    | succ j => exact Nat.succ_le_succ (Nat.zero_le j)

theorem twoApart_distance {u w : V} (h : G.TwoApart u w) :
    G.Distance 2 u w := by
  rcases h with ⟨hne, hnoedge, v, huv, hvw⟩
  constructor
  · exact Walk.cons huv (Walk.cons hvw (Walk.nil w))
  · intro j hj
    cases j with
    | zero =>
      cases hj
      exact False.elim (hne rfl)
    | succ j =>
      cases j with
      | zero =>
        exact False.elim (hnoedge ((G.walk_one_iff).1 hj))
      | succ j =>
        exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le j))

theorem geodesicReply_iff_commonNeighbor {u w x : V}
    (h : G.TwoApart u w) :
    G.GeodesicReply u w x ↔ G.adj u x ∧ G.adj x w := by
  have hdist := G.twoApart_distance h
  constructor
  · rintro ⟨hux, d, hduw, hdxw⟩
    have heq : Nat.succ d = 2 :=
      Nat.le_antisymm (hduw.2 2 hdist.1) (hdist.2 _ hduw.1)
    have hd : d = 1 := Nat.succ.inj heq
    subst d
    exact ⟨hux, (G.walk_one_iff).1 hdxw.1⟩
  · rintro ⟨hux, hxw⟩
    exact ⟨hux, 1, hdist, G.adjacency_distance_one hxw⟩

/-- Absence of actual triangles and quadrilaterals through the edge ab.
The two displayed inequalities, together with looplessness of the four edges,
ensure four distinct vertices in the quadrilateral clause. -/
def Clean (a b : V) : Prop :=
  G.adj a b ∧
  (∀ c, ¬ (G.adj b c ∧ G.adj c a)) ∧
  (∀ c d, a ≠ c → b ≠ d →
    ¬ (G.adj b c ∧ G.adj c d ∧ G.adj d a))

theorem cleanEdge_twoApart {u v w : V}
    (hc : G.Clean v w) (huv : G.adj u v) (huw : u ≠ w) :
    G.TwoApart u w := by
  refine ⟨huw, ?_, v, huv, hc.1⟩
  intro he
  exact hc.2.1 u ⟨G.symm he, huv⟩

theorem cleanEdge_forces_reply {u v w x : V}
    (hc : G.Clean v w) (huv : G.adj u v) (huw : u ≠ w) :
    G.GeodesicReply u w x ↔ x = v := by
  classical
  have hm := G.geodesicReply_iff_commonNeighbor
    (x := x) (G.cleanEdge_twoApart hc huv huw)
  constructor
  · intro hx
    rcases hm.1 hx with ⟨hux, hxw⟩
    by_cases heq : x = v
    · exact heq
    · have hvc : v ≠ x := fun hh => heq hh.symm
      have hwu : w ≠ u := fun hh => huw hh.symm
      exact False.elim
        (hc.2.2 x u hvc hwu ⟨G.symm hxw, G.symm hux, huv⟩)
  · intro hx
    subst x
    exact hm.2 ⟨huv, hc.1⟩


/-- An edge lying on a triangle or quadrilateral: on an actual edge this is
exactly the negation of `Clean`. No ambient graph or cycle oracle is assumed. -/
def ShortAdj (u v : V) : Prop := G.adj u v ∧ ¬ G.Clean u v

/-- Closure of the short-cycle edge subgraph under all internal shortcuts and
all length-two zombie replies. This is the internal part of the paper's
local-to-ambient argument; it does not assert the quotient routing theorem. -/
theorem short_twoStep_closed {u v w : V}
    (huv : G.ShortAdj u v) (hvw : G.ShortAdj v w) (hne : u ≠ w) :
    (G.adj u w → G.ShortAdj u w) ∧
    (∀ x, G.adj u x → G.adj x w →
      G.ShortAdj u x ∧ G.ShortAdj x w) := by
  constructor
  · intro huw
    refine ⟨huw, ?_⟩
    intro hc
    exact hc.2.1 v ⟨G.symm hvw.1, G.symm huv.1⟩
  · intro x hux hxw
    by_cases hx : x = v
    · subst x
      exact ⟨huv, hvw⟩
    · constructor
      · refine ⟨hux, ?_⟩
        intro hc
        exact hc.2.2 w v hne hx ⟨hxw, G.symm hvw.1, G.symm huv.1⟩
      · refine ⟨hxw, ?_⟩
        intro hc
        exact hc.2.2 v u hx (fun h => hne h.symm)
          ⟨G.symm hvw.1, G.symm huv.1, hux⟩

end Graph
end ZombieDamage
