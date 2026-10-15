module

public import LocalDecompression.Ownership
public import Mathlib.Data.Sym.Sym2.Order

@[expose] public section

/-! A faithful, canonically ordered presentation of a simple graph.

Every undirected graph edge occurs exactly once, with its smaller endpoint
first. The order used for payload slots is the lexicographic endpoint order.
The vertex linear order is an explicit parameter; the distributed construction
instantiates it with the identifier order.
-/
namespace LocalDecompression

variable {V : Type*} [LinearOrder V]

/-- Actual simple-graph edges, represented once in increasing endpoint order. -/
abbrev GraphEdge (G : SimpleGraph V) :=
  {p : V × V // p.1 < p.2 ∧ G.Adj p.1 p.2}

instance graphEdgeLinearOrder (G : SimpleGraph V) : LinearOrder (GraphEdge G) :=
  LinearOrder.lift' (fun e : GraphEdge G => (toLex e.val : V ×ₗ V)) (by
    intro a b h
    apply Subtype.ext
    exact congrArg ofLex h)

/-- The endpoints are the actual vertices joined by this simple-graph edge. -/
def graphPresentation (G : SimpleGraph V) : EdgePresentation V (GraphEdge G) where
  left e := e.val.1
  right e := e.val.2
  noLoop e := ne_of_lt e.property.1

@[simp] theorem graphPresentation_adj (G : SimpleGraph V) (e : GraphEdge G) :
    G.Adj ((graphPresentation G).left e) ((graphPresentation G).right e) :=
  e.property.2

/-- The canonical presentation has exactly Mathlib's unordered edge set. -/
def graphEdgeEquiv (G : SimpleGraph V) : GraphEdge G ≃ G.edgeSet where
  toFun e := ⟨s(e.val.1, e.val.2), e.property.2⟩
  invFun e := by
    refine ⟨((Sym2.sortEquiv e.val).val), ?_, ?_⟩
    · have ha : G.Adj (Sym2.sortEquiv e.val).val.1 (Sym2.sortEquiv e.val).val.2 := by
        have he := e.property
        rw [← Sym2.sortEquiv.symm_apply_apply e.val] at he
        exact he
      exact lt_of_le_of_ne (Sym2.sortEquiv e.val).property ha.ne
    · have he := e.property
      rw [← Sym2.sortEquiv.symm_apply_apply e.val] at he
      exact he
  left_inv e := by
    apply Subtype.ext
    change (Sym2.sortEquiv s(e.val.1, e.val.2)).val = e.val
    simpa using congrArg Subtype.val
      (Sym2.sortEquiv.apply_symm_apply ⟨e.val, le_of_lt e.property.1⟩)
  right_inv e := by
    apply Subtype.ext
    exact Sym2.sortEquiv.symm_apply_apply e.val

@[simp] theorem graphEdgeEquiv_apply (G : SimpleGraph V) (e : GraphEdge G) :
    (graphEdgeEquiv G e).val = s(e.val.1, e.val.2) := rfl

/-- Incident edges in the canonical presentation coincide with the graph's
incidence set, rather than merely having a compatible cardinality bound. -/
def graphIncidentEquiv (G : SimpleGraph V) (v : V) :
    {e : GraphEdge G // (graphPresentation G).left e = v ∨
      (graphPresentation G).right e = v} ≃ G.incidenceSet v :=
  (Equiv.subtypeEquiv (q := fun e : G.edgeSet => v ∈ e.val)
    (graphEdgeEquiv G) (fun e => by
    simp [graphPresentation, eq_comm])).trans
    { toFun := fun e => ⟨e.val.val, e.val.property, e.property⟩
      invFun := fun e => ⟨⟨e.val, e.property.1⟩, e.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- Presentation degree equals the degree of the very same simple graph. -/
theorem graphPresentation_degree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : (graphPresentation G).degree v = G.degree v := by
  classical
  rw [← G.card_incidenceSet_eq_degree v, ← Fintype.card_congr (graphIncidentEquiv G v)]
  rw [Fintype.card_subtype]
  simp only [EdgePresentation.degree, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e _
  have hne := (graphPresentation G).noLoop e
  by_cases hl : (graphPresentation G).left e = v <;>
    by_cases hr : (graphPresentation G).right e = v <;> simp [hl, hr]
  all_goals aesop

end LocalDecompression
