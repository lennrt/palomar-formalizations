module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic

@[expose] public section

/-! Edge ownership and the information-theoretic lower bound.

The finite incidence presentation below permits parallel edges.  Consequently
its accounting applies both to original simple graphs and to cell quotients.
The orientation theorem is not assumed here: its needed conclusion is the
explicit numeric hypothesis in `paired_boundary_balance`.
-/
namespace LocalDecompression
open scoped BigOperators

/-- A finite undirected edge presentation with two endpoints for each edge.
The ordering of endpoints is only a bookkeeping choice. -/
structure EdgePresentation (V E : Type*) where
  left : E → V
  right : E → V
  noLoop : ∀ e, left e ≠ right e

namespace EdgePresentation
variable {V E : Type*} [DecidableEq V] [Fintype E]

/-- Degree counted with edge multiplicity. -/
def degree (G : EdgePresentation V E) (v : V) : ℕ :=
  ∑ e, ((if G.left e = v then 1 else 0) + (if G.right e = v then 1 else 0))

def internal (G : EdgePresentation V E) (cell : Finset V) : ℕ :=
  ∑ e, if G.left e ∈ cell ∧ G.right e ∈ cell then 1 else 0

def boundary (G : EdgePresentation V E) (cell : Finset V) : ℕ :=
  ∑ e, if (G.left e ∈ cell ∧ G.right e ∉ cell) ∨
    (G.left e ∉ cell ∧ G.right e ∈ cell) then 1 else 0

/-- The exact cell-incidence identity, including all crossing edges. -/
theorem cell_degree_sum (G : EdgePresentation V E) (cell : Finset V) :
    ∑ v ∈ cell, G.degree v = 2 * G.internal cell + G.boundary cell := by
  unfold degree internal boundary
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.sum_add_distrib]
  by_cases hl : G.left e ∈ cell <;> by_cases hr : G.right e ∈ cell <;>
    simp [eq_comm, hl, hr]

theorem incidence_bound (G : EdgePresentation V E) (cell : Finset V) (d : ℕ)
    (hdegree : ∀ v ∈ cell, G.degree v ≤ d) :
    2 * G.internal cell + G.boundary cell ≤ d * cell.card := by
  rw [← G.cell_degree_sum]
  calc
    ∑ v ∈ cell, G.degree v ≤ ∑ _v ∈ cell, d := Finset.sum_le_sum hdegree
    _ = d * cell.card := by simp [Nat.mul_comm]

/-- The handshake identity for the finite edge presentation. -/
theorem degree_sum [Fintype V] (G : EdgePresentation V E) :
    ∑ v, G.degree v = 2 * Fintype.card E := by
  simpa [internal, boundary] using G.cell_degree_sum Finset.univ

/-- The full component fits in k bits per vertex when its degrees are ≤2k. -/
theorem global_edge_capacity [Fintype V] (G : EdgePresentation V E) (k : ℕ)
    (hdegree : ∀ v, G.degree v ≤ 2 * k) : Fintype.card E ≤ k * Fintype.card V := by
  have hs := G.degree_sum
  have hb : ∑ v, G.degree v ≤ Fintype.card V * (2 * k) := by
    calc
      ∑ v, G.degree v ≤ ∑ _v : V, 2 * k := Finset.sum_le_sum (fun v _ => hdegree v)
      _ = _ := by simp
  nlinarith

end EdgePresentation

/-- Pairing equal numbers of inward and outward boundary edges leaves only
the odd-multiplicity quotient's orientation discrepancy. -/
theorem paired_boundary_balance (pairs residual residualOut : ℕ)
    (hbalance : 2 * residualOut ≤ residual + 1) :
    2 * (pairs + residualOut) ≤ (2 * pairs + residual) + 1 := by omega

/-- Every multiplicity is a paired part and at most one residual edge. -/
theorem multiplicity_decomposition {C : Type*} [Fintype C] (multiplicity : C → ℕ) :
    2 * (∑ c, multiplicity c / 2) + (∑ c, multiplicity c % 2) =
      ∑ c, multiplicity c := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  omega

theorem multiplicity_boundary_balance {C : Type*} [Fintype C]
    (multiplicity : C → ℕ) (residualOut : ℕ)
    (hbalance : 2 * residualOut ≤ (∑ c, multiplicity c % 2) + 1) :
    2 * ((∑ c, multiplicity c / 2) + residualOut) ≤
      (∑ c, multiplicity c) + 1 := by
  have hp := paired_boundary_balance (∑ c, multiplicity c / 2)
    (∑ c, multiplicity c % 2) residualOut hbalance
  simpa [multiplicity_decomposition] using hp

/-- Internal edges plus the outgoing boundary fit in ceil(d*s/2) slots. -/
theorem owned_edge_bound (internal boundary outgoing d s : ℕ)
    (hincidence : 2 * internal + boundary ≤ d * s)
    (hbalance : 2 * outgoing ≤ boundary + 1) :
    internal + outgoing ≤ (d * s + 1) / 2 := by omega

/-- The ownership bound applied to an actual finite cell incidence structure. -/
theorem cell_owned_edge_bound {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (G : EdgePresentation V E) (cell : Finset V) (d outgoing : ℕ)
    (hdegree : ∀ v ∈ cell, G.degree v ≤ d)
    (hbalance : 2 * outgoing ≤ G.boundary cell + 1) :
    G.internal cell + outgoing ≤ (d * cell.card + 1) / 2 :=
  owned_edge_bound _ _ _ _ _ (G.incidence_bound cell d hdegree) hbalance

/-- A lossless decoder forces the encoder to be injective, even if decoding
is centralized and has no locality restriction. -/
theorem lossless_label_count (vertices edges bits : ℕ)
    (encode : (Fin edges → Fin 2) → (Fin vertices → Fin (2 ^ bits)))
    (decode : (Fin vertices → Fin (2 ^ bits)) → (Fin edges → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) :
    2 ^ edges ≤ 2 ^ (bits * vertices) := by
  have hi : Function.Injective encode := Function.LeftInverse.injective roundtrip
  have hc := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_fun, Fintype.card_fin, ← pow_mul] using hc

theorem lossless_bit_budget (vertices edges bits : ℕ)
    (encode : (Fin edges → Fin 2) → (Fin vertices → Fin (2 ^ bits)))
    (decode : (Fin vertices → Fin (2 ^ bits)) → (Fin edges → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : edges ≤ bits * vertices := by
  have h := lossless_label_count vertices edges bits encode decode roundtrip
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp h

/-- The counting bound directly on vertex and edge types, without reindexing. -/
theorem finite_lossless_bit_budget {V E : Type*} [Fintype V] [Fintype E] (bits : ℕ)
    (encode : (E → Fin 2) → (V → Fin (2 ^ bits)))
    (decode : (V → Fin (2 ^ bits)) → (E → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) :
    Fintype.card E ≤ bits * Fintype.card V := by
  classical
  have hi : Function.Injective encode := Function.LeftInverse.injective roundtrip
  have hc := Fintype.card_le_of_injective encode hi
  simp only [Fintype.card_fun, Fintype.card_fin, ← pow_mul] at hc
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hc

/-- The generic edge/vertex density lower bound on fixed-length advice. -/
theorem regular_degree_lower_bound (vertices edges bits d : ℕ)
    (hn : 0 < vertices) (hregular : 2 * edges = d * vertices)
    (encode : (Fin edges → Fin 2) → (Fin vertices → Fin (2 ^ bits)))
    (decode : (Fin vertices → Fin (2 ^ bits)) → (Fin edges → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (d + 1) / 2 ≤ bits := by
  have hb := lossless_bit_budget vertices edges bits encode decode roundtrip
  have hd : d ≤ 2 * bits := by nlinarith
  omega

/-- In particular, any nonempty cubic graph requires at least two bits. -/
theorem cubic_lower_bound (vertices edges bits : ℕ)
    (hn : 0 < vertices) (hregular : 2 * edges = 3 * vertices)
    (encode : (Fin edges → Fin 2) → (Fin vertices → Fin (2 ^ bits)))
    (decode : (Fin vertices → Fin (2 ^ bits)) → (Fin edges → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : 2 ≤ bits := by
  simpa using regular_degree_lower_bound vertices edges bits 3 hn hregular
    encode decode roundtrip

/-- The lower bound for an actual nonempty finite regular edge presentation. -/
theorem finite_regular_lower_bound {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [Nonempty V] (G : EdgePresentation V E) (d bits : ℕ)
    (hregular : ∀ v, G.degree v = d)
    (encode : (E → Fin 2) → (V → Fin (2 ^ bits)))
    (decode : (V → Fin (2 ^ bits)) → (E → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (d + 1) / 2 ≤ bits := by
  have hb := finite_lossless_bit_budget bits encode decode roundtrip
  have hs := G.degree_sum
  simp [hregular] at hs
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hd : d ≤ 2 * bits := by nlinarith
  omega

/-- The information bound on Mathlib's finite simple graphs. -/
theorem simpleGraph_regular_lower_bound {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (d bits : ℕ)
    (hregular : ∀ v, G.degree v = d)
    (encode : (G.edgeSet → Fin 2) → (V → Fin (2 ^ bits)))
    (decode : (V → Fin (2 ^ bits)) → (G.edgeSet → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (d + 1) / 2 ≤ bits := by
  have hb := finite_lossless_bit_budget bits encode decode roundtrip
  have hs := G.sum_degrees_eq_twice_card_edges
  rw [G.card_edgeSet] at hb
  simp only [hregular, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hd : d ≤ 2 * bits := by nlinarith
  omega

/-- Complete graphs supply the regular instances needed for the family lower bound. -/
theorem completeGraph_lower_bound (d bits : ℕ)
    (encode : (((⊤ : SimpleGraph (Fin (d + 1))).edgeSet) → Fin 2) →
      (Fin (d + 1) → Fin (2 ^ bits)))
    (decode : (Fin (d + 1) → Fin (2 ^ bits)) →
      (((⊤ : SimpleGraph (Fin (d + 1))).edgeSet) → Fin 2))
    (roundtrip : ∀ x, decode (encode x) = x) : (d + 1) / 2 ≤ bits := by
  apply simpleGraph_regular_lower_bound (⊤ : SimpleGraph (Fin (d + 1))) d bits
    (fun v => by simp) encode decode roundtrip

end LocalDecompression
