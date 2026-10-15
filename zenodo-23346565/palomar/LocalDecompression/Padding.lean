module

public import LocalDecompression.LocalView
public import Mathlib.Combinatorics.SimpleGraph.Sum

@[expose] public section

/-! Exact virtual graph parameters for the imported orientation algorithm.

The original virtual graph already contains every original vertex, with
nonroots isolated. Adding a disjoint clique supplies a known exact maximum
degree without changing any original vertex's neighborhood. The identifier
extension preserves the original polynomial-range convention. These are
finite graph facts; execution of the imported algorithm is not asserted here.
-/
namespace LocalDecompression.Padding

variable {V : Type*}

/-- Place the root quotient on all original vertices; the additional
original vertices have no incident virtual edges. -/
def onOriginal (roots : Finset V) (H : SimpleGraph roots) : SimpleGraph V :=
  H.map Subtype.val

noncomputable instance (roots : Finset V) (H : SimpleGraph roots) :
    DecidableRel (onOriginal roots H).Adj := Classical.decRel _

theorem onOriginal_adj (roots : Finset V) (H : SimpleGraph roots) (u v : roots) :
    (onOriginal roots H).Adj u.val v.val ↔ H.Adj u v := by
  exact SimpleGraph.map_adj_apply (f := ⟨Subtype.val, Subtype.val_injective⟩)

theorem nonroot_isolated (roots : Finset V) (H : SimpleGraph roots)
    (v : V) (hv : v ∉ roots) (w : V) : ¬ (onOriginal roots H).Adj v w := by
  rintro ⟨_, u, _, _, hu, _⟩
  exact hv (hu ▸ u.property)

theorem onOriginal_root_degree [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) [DecidableRel H.Adj] (v : roots) :
    (onOriginal roots H).degree v.val = H.degree v := by
  classical
  simp only [← SimpleGraph.ncard_neighborSet]
  change ((H.map (⟨Subtype.val, Subtype.val_injective⟩ : roots ↪ V)).neighborSet v.val).ncard = _
  simpa only [← SimpleGraph.ncard_neighborSet, Function.Embedding.coeFn_mk] using
    SimpleGraph.degree_map_apply H ⟨Subtype.val, Subtype.val_injective⟩ v

theorem onOriginal_degree_le [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) [DecidableRel H.Adj] (D : ℕ)
    (hdegree : ∀ v, H.degree v ≤ D) (v : V) : (onOriginal roots H).degree v ≤ D := by
  classical
  by_cases hv : v ∈ roots
  · exact (onOriginal_root_degree roots H ⟨v, hv⟩).trans_le (hdegree ⟨v, hv⟩)
  · have he : (onOriginal roots H).neighborFinset v = ∅ := by
      ext w
      simp [nonroot_isolated roots H v hv w]
    simp [SimpleGraph.degree, he]

/-- The graph actually passed to the advice encoder: the original virtual
graph and a disjoint complete graph on `D + 1` new vertices. -/
def paddedGraph (G : SimpleGraph V) (D : ℕ) : SimpleGraph (V ⊕ Fin (D + 1)) :=
  G.sum ⊤

noncomputable instance (G : SimpleGraph V) (D : ℕ) :
    DecidableRel (paddedGraph G D).Adj := Classical.decRel _

/-- The order of the padded input is known from the original order and D. -/
theorem padded_order [Fintype V] (D : ℕ) :
    Fintype.card (V ⊕ Fin (D + 1)) = Fintype.card V + D + 1 := by
  simp [Nat.add_assoc]

/-- Padding preserves every original adjacency exactly. -/
theorem original_adj (G : SimpleGraph V) (D : ℕ) (v w : V) :
    (paddedGraph G D).Adj (.inl v) (.inl w) ↔ G.Adj v w := Iff.rfl

/-- No original vertex can receive information along a path from the clique. -/
theorem clique_unreachable (G : SimpleGraph V) (D : ℕ) (v : V) (w : Fin (D + 1)) :
    ¬ (paddedGraph G D).Reachable (.inl v) (.inr w) :=
  SimpleGraph.not_reachable_sum_inl_inr v w

/-- The exact degree of an original vertex is unchanged. -/
theorem original_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ) (v : V) :
    (paddedGraph G D).degree (.inl v) = G.degree v := by
  classical
  have h : (paddedGraph G D).neighborFinset (.inl v) =
      (G.neighborFinset v).image (Sum.inl : V → V ⊕ Fin (D + 1)) := by
    ext w
    rw [SimpleGraph.mem_neighborFinset]
    cases w <;> simp [paddedGraph]
  simp only [SimpleGraph.degree, h]
  exact Finset.card_image_of_injective _ Sum.inl_injective

/-- Every added vertex has degree exactly D, including the D=0 case. -/
theorem clique_degree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : ℕ) (w : Fin (D + 1)) :
    (paddedGraph G D).degree (.inr w) = D := by
  classical
  have h : (paddedGraph G D).neighborFinset (.inr w) =
      ((⊤ : SimpleGraph (Fin (D + 1))).neighborFinset w).image
        (Sum.inr : Fin (D + 1) → V ⊕ Fin (D + 1)) := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v <;> simp [paddedGraph, eq_comm]
  rw [SimpleGraph.degree, h, Finset.card_image_of_injective _ Sum.inr_injective]
  change (⊤ : SimpleGraph (Fin (D + 1))).degree w = D
  simp [SimpleGraph.complete_graph_degree]

/-- An upper degree bound on the old graph becomes an exact maximum degree. -/
theorem padded_maxDegree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : ℕ)
    (hdegree : ∀ v, G.degree v ≤ D) : (paddedGraph G D).maxDegree = D := by
  apply Nat.le_antisymm
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    cases v with
    | inl v => simpa only [original_degree] using hdegree v
    | inr w => exact (clique_degree G D w).le
  · have h := (paddedGraph G D).degree_le_maxDegree (.inr ⟨0, by omega⟩)
    simpa only [clique_degree] using h

/-- A positive power gains at least the added base increment. -/
theorem power_add_increment (n t c : ℕ) (hc : 1 ≤ c) :
    n ^ c + t ≤ (n + t) ^ c := by
  induction c, hc using Nat.le_induction with
  | base => simp
  | succ c hc ih =>
    by_cases hzero : n + t = 0
    · have hn : n = 0 := by omega
      have ht : t = 0 := by omega
      simp [hn, ht]
    have hpos : 1 ≤ n + t := by omega
    calc
      n ^ (c + 1) + t = n ^ c * n + t := by rw [pow_succ]
      _ ≤ (n ^ c + t) * (n + t) := by
        nlinarith [Nat.mul_le_mul_left t hpos, Nat.zero_le (n ^ c * t)]
      _ ≤ (n + t) ^ c * (n + t) := Nat.mul_le_mul_right _ ih
      _ = (n + t) ^ (c + 1) := by rw [pow_succ]

/-- Original identifiers are retained; clique identifiers start above n^c. -/
def paddedId (id : V → ℕ) (n c D : ℕ) : V ⊕ Fin (D + 1) → ℕ :=
  Sum.elim id (fun w => n ^ c + 1 + w.val)

theorem paddedId_original (id : V → ℕ) (n c D : ℕ) (v : V) :
    paddedId id n c D (.inl v) = id v := rfl

/-- No dummy identifier collides with an original one, and both parts are injective. -/
theorem paddedId_injective (id : V → ℕ) (n c D : ℕ)
    (hinj : Function.Injective id) (hbound : ∀ v, id v ≤ n ^ c) :
    Function.Injective (paddedId id n c D) := by
  intro x y h
  cases x with
  | inl v =>
    cases y with
    | inl w => exact congrArg Sum.inl (hinj h)
    | inr w => have hb := hbound v; simp only [paddedId, Sum.elim_inl, Sum.elim_inr] at h; omega
  | inr v =>
    cases y with
    | inl w => have hb := hbound w; simp only [paddedId, Sum.elim_inl, Sum.elim_inr] at h; omega
    | inr w =>
      apply congrArg Sum.inr
      apply Fin.ext
      simp only [paddedId, Sum.elim_inr] at h
      omega

/-- The same exponent c suffices for every identifier in the padded input. -/
theorem paddedId_range (id : V → ℕ) (n c D : ℕ) (hc : 1 ≤ c)
    (hpositive : ∀ v, 1 ≤ id v) (hbound : ∀ v, id v ≤ n ^ c)
    (x : V ⊕ Fin (D + 1)) :
    1 ≤ paddedId id n c D x ∧ paddedId id n c D x ≤ (n + D + 1) ^ c := by
  have hp := power_add_increment n (D + 1) c hc
  simp only [← Nat.add_assoc] at hp
  cases x with
  | inl v =>
    have hv := hbound v
    exact ⟨hpositive v, by change id v ≤ _; omega⟩
  | inr w =>
    have hw := w.isLt
    simp only [paddedId, Sum.elim_inr]
    constructor <;> omega

/-- The precise graph order, maximum degree and identifier contract used
when applying the external theorem to a root quotient. This theorem does
not assume or assert an implementation of that external algorithm. -/
theorem padded_input_parameters [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) [DecidableRel H.Adj]
    (id : V → ℕ) (c D : ℕ) (hc : 1 ≤ c)
    (hinj : Function.Injective id) (hpositive : ∀ v, 1 ≤ id v)
    (hbound : ∀ v, id v ≤ (Fintype.card V) ^ c) (hdegree : ∀ v, H.degree v ≤ D) :
    Fintype.card (V ⊕ Fin (D + 1)) = Fintype.card V + D + 1 ∧
    (paddedGraph (onOriginal roots H) D).maxDegree = D ∧
    Function.Injective (paddedId id (Fintype.card V) c D) ∧
    ∀ x, 1 ≤ paddedId id (Fintype.card V) c D x ∧
      paddedId id (Fintype.card V) c D x ≤ (Fintype.card V + D + 1) ^ c := by
  exact ⟨padded_order D,
    padded_maxDegree _ D (onOriginal_degree_le roots H D hdegree),
    paddedId_injective id _ c D hinj hbound,
    paddedId_range id _ c D hc hpositive hbound⟩

end LocalDecompression.Padding
