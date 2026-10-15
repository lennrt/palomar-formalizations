module
public import LocalDecompression.UniformDecoder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket Reduction
open LocalDecompression.OrientationOracle
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Normalize the queried endpoints so either endpoint recovers the same edge
bit. The query does not alter the encoded vertex labels. -/
noncomputable def symmetricUniformDecode {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R d : ℕ) (labels : V → Fin (q+1)) (e : V × V) : Fin 2 :=
  uniformDecode hq F N D c T G id R d labels (toLex (min e.1 e.2, max e.1 e.2))

theorem symmetricUniformDecode_swap {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R d : ℕ) (labels : V → Fin (q+1)) (u v : V) :
    symmetricUniformDecode hq F N D c T G id R d labels (u,v) =
      symmetricUniformDecode hq F N D c T G id R d labels (v,u) := by
  simp only [symmetricUniformDecode, min_comm u v, max_comm u v]

theorem symmetricUniformDecode_forward {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R d : ℕ) (labels : V → Fin (q+1)) (u v : V) (h : u ≤ v) :
    symmetricUniformDecode hq F N D c T G id R d labels (u,v) =
      uniformDecode hq F N D c T G id R d labels (toLex (u,v)) := by
  simp only [symmetricUniformDecode, min_eq_left h, max_eq_right h]

theorem symmetricUniformDecode_nonedge {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (R d : ℕ) (labels : V → Fin (q+1)) (u v : V) (h : ¬ G.Adj u v) :
    symmetricUniformDecode hq F N D c T G id R d labels (u,v) = 0 := by
  unfold symmetricUniformDecode uniformDecode
  apply boundedPairDecode_nonedge
  intro he
  have hadj := ((mem_actualPairs G _).mp he).2
  change G.Adj (min u v) (max u v) at hadj
  by_cases huv : u ≤ v
  · exact h (by simpa only [min_eq_left huv, max_eq_right huv] using hadj)
  · apply h
    have h' : G.Adj v u := by
      simpa only [min_eq_right (le_of_not_ge huv), max_eq_left (le_of_not_ge huv)] using hadj
    exact h'.symm

/-- A physical view with radius at least one determines every incident
adjacency, even for a queried second identifier outside the observed ball. -/
theorem incident_adj_iff_of_graph_view (G H : SimpleGraph V) (u v : V) (K : ℕ)
    (physical : SameGraphView G H u K) (hK : 1 ≤ K) : G.Adj u v ↔ H.Adj u v := by
  constructor
  · intro h
    have hv : G.dist u v ≤ K := (le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr h)).trans hK
    exact (physical.edges u v (by simp) hv).mp h
  · intro h
    have hv : H.dist u v ≤ K := (le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr h)).trans hK
    exact (physical.edges u v (by simp) ((physical.vertices v).mpr hv)).mpr h

/-- Both endpoints have a bounded physical-view decoder. Sorting the query
costs at most one extra hop, so no endpoint has to know which one is smaller
before observing its local neighborhood. Arbitrary labels remain total. -/
theorem symmetricUniformDecode_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (F : Rule) (N D c T : ℕ)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R d : ℕ)
    (x y : V → Fin (q+1)) (u v : V)
    (physical : SameGraphView G H u (decodeRadius R T + 1))
    (hlabels : ∀ w, G.dist u w ≤ decodeRadius R T + 1 → x w = y w) :
    symmetricUniformDecode hq F N D c T G id R d x (u,v) =
      symmetricUniformDecode hq F N D c T H id R d y (u,v) := by
  by_cases hadj : G.Adj u v
  · have hnear : G.dist u (min u v) ≤ 1 := by
      by_cases huv : u ≤ v
      · simp [min_eq_left huv]
      · rw [min_eq_right (le_of_not_ge huv)]
        exact le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hadj)
    apply uniformDecode_eq_of_graph_view hq F N D c T G H hG hH id hinj R d x y
      (toLex (min u v, max u v))
    · exact nearby_view G H hG hH u 1 (decodeRadius R T)
        (by simpa only [Nat.add_comm] using physical) (min u v) hnear
    · intro w hw
      change G.dist (min u v) w ≤ decodeRadius R T at hw
      exact hlabels w (le_trans (hG.dist_triangle (u := u) (v := min u v) (w := w)) (by omega))
  · have hn : ¬ H.Adj u v := fun h => hadj
      ((incident_adj_iff_of_graph_view G H u v _ physical (by omega)).mpr h)
    rw [symmetricUniformDecode_nonedge hq F N D c T G id R d x u v hadj,
      symmetricUniformDecode_nonedge hq F N D c T H id R d y u v hn]

end LocalDecompression.FiniteView
