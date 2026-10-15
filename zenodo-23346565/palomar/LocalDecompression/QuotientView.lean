module
public import LocalDecompression.NamedDecoder

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The actual canonically ordered crossing-edge fiber, in a common ambient
edge-name space. Uncovered endpoints are discarded by the Option tests. -/
noncomputable def crossingPairs {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c d : V) : Finset (NamedPair V) := by
  classical
  let part := boundedOwner G id R labels
  exact (actualPairs G).filter (fun e =>
    (part (ofLex e).1 = some c ∧ part (ofLex e).2 = some d) ∨
    (part (ofLex e).1 = some d ∧ part (ofLex e).2 = some c))

@[simp] theorem mem_crossingPairs {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c d : V) (e : NamedPair V) :
    e ∈ crossingPairs G id R labels c d ↔
      e ∈ actualPairs G ∧
        ((boundedOwner G id R labels (ofLex e).1 = some c ∧
          boundedOwner G id R labels (ofLex e).2 = some d) ∨
         (boundedOwner G id R labels (ofLex e).1 = some d ∧
          boundedOwner G id R labels (ofLex e).2 = some c)) := by
  classical
  simp [crossingPairs]

theorem crossingPairs_symm {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c d : V) :
    crossingPairs G id R labels c d = crossingPairs G id R labels d c := by
  ext e
  simp only [mem_crossingPairs, or_comm]

theorem owner_distance {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    {c v : V} (h : boundedOwner G id R labels v = some c) : G.dist c v ≤ R :=
  ((boundedOwner_some_iff G id hinj R labels v c).mp h).2

/-- Both physical endpoints of a root's crossing fiber lie within R+1,
including inputs lacking global marker coverage or separation. -/
theorem crossingPairs_near {q : ℕ} (G : SimpleGraph V) (hG : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (c d : V) (e : NamedPair V) (he : e ∈ crossingPairs G id R labels c d) :
    G.dist c (ofLex e).1 ≤ R+1 ∧ G.dist c (ofLex e).2 ≤ R+1 := by
  obtain ⟨hp, ho | ho⟩ := (mem_crossingPairs G id R labels c d e).mp he
  · have hnear := owner_distance G id hinj R labels ho.1
    have hadj := (mem_actualPairs G e).mp hp
    have hedge : G.dist (ofLex e).1 (ofLex e).2 ≤ 1 := le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.2)
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).1) (w := (ofLex e).2)
    exact ⟨by omega, by omega⟩
  · have hnear := owner_distance G id hinj R labels ho.2
    have hadj := (mem_actualPairs G e).mp hp
    have hedge : G.dist (ofLex e).2 (ofLex e).1 ≤ 1 := le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.2.symm)
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).2) (w := (ofLex e).1)
    exact ⟨by omega, by omega⟩

/-- The entire crossing fiber, including multiplicity and canonical ranks,
is unchanged by an equal radius-(2R+1) physical/marker view at either root. -/
theorem crossingPairs_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c d : V) (R : ℕ)
    (view : SameGraphView G H c ((R+1)+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ (R+1)+R → (x w = 0 ↔ y w = 0)) :
    crossingPairs G id R x c d = crossingPairs H id R y c d := by
  have forward : ∀ (G H : SimpleGraph V), G.Connected → H.Connected →
      ∀ (x y : V → Fin (q+1)), SameGraphView G H c ((R+1)+R) →
      (∀ w, G.dist c w ≤ (R+1)+R → (x w = 0 ↔ y w = 0)) →
      crossingPairs G id R x c d ⊆ crossingPairs H id R y c d := by
    intro G H hG hH x y view hlabels e he
    obtain ⟨hnl, hnr⟩ := crossingPairs_near G hG id hinj R x c d e he
    have hlo := boundedOwner_eq_of_graph_view G H hG hH id hinj (ofLex e).1 R
      (nearby_view G H hG hH c (R+1) R view (ofLex e).1 hnl) x y
      (fun w hw => hlabels w (le_trans (hG.dist_triangle (u := c) (v := (ofLex e).1) (w := w)) (by omega)))
    have hro := boundedOwner_eq_of_graph_view G H hG hH id hinj (ofLex e).2 R
      (nearby_view G H hG hH c (R+1) R view (ofLex e).2 hnr) x y
      (fun w hw => hlabels w (le_trans (hG.dist_triangle (u := c) (v := (ofLex e).2) (w := w)) (by omega)))
    obtain ⟨hp, ho⟩ := (mem_crossingPairs G id R x c d e).mp he
    apply (mem_crossingPairs H id R y c d e).mpr
    refine ⟨?_, ?_⟩
    · obtain ⟨hlt, hadj⟩ := (mem_actualPairs G e).mp hp
      exact (mem_actualPairs H e).mpr ⟨hlt,
        (view.edges _ _ (by omega) (by omega)).mp hadj⟩
    · simpa only [← hlo, ← hro] using ho
  apply Finset.Subset.antisymm
  · exact forward G H hG hH x y view hlabels
  · exact forward H G hH hG y x view.symm
      (fun w hw => (hlabels w ((view.vertices w).mpr hw)).symm)

/-- The actual residual simple graph: one edge survives exactly when the
physical crossing fiber has odd multiplicity. Unassigned vertices stay out. -/
noncomputable def boundedResidualGraph {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) : SimpleGraph V where
  Adj c d := c ≠ d ∧ (crossingPairs G id R labels c d).card % 2 = 1
  symm := ⟨by
    intro c d h
    exact ⟨h.1.symm, by rw [← crossingPairs_symm G id R labels c d]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- No residual hop can exceed the geometric cell-to-cell bound 2R+1. -/
theorem boundedResidualGraph_edge_length {q : ℕ} (G : SimpleGraph V) (hG : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    {c d : V} (h : (boundedResidualGraph G id R labels).Adj c d) :
    G.dist c d ≤ 2*R+1 := by
  have hne : (crossingPairs G id R labels c d).Nonempty := by
    apply Finset.card_pos.mp
    have ho := h.2
    omega
  obtain ⟨e, he⟩ := hne
  obtain ⟨hp, ho | ho⟩ := (mem_crossingPairs G id R labels c d e).mp he
  · have hc := owner_distance G id hinj R labels ho.1
    have hd := owner_distance G id hinj R labels ho.2
    have hadj := (mem_actualPairs G e).mp hp
    have hedge : G.dist (ofLex e).1 (ofLex e).2 ≤ 1 := le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.2)
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).1) (w := (ofLex e).2)
    have ht' := hG.dist_triangle (u := c) (v := (ofLex e).2) (w := d)
    rw [G.dist_comm (u := (ofLex e).2) (v := d)] at ht'
    omega
  · have hc := owner_distance G id hinj R labels ho.2
    have hd := owner_distance G id hinj R labels ho.1
    have hadj := (mem_actualPairs G e).mp hp
    have hedge : G.dist (ofLex e).2 (ofLex e).1 ≤ 1 := le_of_eq (SimpleGraph.dist_eq_one_iff_adj.mpr hadj.2.symm)
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).2) (w := (ofLex e).1)
    have ht' := hG.dist_triangle (u := c) (v := (ofLex e).1) (w := d)
    rw [G.dist_comm (u := (ofLex e).1) (v := d)] at ht'
    omega

/-- The full neighbor list of a residual root, not only its observed induced
subgraph, is determined by the physical radius-(2R+1) marker view. -/
theorem boundedResidualGraph_adj_iff {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c d : V) (R : ℕ)
    (view : SameGraphView G H c ((R+1)+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ (R+1)+R → (x w = 0 ↔ y w = 0)) :
    (boundedResidualGraph G id R x).Adj c d ↔
      (boundedResidualGraph H id R y).Adj c d := by
  change (c ≠ d ∧ _) ↔ (c ≠ d ∧ _)
  rw [crossingPairs_eq_of_graph_view G H hG hH id hinj c d R view x y hlabels]

end LocalDecompression.FiniteView
