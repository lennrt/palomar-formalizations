module
public import LocalDecompression.NamedDecoder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
@[expose] public section
namespace LocalDecompression.FiniteView
open Reduction MarkerLocality BoundedCells BoundedPacket
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem pairOwner_eq_some_incident (part : V → Option V) (dirs : NamedPair V → Fin 2)
    (e : NamedPair V) (c : V) (h : pairOwner part dirs e = some c) :
    part (ofLex e).1 = some c ∨ part (ofLex e).2 = some c := by
  unfold pairOwner at h
  cases hl : part (ofLex e).1 <;> cases hr : part (ofLex e).2 <;> simp only [hl,hr] at h
  all_goals try contradiction
  split_ifs at h <;> simp_all

theorem pairOwnedEdges_near {q : ℕ} (G : SimpleGraph V) (hG : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (dirs : NamedPair V → Fin 2) (c : V) (e : NamedPair V)
    (he : e ∈ pairOwnedEdges G (boundedOwner G id R labels) dirs c) :
    G.dist c (ofLex e).1 ≤ R+1 ∧ G.dist c (ofLex e).2 ≤ R+1 := by
  obtain ⟨ha,ho⟩ := (mem_pairOwnedEdges _ _ _ _ _).mp he
  have hadj := ((mem_actualPairs G e).mp ha).2
  have hd : G.dist (ofLex e).1 (ofLex e).2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
  obtain hl | hr := pairOwner_eq_some_incident _ _ _ _ ho
  · have hc := ((boundedOwner_some_iff G id hinj R labels _ _).mp hl).2
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).1) (w := (ofLex e).2)
    exact ⟨by omega,by omega⟩
  · have hc := ((boundedOwner_some_iff G id hinj R labels _ _).mp hr).2
    have ht := hG.dist_triangle (u := c) (v := (ofLex e).2) (w := (ofLex e).1)
    rw [G.dist_comm (u := (ofLex e).2) (v := (ofLex e).1)] at ht
    exact ⟨by omega,by omega⟩

theorem pairOwnedEdges_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c ((R+1)+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ (R+1)+R → (x w = 0 ↔ y w = 0))
    (ox oy : NamedPair V → Fin 2)
    (hdir : ∀ e, e ∈ actualPairs G → G.dist c (ofLex e).1 ≤ R+1 →
      G.dist c (ofLex e).2 ≤ R+1 → ox e = oy e) :
    pairOwnedEdges G (boundedOwner G id R x) ox c =
      pairOwnedEdges H (boundedOwner H id R y) oy c := by
  have forward : ∀ (G H : SimpleGraph V), G.Connected → H.Connected →
      ∀ (x y : V → Fin (q+1)), SameGraphView G H c ((R+1)+R) →
      (∀ w, G.dist c w ≤ (R+1)+R → (x w = 0 ↔ y w = 0)) →
      ∀ (ox oy : NamedPair V → Fin 2),
      (∀ e, e ∈ actualPairs G → G.dist c (ofLex e).1 ≤ R+1 →
        G.dist c (ofLex e).2 ≤ R+1 → ox e = oy e) →
      pairOwnedEdges G (boundedOwner G id R x) ox c ⊆
        pairOwnedEdges H (boundedOwner H id R y) oy c := by
    intro G H hG hH x y view hlabels ox oy hdir e he
    obtain ⟨hl,hr⟩ := pairOwnedEdges_near G hG id hinj R x ox c e he
    have hlo := boundedOwner_eq_of_graph_view G H hG hH id hinj (ofLex e).1 R
      (nearby_view G H hG hH c (R+1) R view (ofLex e).1 hl) x y
      (fun w hw => hlabels w (le_trans (hG.dist_triangle (u := c) (v := (ofLex e).1) (w := w)) (by omega)))
    have hro := boundedOwner_eq_of_graph_view G H hG hH id hinj (ofLex e).2 R
      (nearby_view G H hG hH c (R+1) R view (ofLex e).2 hr) x y
      (fun w hw => hlabels w (le_trans (hG.dist_triangle (u := c) (v := (ofLex e).2) (w := w)) (by omega)))
    obtain ⟨ha,ho⟩ := (mem_pairOwnedEdges _ _ _ _ _).mp he
    apply (mem_pairOwnedEdges _ _ _ _ _).mpr
    refine ⟨?_,?_⟩
    · obtain ⟨hlt,hadj⟩ := (mem_actualPairs G e).mp ha
      exact (mem_actualPairs H e).mpr ⟨hlt,(view.edges _ _ (by omega) (by omega)).mp hadj⟩
    · simpa only [pairOwner,← hlo,← hro,← hdir e ha hl hr] using ho
  apply Finset.Subset.antisymm
  · exact forward G H hG hH x y view hlabels ox oy hdir
  · apply forward H G hH hG y x view.symm
      (fun w hw => (hlabels w ((view.vertices w).mpr hw)).symm) oy ox
    intro e he hl hr
    have hl' : G.dist c (ofLex e).1 ≤ R+1 := by
      rw [center_distance_eq H G hH hG c _ view.symm _ (by omega)] at hl
      exact hl
    have hr' : G.dist c (ofLex e).2 ≤ R+1 := by
      rw [center_distance_eq H G hH hG c _ view.symm _ (by omega)] at hr
      exact hr
    have he' : e ∈ actualPairs G := by
      obtain ⟨hlt,hadj⟩ := (mem_actualPairs H e).mp he
      exact (mem_actualPairs G e).mpr ⟨hlt,(view.edges _ _ (by omega) (by omega)).mpr hadj⟩
    exact (hdir e he' hl' hr').symm


/-- Locality of the final total payload stage on arbitrary labels and changing
connected physical graphs. Only direction decisions for the nearby incident
edges are required to agree; no valid marker pattern or balancing is assumed. -/
theorem boundedPairDecode_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R d : ℕ)
    (x y : V → Fin (q+1)) (ox oy : NamedPair V → Fin 2) (e : NamedPair V)
    (view : SameGraphView G H (ofLex e).1 (3*R+2))
    (hlabels : ∀ w, G.dist (ofLex e).1 w ≤ 3*R+2 → x w = y w)
    (hdir : ∀ p, p ∈ actualPairs G → G.dist (ofLex e).1 (ofLex p).1 ≤ 2*R+2 →
      G.dist (ofLex e).1 (ofLex p).2 ≤ 2*R+2 → ox p = oy p) :
    boundedPairDecode hq G id R d x ox e = boundedPairDecode hq H id R d y oy e := by
  have transfer : ∀ (G H : SimpleGraph V),
      SameGraphView G H (ofLex e).1 (3*R+2) → e ∈ actualPairs G → e ∈ actualPairs H := by
    intro G H v he
    obtain ⟨hlt,hadj⟩ := (mem_actualPairs G e).mp he
    have hd : G.dist (ofLex e).1 (ofLex e).2 = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    exact (mem_actualPairs H e).mpr ⟨hlt,(v.edges _ _ (by simp) (by omega)).mp hadj⟩
  have hedge : e ∈ actualPairs G ↔ e ∈ actualPairs H :=
    ⟨transfer G H view,transfer H G view.symm⟩
  by_cases he : e ∈ actualPairs G
  · have hd : G.dist (ofLex e).1 (ofLex e).2 = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((mem_actualPairs G e).mp he).2
    have endpoint_owner : ∀ v, G.dist (ofLex e).1 v ≤ 1 →
        boundedOwner G id R x v = boundedOwner H id R y v := by
      intro v hv
      exact boundedOwner_eq_of_graph_view G H hG hH id hinj v R
        (nearby_view G H hG hH (ofLex e).1 1 R
          (view.restrict hG hH (by omega)) v hv) x y
        (fun w hw => by rw [hlabels w (le_trans
          (hG.dist_triangle (u := (ofLex e).1) (v := v) (w := w)) (by omega))])
    have hleft := endpoint_owner (ofLex e).1 (by simp)
    have hright := endpoint_owner (ofLex e).2 (by omega)
    have hoe : pairOwner (boundedOwner G id R x) ox e =
        pairOwner (boundedOwner H id R y) oy e := by
      simp only [pairOwner,hleft,hright,hdir e he (by simp) (by omega)]
    have owner_near : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
        G.dist (ofLex e).1 c ≤ R+1 := by
      intro c hc
      obtain hl | hr := pairOwner_eq_some_incident _ _ _ _ hc
      · have hn := ((boundedOwner_some_iff G id hinj R x _ _).mp hl).2
        rw [G.dist_comm] at hn
        omega
      · have hn := ((boundedOwner_some_iff G id hinj R x _ _).mp hr).2
        have ht := hG.dist_triangle (u := (ofLex e).1) (v := (ofLex e).2) (w := c)
        rw [G.dist_comm (u := (ofLex e).2) (v := c)] at ht
        omega
    have rootview : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
        SameGraphView G H c ((R+1)+R) := by
      intro c hc
      apply nearby_view G H hG hH (ofLex e).1 (R+1) ((R+1)+R) _ c (owner_near c hc)
      convert view using 1; omega
    have rootlabels : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
        ∀ w, G.dist c w ≤ (R+1)+R → x w = y w := by
      intro c hc w hw
      have hn := owner_near c hc
      exact hlabels w (le_trans
        (hG.dist_triangle (u := (ofLex e).1) (v := c) (w := w)) (by omega))
    apply boundedPairDecode_congr hq G H id R d x y ox oy e hedge hoe
    · intro c hc
      apply pairOwnedEdges_eq_of_graph_view G H hG hH id hinj c R (rootview c hc) x y
        (fun w hw => by rw [rootlabels c hc w hw]) ox oy
      intro p hp hl hr
      have hn := owner_near c hc
      exact hdir p hp
        (le_trans (hG.dist_triangle (u := (ofLex e).1) (v := c) (w := (ofLex p).1)) (by omega))
        (le_trans (hG.dist_triangle (u := (ofLex e).1) (v := c) (w := (ofLex p).2)) (by omega))
    · intro c hc
      exact boundedCell_eq_of_graph_view G H hG hH id hinj c R
        ((rootview c hc).restrict hG hH (by omega)) x y
        (fun w hw => by rw [rootlabels c hc w (by omega)])
    · intro c hc
      exact boundedSites_eq_of_graph_view G H hG hH id hinj c R
        ((rootview c hc).restrict hG hH (by omega)) x y
        (fun w hw => by rw [rootlabels c hc w (by omega)])
    · intro c hc
      exact boundedWord_eq_of_graph_view hq G H hG hH id hinj c R
        ((rootview c hc).restrict hG hH (by omega)) x y
        (fun w hw => rootlabels c hc w (by omega))
  · rw [boundedPairDecode_nonedge hq G id R d x ox e he,
      boundedPairDecode_nonedge hq H id R d y oy e (fun h => he (hedge.mpr h))]

end LocalDecompression.FiniteView
