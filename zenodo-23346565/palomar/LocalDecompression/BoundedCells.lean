module

public import LocalDecompression.MarkerLocality

@[expose] public section

/-! Geometry of the existing bounded marker selector on arbitrary labels.

No marker coverage or separation is assumed. Each selected cell is the
radius-truncation of an identifier-tiebroken Voronoi cell, and the no-marker
case remains explicit. Geometric statements assume a connected physical
component because natural graph distance is totalized on unreachable pairs.
This module does not replace the selector or assert operational LOCAL
semantics for a complete decoder.
-/
namespace LocalDecompression.BoundedCells
open MarkerLocality

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The existing bounded selector returns no owner exactly when its finite
observation contains no marker. No assumption is made on the labels. -/
theorem boundedOwner_none_iff {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (v : V) :
    boundedOwner G id R labels v = none ↔ visibleMarkers G R labels v = ∅ := by
  unfold boundedOwner
  by_cases h : (visibleMarkers G R labels v).Nonempty
  · simp [h, h.ne_empty]
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

/-- The empty-output case can equivalently be read as absence of every
zero marker within the distance threshold. -/
theorem boundedOwner_none_iff_no_marker {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (v : V) :
    boundedOwner G id R labels v = none ↔
      ¬ ∃ c, labels c = 0 ∧ G.dist c v ≤ R := by
  rw [boundedOwner_none_iff, ← Finset.not_nonempty_iff_eq_empty]
  simp only [Finset.Nonempty, mem_visibleMarkers, G.dist_comm, and_comm]

/-- A marker-free input has no selected owner anywhere, including when the
graph is empty. No artificial root is inserted by the selector. -/
theorem boundedOwner_of_no_markers {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1))
    (hmarkers : recognizedRoots labels = ∅) (v : V) :
    boundedOwner G id R labels v = none := by
  apply (boundedOwner_none_iff_no_marker G id R labels v).mpr
  rintro ⟨c,hc,_⟩
  have hm : c ∈ recognizedRoots labels := by simp [recognizedRoots,hc]
  simp [hmarkers] at hm

/-- Bounded selection is exactly global nearest-marker selection truncated
at radius R. It requires no global marker coverage or marker separation. -/
theorem boundedOwner_some_iff {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1)) (v c : V) :
    boundedOwner G id R labels v = some c ↔
      Voronoi G (recognizedRoots labels) id c v ∧ G.dist c v ≤ R := by
  constructor
  · intro h
    unfold boundedOwner at h
    split_ifs at h with hvisible
    · have he := Option.some.inj h
      have hs := owner_spec G (visibleMarkers G R labels v) id hvisible v
      rw [he] at hs
      obtain ⟨hd,hmarker⟩ := (mem_visibleMarkers G R labels v c).mp hs.1
      have hd' : G.dist c v ≤ R := by simpa only [G.dist_comm] using hd
      have hc : c ∈ recognizedRoots labels := by simp [recognizedRoots,hmarker]
      refine ⟨?_,hd'⟩
      apply (voronoi_local_roots G (recognizedRoots labels) id R v ⟨c,hc,hd'⟩ c).mpr
      rw [← visibleMarkers_eq_filter]
      exact hs
  · rintro ⟨hc,hd⟩
    have hmarker : labels c = 0 := by simpa [recognizedRoots] using hc.1
    have hcover : ∃ w, labels w = 0 ∧ G.dist w v ≤ R := ⟨c,hmarker,hd⟩
    rw [boundedOwner_eq_rootOwner G id hinj R labels ⟨c,hc.1⟩ v hcover]
    have he := (rootOwner_eq_iff G (recognizedRoots labels) id ⟨c,hc.1⟩ hinj v
      ⟨c,hc.1⟩).mpr hc
    exact congrArg (fun z => some z.val) he

/-- Every zero marker selects itself, even when other vertices have no
visible marker and no global coverage condition holds. -/
theorem boundedOwner_self_iff_marker {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) (c : V) :
    boundedOwner G id R labels c = some c ↔ labels c = 0 := by
  rw [boundedOwner_some_iff G id hinj R labels c c]
  constructor
  · rintro ⟨hc,_⟩
    simpa [recognizedRoots] using hc.1
  · intro hc
    exact ⟨voronoi_self G hconn (recognizedRoots labels) id
      (by simp [recognizedRoots,hc]),by simp⟩

/-- Along every geodesic from a selected marker to its vertex, the selected
marker remains the same. Radius truncation does not break these routes. -/
theorem boundedOwner_on_geodesic {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) {c v w : V}
    (howner : boundedOwner G id R labels v = some c)
    (hgeo : G.dist c v = G.dist c w + G.dist w v) :
    boundedOwner G id R labels w = some c := by
  obtain ⟨hv,hd⟩ := (boundedOwner_some_iff G id hinj R labels v c).mp howner
  exact (boundedOwner_some_iff G id hinj R labels w c).mpr
    ⟨voronoi_on_geodesic G hconn (recognizedRoots labels) id hv hgeo,by omega⟩

/-- An actual shortest path, of length at most R, connects each selected
vertex to its marker and stays entirely within that selected cell. -/
theorem boundedOwner_path {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) {c v : V}
    (howner : boundedOwner G id R labels v = some c) :
    ∃ p : G.Walk c v, p.IsPath ∧ p.length = G.dist c v ∧ p.length ≤ R ∧
      ∀ w ∈ p.support, boundedOwner G id R labels w = some c := by
  obtain ⟨hv,hd⟩ := (boundedOwner_some_iff G id hinj R labels v c).mp howner
  obtain ⟨p,hpath,hp,hcell⟩ := voronoi_path G hconn (recognizedRoots labels) id hv
  refine ⟨p,hpath,hp,by omega,?_⟩
  intro w hw
  apply (boundedOwner_some_iff G id hinj R labels w c).mpr
  refine ⟨hcell w hw,?_⟩
  have hdist := SimpleGraph.dist_le (p.takeUntil w hw)
  have hlen := p.length_takeUntil_le_length hw
  omega

/-- The actual finite fiber of the existing Option-valued bounded selector.
Vertices returning `none` are not placed in any selected cell. -/
noncomputable def boundedCell {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c : V) : Finset V :=
  Finset.univ.filter (fun v => boundedOwner G id R labels v = some c)

@[simp] theorem mem_boundedCell {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c v : V) :
    v ∈ boundedCell G id R labels c ↔ boundedOwner G id R labels v = some c := by
  simp [boundedCell]

/-- A selected cell is exactly the global Voronoi cell intersected with the
root's radius-R ball. Coverage is not needed for this truncation identity. -/
theorem boundedCell_eq_inter {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1)) (c : V) :
    boundedCell G id R labels c = markerCell G id labels c ∩ closedBall G c R := by
  ext v
  simp only [mem_boundedCell, Finset.mem_inter, mem_markerCell, mem_closedBall,
    boundedOwner_some_iff G id hinj R labels v c]

theorem boundedCell_radius {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1)) {c v : V}
    (hv : v ∈ boundedCell G id R labels c) : G.dist c v ≤ R :=
  ((boundedOwner_some_iff G id hinj R labels v c).mp
    ((mem_boundedCell G id R labels c v).mp hv)).2

/-- Every selected cell has a degree-only size bound, including on malformed
inputs with uncovered vertices or roots arbitrarily close to one another. -/
theorem boundedCell_card_upper {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R Δ : ℕ) (hdegree : ∀ v, G.degree v ≤ Δ) (labels : V → Fin (q+1)) (c : V) :
    (boundedCell G id R labels c).card ≤ (Δ+1)^R := by
  apply (Finset.card_le_card (show boundedCell G id R labels c ⊆ closedBall G c R from ?_)).trans
    (closedBall_card_upper G hconn Δ hdegree c R)
  intro v hv
  exact (mem_closedBall G c v R).mpr (boundedCell_radius G id hinj R labels hv)

/-- A selected cell is nonempty exactly when its named root is an actual
zero marker. Nonmarkers cannot acquire a spurious selected cell. -/
theorem boundedCell_nonempty_iff_marker {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) (c : V) :
    (boundedCell G id R labels c).Nonempty ↔ labels c = 0 := by
  constructor
  · rintro ⟨v,hv⟩
    have hc := ((boundedOwner_some_iff G id hinj R labels v c).mp
      ((mem_boundedCell G id R labels c v).mp hv)).1.1
    simpa [recognizedRoots] using hc
  · intro hc
    exact ⟨c,(mem_boundedCell G id R labels c c).mpr
      ((boundedOwner_self_iff_marker G hconn id hinj R labels c).mpr hc)⟩

/-- The bounded route also exists as a path in the actual induced cell
graph, with the same geodesic length and hence at most R edges. -/
theorem boundedCell_induced_path {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) {c v : V}
    (hv : v ∈ boundedCell G id R labels c) :
    ∃ hc : c ∈ boundedCell G id R labels c,
      ∃ p : (G.induce {w | w ∈ boundedCell G id R labels c}).Walk ⟨c,hc⟩ ⟨v,hv⟩,
        p.IsPath ∧ p.length = G.dist c v ∧ p.length ≤ R := by
  obtain ⟨p,_,hp,hr,hs⟩ := boundedOwner_path G hconn id hinj R labels
    ((mem_boundedCell G id R labels c v).mp hv)
  have hS : ∀ w ∈ p.support, w ∈ boundedCell G id R labels c := by
    intro w hw
    exact (mem_boundedCell G id R labels c w).mpr (hs w hw)
  have hc := hS c p.start_mem_support
  have hd := induced_dist_eq_of_geodesic G {w | w ∈ boundedCell G id R labels c}
    hc hv p hp hS
  obtain ⟨t,ht,hlen⟩ :=
    (p.induce {w | w ∈ boundedCell G id R labels c} hS).reachable.exists_path_of_dist
  refine ⟨hc,t,ht,hlen.trans hd,?_⟩
  calc
    t.length = G.dist c v := hlen.trans hd
    _ ≤ R := by omega

/-- Complete bounded cells are unaffected by changes of marker status
outside radius 2R of the named root. Neither input needs global coverage. -/
theorem boundedCell_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (x y : V → Fin (q+1)) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → (x w = 0 ↔ y w = 0)) :
    boundedCell G id R x c = boundedCell G id R y c := by
  ext v
  by_cases hd : G.dist c v ≤ R
  · have ho := nearby_boundedOwner_eq G hconn id R R x y c v hd
      (fun w hw => hagree w (by omega))
    simp only [mem_boundedCell,ho]
  · have hx : v ∉ boundedCell G id R x c :=
      fun hv => hd (boundedCell_radius G id hinj R x hv)
    have hy : v ∉ boundedCell G id R y c :=
      fun hv => hd (boundedCell_radius G id hinj R y hv)
    simp only [hx,hy]

/-- The actual nonroot storage sites of a bounded cell. -/
noncomputable def boundedSites {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c : V) : Finset V :=
  (boundedCell G id R labels c).erase c

@[simp] theorem mem_boundedSites {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (R : ℕ) (labels : V → Fin (q+1)) (c v : V) :
    v ∈ boundedSites G id R labels c ↔
      v ≠ c ∧ boundedOwner G id R labels v = some c := by
  simp only [boundedSites, Finset.mem_erase, mem_boundedCell]

/-- Even on uncovered inputs, the complete nonroot site set is fixed by
the root's radius-2R marker view. -/
theorem boundedSites_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (x y : V → Fin (q+1)) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → (x w = 0 ↔ y w = 0)) :
    boundedSites G id R x c = boundedSites G id R y c := by
  unfold boundedSites
  rw [boundedCell_eq_of_marker_agreement G hconn id hinj R x y c hagree]

end LocalDecompression.BoundedCells
