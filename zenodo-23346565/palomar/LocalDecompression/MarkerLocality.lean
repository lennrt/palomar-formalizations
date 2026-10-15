module

public import LocalDecompression.GraphLayout
public import LocalDecompression.LocalView
public import LocalDecompression.GraphPresentation
public import LocalDecompression.Main

@[expose] public section

/-! Bounded marker selection across different marker sets.

The physical graph is fixed. Unlike fixed-marker-domain locality, these
lemmas permit the global zero-marker sets of the two inputs to differ. The
selector reads only zero markers in a bounded ball and returns `none` if
there is no visible marker. Coverage relates it to the global Voronoi owner.
These are finite geometric and label-dependence results, not an operational
cross-topology LOCAL semantics.
-/
namespace LocalDecompression.MarkerLocality

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The zero markers contained in the observed physical ball. -/
noncomputable def visibleMarkers {q : ℕ} (G : SimpleGraph V) (R : ℕ)
    (labels : V → Fin (q+1)) (v : V) : Finset V :=
  (closedBall G v R).filter (fun c => labels c = 0)

@[simp] theorem mem_visibleMarkers {q : ℕ} (G : SimpleGraph V) (R : ℕ)
    (labels : V → Fin (q+1)) (v c : V) :
    c ∈ visibleMarkers G R labels v ↔ G.dist v c ≤ R ∧ labels c = 0 := by
  simp [visibleMarkers, mem_closedBall]

theorem visibleMarkers_eq_filter {q : ℕ} (G : SimpleGraph V) (R : ℕ)
    (labels : V → Fin (q+1)) (v : V) :
    visibleMarkers G R labels v =
      (recognizedRoots labels).filter (fun c => G.dist c v ≤ R) := by
  ext c
  simp [recognizedRoots, G.dist_comm, and_comm]

/-- Distance-first, identifier-second selection from only the visible markers.
The empty-view case is total and explicitly returns no owner. -/
noncomputable def boundedOwner {q : ℕ} (G : SimpleGraph V) (id : V → ℕ) (R : ℕ)
    (labels : V → Fin (q+1)) (v : V) : Option V :=
  if h : (visibleMarkers G R labels v).Nonempty then
    some (owner G (visibleMarkers G R labels v) id h v)
  else none

/-- Coverage is a property of the actual zero labels, not of an independently
supplied root set. Connectedness is separately stated when distances are used. -/
def MarkerCover {q : ℕ} (G : SimpleGraph V) (R : ℕ) (labels : V → Fin (q+1)) : Prop :=
  ∀ v, ∃ c, labels c = 0 ∧ G.dist c v ≤ R

theorem visibleMarkers_nonempty {q : ℕ} (G : SimpleGraph V) (R : ℕ)
    (labels : V → Fin (q+1)) (v : V)
    (hcover : ∃ c, labels c = 0 ∧ G.dist c v ≤ R) :
    (visibleMarkers G R labels v).Nonempty := by
  obtain ⟨c,hc,hd⟩ := hcover
  exact ⟨c,(mem_visibleMarkers G R labels v c).mpr ⟨by simpa [G.dist_comm] using hd,hc⟩⟩

omit [DecidableEq V] in
theorem recognizedRoots_nonempty {q : ℕ} (G : SimpleGraph V) (R : ℕ)
    (labels : V → Fin (q+1)) (v : V)
    (hcover : ∃ c, labels c = 0 ∧ G.dist c v ≤ R) :
    (recognizedRoots labels).Nonempty := by
  obtain ⟨c,hc,_⟩ := hcover
  exact ⟨c,by simp [recognizedRoots,hc]⟩

/-- Changing any markers outside the observation radius cannot change the
bounded selector. Only marker status, not the nonzero payload, matters. -/
theorem boundedOwner_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1)) (v : V)
    (hagree : ∀ c, G.dist v c ≤ R → (x c = 0 ↔ y c = 0)) :
    boundedOwner G id R x v = boundedOwner G id R y v := by
  have he : visibleMarkers G R x v = visibleMarkers G R y v := by
    ext c
    simp only [mem_visibleMarkers]
    by_cases hc : G.dist v c ≤ R
    · simp only [hc, true_and, hagree c hc]
    · simp [hc]
  unfold boundedOwner
  rw [he]

/-- The bounded selector is radius-R label-local on a connected physical graph,
without any coverage or global-marker equality premise. -/
theorem boundedOwner_local {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R : ℕ) : LocalAt G R (fun v => v) (boundedOwner (q := q) G id R) := by
  intro x y v hagree
  apply boundedOwner_eq_of_marker_agreement
  intro c hc
  rw [hagree c ((within_iff_dist G hconn R v c).mpr hc)]

/-- Under local coverage, bounded selection equals the global nearest-root
assignment, even when distant markers are present. -/
theorem boundedOwner_eq_rootOwner {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (hne : (recognizedRoots labels).Nonempty) (v : V)
    (hcover : ∃ c, labels c = 0 ∧ G.dist c v ≤ R) :
    boundedOwner G id R labels v = some (rootOwner G (recognizedRoots labels) id hne v).val := by
  have hvisible := visibleMarkers_nonempty G R labels v hcover
  have hroot : ∃ c ∈ recognizedRoots labels, G.dist c v ≤ R := by
    obtain ⟨c,hc,hd⟩ := hcover
    exact ⟨c,by simp [recognizedRoots,hc],hd⟩
  have hs := owner_spec G (visibleMarkers G R labels v) id hvisible v
  have hs' : Voronoi G ((recognizedRoots labels).filter (fun c => G.dist c v ≤ R)) id
      (owner G (visibleMarkers G R labels v) id hvisible v) v := by
    rw [← visibleMarkers_eq_filter]
    exact hs
  have hg := (voronoi_local_roots G (recognizedRoots labels) id R v hroot _).mpr hs'
  have he := voronoi_unique G (recognizedRoots labels) id hinj hg
    (owner_spec G (recognizedRoots labels) id hne v)
  unfold boundedOwner
  rw [dite_eq_left hvisible]
  exact congrArg some he

/-- Owners from distinct global root sets coincide whenever the markers
agree locally and both inputs contain a visible root. -/
theorem rootOwner_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (x y : V → Fin (q+1)) (hx : (recognizedRoots x).Nonempty)
    (hy : (recognizedRoots y).Nonempty) (v : V)
    (hcoverx : ∃ c, x c = 0 ∧ G.dist c v ≤ R)
    (hcovery : ∃ c, y c = 0 ∧ G.dist c v ≤ R)
    (hagree : ∀ c, G.dist v c ≤ R → (x c = 0 ↔ y c = 0)) :
    (rootOwner G (recognizedRoots x) id hx v).val =
      (rootOwner G (recognizedRoots y) id hy v).val := by
  have he := boundedOwner_eq_of_marker_agreement G id R x y v hagree
  rw [boundedOwner_eq_rootOwner G id hinj R x hx v hcoverx,
    boundedOwner_eq_rootOwner G id hinj R y hy v hcovery] at he
  exact Option.some.inj he


omit [DecidableEq V] in
/-- Conversion to the root-set coverage interface used by Voronoi geometry. -/
theorem MarkerCover.roots {q : ℕ} {G : SimpleGraph V} {R : ℕ} {labels : V → Fin (q+1)}
    (hcover : MarkerCover G R labels) (v : V) :
    ∃ c ∈ recognizedRoots labels, G.dist c v ≤ R := by
  obtain ⟨c,hc,hd⟩ := hcover v
  exact ⟨c,by simp [recognizedRoots,hc],hd⟩

/-- A radius-R marker view at a nearby vertex is contained in the center's
radius-(S+R) marker view. The two global marker sets may be different. -/
theorem nearby_visibleMarkers_eq {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (R S : ℕ) (x y : V → Fin (q+1)) (center v : V) (hnear : G.dist center v ≤ S)
    (hagree : ∀ w, G.dist center w ≤ S+R → (x w = 0 ↔ y w = 0)) :
    visibleMarkers G R x v = visibleMarkers G R y v := by
  ext w
  simp only [mem_visibleMarkers]
  by_cases hw : G.dist v w ≤ R
  · have ht := hconn.dist_triangle (u := center) (v := v) (w := w)
    have hc : G.dist center w ≤ S+R := by omega
    simp only [hw,true_and,hagree w hc]
  · simp [hw]

/-- Bounded marker agreement determines every nearby Voronoi comparison,
without imposing equality of the global root sets. -/
theorem nearby_voronoi_iff {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R S : ℕ) (x y : V → Fin (q+1)) (center v c : V)
    (hnear : G.dist center v ≤ S)
    (hcoverx : ∃ w, x w = 0 ∧ G.dist w v ≤ R)
    (hcovery : ∃ w, y w = 0 ∧ G.dist w v ≤ R)
    (hagree : ∀ w, G.dist center w ≤ S+R → (x w = 0 ↔ y w = 0)) :
    Voronoi G (recognizedRoots x) id c v ↔ Voronoi G (recognizedRoots y) id c v := by
  apply voronoi_of_local_root_agreement G (recognizedRoots x) (recognizedRoots y) id R v
  · obtain ⟨w,hw,hd⟩ := hcoverx
    exact ⟨w,by simp [recognizedRoots,hw],hd⟩
  · obtain ⟨w,hw,hd⟩ := hcovery
    exact ⟨w,by simp [recognizedRoots,hw],hd⟩
  · simpa only [visibleMarkers_eq_filter] using
      nearby_visibleMarkers_eq G hconn R S x y center v hnear hagree

/-- The complete cell reconstructed from the actual marker set. -/
noncomputable def markerCell {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (labels : V → Fin (q+1)) (c : V) : Finset V :=
  cell G (recognizedRoots labels) id c

@[simp] theorem mem_markerCell {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (labels : V → Fin (q+1)) (c v : V) :
    v ∈ markerCell G id labels c ↔ Voronoi G (recognizedRoots labels) id c v :=
  mem_cell _ _ _ _ _

theorem markerCell_radius {q : ℕ} (G : SimpleGraph V) (id : V → ℕ) (R : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    {c v : V} (hv : v ∈ markerCell G id labels c) : G.dist c v ≤ R := by
  obtain ⟨w,hw,hd⟩ := hcover.roots v
  exact (voronoi_dist_le G (recognizedRoots labels) id
    ((mem_markerCell G id labels c v).mp hv) hw).trans hd

/-- The entire cell, including vertices beyond the initial query point, is
unchanged by arbitrary marker modifications outside radius 2R of its root. -/
theorem markerCell_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → (x w = 0 ↔ y w = 0)) :
    markerCell G id x c = markerCell G id y c := by
  have hxy : ∀ v, v ∈ markerCell G id x c → v ∈ markerCell G id y c := by
    intro v hv
    have hd := markerCell_radius G id R x hcoverx hv
    exact (mem_markerCell G id y c v).mpr
      ((nearby_voronoi_iff G hconn id R R x y c v c hd (hcoverx v) (hcovery v)
        (fun w hw => hagree w (by omega))).mp ((mem_markerCell G id x c v).mp hv))
  have hyx : ∀ v, v ∈ markerCell G id y c → v ∈ markerCell G id x c := by
    intro v hv
    have hd := markerCell_radius G id R y hcovery hv
    exact (mem_markerCell G id x c v).mpr
      ((nearby_voronoi_iff G hconn id R R x y c v c hd (hcoverx v) (hcovery v)
        (fun w hw => hagree w (by omega))).mpr ((mem_markerCell G id y c v).mp hv))
  exact Finset.ext (fun v => ⟨hxy v,hyx v⟩)

/-- Actual nonroot storage vertices, selected from the decoded marker cell. -/
noncomputable def markerSites {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (labels : V → Fin (q+1)) (c : V) : Finset V :=
  (markerCell G id labels c).erase c

theorem markerSites_eq_of_marker_agreement {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → (x w = 0 ↔ y w = 0)) :
    markerSites G id x c = markerSites G id y c := by
  unfold markerSites
  rw [markerCell_eq_of_marker_agreement G hconn id R x y hcoverx hcovery c hagree]


/-- A visible candidate's score is its distance in the actual induced view.
Thus the bounded selector's comparisons do not need unseen graph vertices. -/
theorem visible_marker_distance_in_view {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (R : ℕ) (labels : V → Fin (q+1)) (v c : V) (hc : c ∈ visibleMarkers G R labels v) :
    ∃ hcv : G.dist v c ≤ R,
      (G.induce {w | G.dist v w ≤ R}).dist ⟨v,by simp⟩ ⟨c,hcv⟩ = G.dist c v := by
  have hcv := ((mem_visibleMarkers G R labels v c).mp hc).1
  exact ⟨hcv,by simpa only [G.dist_comm] using view_center_dist G hconn v R c hcv⟩

/-- Marker agreement in the center's enlarged view fixes bounded owner queries
at all nearby vertices, regardless of distant changes in the marker sets. -/
theorem nearby_boundedOwner_eq {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R S : ℕ) (x y : V → Fin (q+1)) (center v : V)
    (hnear : G.dist center v ≤ S)
    (hagree : ∀ w, G.dist center w ≤ S+R → (x w = 0 ↔ y w = 0)) :
    boundedOwner G id R x v = boundedOwner G id R y v := by
  unfold boundedOwner
  rw [nearby_visibleMarkers_eq G hconn R S x y center v hnear hagree]

/-- The actual nonroot labels in a reconstructed packet, retaining vertex IDs
through the vertex coordinate. -/
noncomputable def packetRecords {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (labels : V → Fin (q+1)) (c : V) : Finset (V × Fin (q+1)) :=
  (markerSites G id labels c).image (fun v => (v, labels v))

/-- Vertex-tagged packet records determine both the storage sites and the
label at each site; this is the input required by the ordered packet reader. -/
theorem packetRecords_eq_iff {q : ℕ} (G : SimpleGraph V) (id : V → ℕ)
    (x y : V → Fin (q+1)) (c : V) :
    packetRecords G id x c = packetRecords G id y c ↔
      markerSites G id x c = markerSites G id y c ∧
      ∀ v ∈ markerSites G id x c, x v = y v := by
  have forward : ∀ (a b : V → Fin (q+1)),
      packetRecords G id a c = packetRecords G id b c →
      ∀ v ∈ markerSites G id a c, v ∈ markerSites G id b c ∧ a v = b v := by
    intro a b hab v hv
    have hm : (v,a v) ∈ packetRecords G id a c := Finset.mem_image.mpr ⟨v,hv,rfl⟩
    rw [hab] at hm
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hm
    have hwv : w = v := congrArg Prod.fst he
    subst w
    exact ⟨hw,(congrArg Prod.snd he).symm⟩
  constructor
  · intro h
    exact ⟨Finset.ext (fun v => ⟨fun hv => (forward x y h v hv).1,
      fun hv => (forward y x h.symm v hv).1⟩),fun v hv => (forward x y h v hv).2⟩
  · rintro ⟨hs,hl⟩
    unfold packetRecords
    rw [← hs]
    apply Finset.image_congr
    intro v hv
    exact congrArg (fun z => (v,z)) (hl v hv)

theorem packetRecords_eq_of_label_agreement {q : ℕ} (G : SimpleGraph V) (hconn : G.Connected)
    (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → x w = y w) :
    packetRecords G id x c = packetRecords G id y c := by
  have hs := markerSites_eq_of_marker_agreement G hconn id R x y hcoverx hcovery c
    (fun w hw => by rw [hagree w hw])
  unfold packetRecords
  rw [← hs]
  apply Finset.image_congr
  intro v hv
  have hc : v ∈ markerCell G id x c := (Finset.mem_erase.mp hv).2
  have hd := markerCell_radius G id R x hcoverx hc
  exact congrArg (fun z => (v,z)) (hagree v (by omega))


section Edges
variable [LinearOrder V]

/-- All original graph edges incident to the reconstructed cell, including
its internal edges. Their endpoints retain the physical graph's vertex IDs. -/
noncomputable def cellIncidentEdges {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (id : V → ℕ) (labels : V → Fin (q+1)) (c : V) : Finset (GraphEdge G) :=
  Finset.univ.filter (fun e => (graphPresentation G).left e ∈ markerCell G id labels c ∨
    (graphPresentation G).right e ∈ markerCell G id labels c)

@[simp] theorem mem_cellIncidentEdges {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (id : V → ℕ) (labels : V → Fin (q+1)) (c : V) (e : GraphEdge G) :
    e ∈ cellIncidentEdges G id labels c ↔
      (graphPresentation G).left e ∈ markerCell G id labels c ∨
      (graphPresentation G).right e ∈ markerCell G id labels c := by
  simp [cellIncidentEdges]

theorem cellIncidentEdges_eq {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R → (x w = 0 ↔ y w = 0)) :
    cellIncidentEdges G id x c = cellIncidentEdges G id y c := by
  unfold cellIncidentEdges
  rw [markerCell_eq_of_marker_agreement G hconn id R x y hcoverx hcovery c hagree]

theorem incident_endpoints_near {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hcover : MarkerCover G R labels) (c : V) (e : GraphEdge G)
    (he : e ∈ cellIncidentEdges G id labels c) :
    G.dist c ((graphPresentation G).left e) ≤ R+1 ∧
      G.dist c ((graphPresentation G).right e) ≤ R+1 := by
  have hedge := SimpleGraph.dist_eq_one_iff_adj.mpr (graphPresentation_adj G e)
  rcases (mem_cellIncidentEdges G id labels c e).mp he with hl | hr
  · have hd := markerCell_radius G id R labels hcover hl
    have ht := hconn.dist_triangle (u := c) (v := (graphPresentation G).left e)
      (w := (graphPresentation G).right e)
    constructor <;> omega
  · have hd := markerCell_radius G id R labels hcover hr
    have ht := hconn.dist_triangle (u := c) (v := (graphPresentation G).right e)
      (w := (graphPresentation G).left e)
    rw [G.dist_comm (u := (graphPresentation G).right e)] at ht
    constructor <;> omega

/-- Original incident edges together with both recovered endpoint-cell roots.
This contains the boundary information needed to form parallel quotient fibers.
Internal edges remain present with equal endpoint owners. -/
noncomputable def cellEdgeRecords {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V) :
    Finset (GraphEdge G × Option V × Option V) :=
  (cellIncidentEdges G id labels c).image (fun e =>
    (e, boundedOwner G id R labels ((graphPresentation G).left e),
      boundedOwner G id R labels ((graphPresentation G).right e)))

/-- Under marker coverage, the bounded endpoint records are exactly the
global Voronoi partition records of the original incident edges. -/
theorem cellEdgeRecords_eq_global {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    (hne : (recognizedRoots labels).Nonempty) (c : V) :
    cellEdgeRecords G id R labels c =
      (cellIncidentEdges G id labels c).image (fun e =>
        (e, some (rootOwner G (recognizedRoots labels) id hne
            ((graphPresentation G).left e)).val,
          some (rootOwner G (recognizedRoots labels) id hne
            ((graphPresentation G).right e)).val)) := by
  unfold cellEdgeRecords
  apply Finset.image_congr
  intro e _
  dsimp only
  rw [boundedOwner_eq_rootOwner G id hinj R labels hne _ (hcover _),
    boundedOwner_eq_rootOwner G id hinj R labels hne _ (hcover _)]

/-- Radius-(2R+2) agreement determines all incident-edge and boundary-owner
records, even when the two marker sets differ arbitrarily outside that view. -/
theorem cellEdgeRecords_eq_of_marker_agreement {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 2*R+2 → (x w = 0 ↔ y w = 0)) :
    cellEdgeRecords G id R x c = cellEdgeRecords G id R y c := by
  have hs := cellIncidentEdges_eq G hconn id R x y hcoverx hcovery c
    (fun w hw => hagree w (by omega))
  unfold cellEdgeRecords
  rw [← hs]
  apply Finset.image_congr
  intro e he
  obtain ⟨hl,hr⟩ := incident_endpoints_near G hconn id R x hcoverx c e he
  have hlo := nearby_boundedOwner_eq G hconn id R (R+1) x y c
    ((graphPresentation G).left e) hl (fun w hw => hagree w (by omega))
  have hro := nearby_boundedOwner_eq G hconn id R (R+1) x y c
    ((graphPresentation G).right e) hr (fun w hw => hagree w (by omega))
  dsimp only
  rw [hlo,hro]

/-- The radius used in the paper: marker coverage at 2r and agreement at
4r+2 determine the actual cell sites and all original incident-edge records. -/
theorem cell_data_four_r {q : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (id : V → ℕ) (r : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G (2*r) x) (hcovery : MarkerCover G (2*r) y) (c : V)
    (hagree : ∀ w, G.dist c w ≤ 4*r+2 → (x w = 0 ↔ y w = 0)) :
    markerSites G id x c = markerSites G id y c ∧
      cellEdgeRecords G id (2*r) x c = cellEdgeRecords G id (2*r) y c := by
  constructor
  · exact markerSites_eq_of_marker_agreement G hconn id (2*r) x y hcoverx hcovery c
      (fun w hw => hagree w (by omega))
  · exact cellEdgeRecords_eq_of_marker_agreement G hconn id (2*r) x y hcoverx hcovery c
      (fun w hw => hagree w (by omega))

end Edges
end LocalDecompression.MarkerLocality

namespace LocalDecompression.MarkerLocality
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Increasing enumeration preserves a packet when the actual site predicate
and its labels agree. Heterogeneous equality accounts only for the two
definitionally different presentations of the same number of sites. -/
theorem ordered_reader_congr {q : ℕ} (hq : 0 < q)
    (P Q : V → Prop) [decP : DecidablePred P] [decQ : DecidablePred Q]
    (x y : V → Fin (q+1)) (hpred : P = Q)
    (hlabels : ∀ v, P v → x v = y v) :
    HEq (fun i : Fin (Fintype.card {v // P v}) =>
      Reduction.unmark hq (x ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).val))
      (fun i : Fin (Fintype.card {v // Q v}) =>
      Reduction.unmark hq (y ((Fintype.orderIsoFinOfCardEq {v // Q v} rfl) i).val)) := by
  subst Q
  have hdec : decP = decQ := Subsingleton.elim _ _
  subst decQ
  apply heq_of_eq
  funext i
  apply congrArg (Reduction.unmark hq)
  exact hlabels _ ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).property

/-- The existing positional packet reader agrees across different partition
types whenever the selected cells have the same actual nonroot sites and
labels. No new decoding rule or arbitrary site bijection is introduced. -/
theorem packet_reader_sites_congr {C D : Type*} [DecidableEq C] [DecidableEq D]
    {q : ℕ} (hq : 0 < q)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (part' : V → D) (root' : D → V) (hroot' : ∀ c, part' (root' c) = c)
    (x y : V → Fin (q+1)) (c : C) (c' : D)
    (hsite : ∀ v, (part v = c ∧ v ≠ root c) ↔
      (part' v = c' ∧ v ≠ root' c'))
    (hlabels : ∀ v, part v = c ∧ v ≠ root c → x v = y v) :
    HEq (Reduction.wordsOfLabels hq (Reduction.digitLayout part root hroot) x c)
      (Reduction.wordsOfLabels hq (Reduction.digitLayout part' root' hroot') y c') := by
  change HEq
    (fun i : Fin (Fintype.card (Sites part root c)) =>
      Reduction.unmark hq (x ((Fintype.orderIsoFinOfCardEq (Sites part root c) rfl) i).val))
    (fun i : Fin (Fintype.card (Sites part' root' c')) =>
      Reduction.unmark hq (y ((Fintype.orderIsoFinOfCardEq (Sites part' root' c') rfl) i).val))
  exact ordered_reader_congr hq _ _ x y (funext (fun v => propext (hsite v))) hlabels

/-- The actual advice extractor is unchanged when the selected ordered
packet is unchanged across different partition types. -/
theorem packet_advice_sites_congr {C D : Type*} [DecidableEq C] [DecidableEq D]
    {q : ℕ} (hq : 0 < q)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (part' : V → D) (root' : D → V) (hroot' : ∀ c, part' (root' c) = c)
    (x y : V → Fin (q+1)) (c : C) (c' : D)
    (hsite : ∀ v, (part v = c ∧ v ≠ root c) ↔
      (part' v = c' ∧ v ≠ root' c'))
    (hlabels : ∀ v, part v = c ∧ v ≠ root c → x v = y v) :
    Reduction.decodeAdvice
      (Reduction.wordsOfLabels hq (Reduction.digitLayout part root hroot) x) c =
    Reduction.decodeAdvice
      (Reduction.wordsOfLabels hq (Reduction.digitLayout part' root' hroot') y) c' := by
  have hp := packet_reader_sites_congr hq part root hroot part' root' hroot' x y c c'
    hsite hlabels
  have hc : Fintype.card (Sites part root c) = Fintype.card (Sites part' root' c') :=
    Fintype.card_congr (Equiv.subtypeEquivRight hsite)
  have ha : ∀ {m n : ℕ}, m = n → ∀ (w : Fin m → Fin q) (w' : Fin n → Fin q),
      HEq w w' → blockAdvice w = blockAdvice w' := by
    intro m n he w w' hw
    subst n
    exact congrArg blockAdvice (eq_of_heq hw)
  exact ha hc _ _ hp

/-- Equality of the existing ordered packet reader across distinct global
marker sets. The common candidate root is a marker in both inputs, both
inputs are R-covered, and actual labels agree only in its radius-2R ball. -/
theorem marker_packet_reader_eq {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y)
    (c : V) (hcx : c ∈ recognizedRoots x) (hcy : c ∈ recognizedRoots y)
    (hagree : ∀ v, G.dist c v ≤ 2*R → x v = y v) :
    HEq
      (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots x) id ⟨c,hcx⟩) Subtype.val
          (rootOwner_root G hconn (recognizedRoots x) id ⟨c,hcx⟩ hinj)) x ⟨c,hcx⟩)
      (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots y) id ⟨c,hcy⟩) Subtype.val
          (rootOwner_root G hconn (recognizedRoots y) id ⟨c,hcy⟩ hinj)) y ⟨c,hcy⟩) := by
  have hp := packetRecords_eq_of_label_agreement G hconn id R x y hcoverx hcovery c hagree
  obtain ⟨hs,hl⟩ := (packetRecords_eq_iff G id x y c).mp hp
  apply packet_reader_sites_congr
  · intro v
    rw [rootOwner_eq_iff G (recognizedRoots x) id ⟨c,hcx⟩ hinj,
      rootOwner_eq_iff G (recognizedRoots y) id ⟨c,hcy⟩ hinj]
    have hm : v ∈ markerSites G id x c ↔ v ∈ markerSites G id y c := by rw [hs]
    simpa only [markerSites, Finset.mem_erase, mem_markerCell, and_comm] using hm
  · intro v hv
    have hm : v ∈ markerCell G id x c := (mem_markerCell G id x c v).mpr
      ((rootOwner_eq_iff G (recognizedRoots x) id ⟨c,hcx⟩ hinj v ⟨c,hcx⟩).mp hv.1)
    exact hl v (Finset.mem_erase.mpr ⟨hv.2,hm⟩)

/-- The advice actually used by `vertexDecode` agrees across the two marker
sets under the same local packet hypotheses. This is a packet-reader result;
it does not assert coherence of orientation decoders on different quotients. -/
theorem marker_packet_advice_eq {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q+1))
    (hcoverx : MarkerCover G R x) (hcovery : MarkerCover G R y)
    (c : V) (hcx : c ∈ recognizedRoots x) (hcy : c ∈ recognizedRoots y)
    (hagree : ∀ v, G.dist c v ≤ 2*R → x v = y v) :
    Reduction.decodeAdvice
      (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots x) id ⟨c,hcx⟩) Subtype.val
          (rootOwner_root G hconn (recognizedRoots x) id ⟨c,hcx⟩ hinj)) x) ⟨c,hcx⟩ =
    Reduction.decodeAdvice
      (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots y) id ⟨c,hcy⟩) Subtype.val
          (rootOwner_root G hconn (recognizedRoots y) id ⟨c,hcy⟩ hinj)) y) ⟨c,hcy⟩ := by
  have hp := packetRecords_eq_of_label_agreement G hconn id R x y hcoverx hcovery c hagree
  obtain ⟨hs,hl⟩ := (packetRecords_eq_iff G id x y c).mp hp
  apply packet_advice_sites_congr
  · intro v
    rw [rootOwner_eq_iff G (recognizedRoots x) id ⟨c,hcx⟩ hinj,
      rootOwner_eq_iff G (recognizedRoots y) id ⟨c,hcy⟩ hinj]
    have hm : v ∈ markerSites G id x c ↔ v ∈ markerSites G id y c := by rw [hs]
    simpa only [markerSites, Finset.mem_erase, mem_markerCell, and_comm] using hm
  · intro v hv
    have hm : v ∈ markerCell G id x c := (mem_markerCell G id x c v).mpr
      ((rootOwner_eq_iff G (recognizedRoots x) id ⟨c,hcx⟩ hinj v ⟨c,hcx⟩).mp hv.1)
    exact hl v (Finset.mem_erase.mpr ⟨hv.2,hm⟩)

end LocalDecompression.MarkerLocality
