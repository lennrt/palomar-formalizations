module
public import LocalDecompression.FiniteView

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section

namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Visible markers depend only on the rooted labelled physical view, across
changes of topology and of the global marker set. -/
theorem visibleMarkers_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (v : V) (R : ℕ) (view : SameGraphView G H v R)
    (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist v w ≤ R → (x w = 0 ↔ y w = 0)) :
    visibleMarkers G R x v = visibleMarkers H R y v := by
  ext w
  simp only [mem_visibleMarkers]
  constructor
  · rintro ⟨hd,hx⟩
    exact ⟨(view.vertices w).mp hd, (hlabels w hd).mp hx⟩
  · rintro ⟨hd,hy⟩
    have hd' := (view.vertices w).mpr hd
    exact ⟨hd', (hlabels w hd').mpr hy⟩

/-- The total nearest-marker selector is uniform across physical graphs.
Neither graph needs marker coverage or separation. -/
theorem boundedOwner_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (v : V) (R : ℕ)
    (view : SameGraphView G H v R) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist v w ≤ R → (x w = 0 ↔ y w = 0)) :
    boundedOwner G id R x v = boundedOwner H id R y v := by
  have he := visibleMarkers_eq_of_graph_view G H v R view x y hlabels
  have hdist : ∀ w ∈ visibleMarkers H R y v, G.dist w v = H.dist w v := by
    intro w hw
    rw [← he] at hw
    have hd := (mem_visibleMarkers G R x v w).mp hw
    simpa only [G.dist_comm, H.dist_comm] using
      center_distance_eq G H hG hH v R view w hd.1
  unfold boundedOwner
  rw [he]
  split_ifs with hne
  · congr 1
    symm
    apply (owner_eq_iff H (visibleMarkers H R y v) id hne hinj v _).mpr
    have hs := owner_spec G (visibleMarkers H R y v) id hne v
    refine ⟨hs.1, ?_⟩
    intro w hw
    have hh := hs.2 w hw
    rwa [hdist _ hs.1, hdist w hw] at hh
  · rfl

/-- The complete truncated cell is determined by the radius-2R physical
view. Outside topology and all marker information beyond that view can vary. -/
theorem boundedCell_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c (R+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ R+R → (x w = 0 ↔ y w = 0)) :
    boundedCell G id R x c = boundedCell H id R y c := by
  have hball : ∀ v, G.dist c v ≤ R ↔ H.dist c v ≤ R := by
    intro v
    have ht := nearby_within_iff G H hG hH c R R view (u := c) (v := v) (by simp)
    simpa only [within_iff_dist G hG, within_iff_dist H hH] using ht
  ext v
  by_cases hd : G.dist c v ≤ R
  · have nearview := nearby_view G H hG hH c R R view v hd
    have ho := boundedOwner_eq_of_graph_view G H hG hH id hinj v R nearview x y
      (fun w hw => hlabels w (le_trans (hG.dist_triangle (u := c) (v := v) (w := w))
        (by omega)))
    simp only [mem_boundedCell, ho]
  · have hx : v ∉ boundedCell G id R x c :=
      fun hv => hd (boundedCell_radius G id hinj R x hv)
    have hy : v ∉ boundedCell H id R y c :=
      fun hv => hd ((hball v).mpr (boundedCell_radius H id hinj R y hv))
    simp only [hx, hy]

/-- The physical-view result applies to the actual nonroot storage sites. -/
theorem boundedSites_eq_of_graph_view {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c (R+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ R+R → (x w = 0 ↔ y w = 0)) :
    boundedSites G id R x c = boundedSites H id R y c := by
  unfold boundedSites
  rw [boundedCell_eq_of_graph_view G H hG hH id hinj c R view x y hlabels]

end LocalDecompression.FiniteView

namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket
variable {V : Type*} [Fintype V] [LinearOrder V]

omit [Fintype V] in
private theorem ordered_reader_graph_congr {q : ℕ} (hq : 0 < q)
    (P Q : V → Prop) [fp : Fintype {v // P v}] [fq : Fintype {v // Q v}]
    (x y : V → Fin (q+1)) (hpred : P = Q)
    (hlabels : ∀ v, P v → x v = y v) :
    HEq (fun i : Fin (Fintype.card {v // P v}) =>
      Reduction.unmark hq (x ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).val))
      (fun i : Fin (Fintype.card {v // Q v}) =>
      Reduction.unmark hq (y ((Fintype.orderIsoFinOfCardEq {v // Q v} rfl) i).val)) := by
  subst Q
  have hf : fp = fq := Subsingleton.elim _ _
  subst fq
  apply heq_of_eq
  funext i
  exact congrArg (Reduction.unmark hq)
    (hlabels _ ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).property)

/-- Equal physical radius-2R views determine the whole ordered packet,
including its length, across both topology and marker-set changes. -/
theorem boundedWord_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c (R+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ R+R → x w = y w) :
    HEq (boundedWord hq G id R x c) (boundedWord hq H id R y c) := by
  apply ordered_reader_graph_congr
  · have hs := boundedSites_eq_of_graph_view G H hG hH id hinj c R view x y
      (fun w hw => by rw [hlabels w hw])
    exact funext (fun w => propext (by rw [hs]))
  · intro v hv
    have hd := boundedCell_radius G id hinj R x (Finset.mem_erase.mp hv).2
    exact hlabels v (by omega)

/-- Total packet arithmetic is uniform across physical graphs, without
requiring marker coverage, separation, or valid encoded payloads. -/
theorem boundedValue_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c (R+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ R+R → x w = y w) :
    boundedValue hq G id R x c = boundedValue hq H id R y c := by
  have hword := boundedWord_eq_of_graph_view hq G H hG hH id hinj c R view x y hlabels
  have hs := boundedSites_eq_of_graph_view G H hG hH id hinj c R view x y
    (fun w hw => by rw [hlabels w hw])
  have hc : Fintype.card {v // v ∈ boundedSites G id R x c} =
      Fintype.card {v // v ∈ boundedSites H id R y c} := by rw [hs]
  have hcongr : ∀ {m n : ℕ}, m = n → ∀ (w : Fin m → Fin q) (w' : Fin n → Fin q),
      HEq w w' → (finFunctionFinEquiv w).val = (finFunctionFinEquiv w').val := by
    intro m n he w w' hw
    subst n
    exact congrArg (fun z => (finFunctionFinEquiv z).val) (eq_of_heq hw)
  exact hcongr hc _ _ hword

/-- The actual orientation-advice reader depends only on the same bounded
physical view even when global topology and marker sets differ. -/
theorem boundedAdvice_eq_of_graph_view {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R : ℕ)
    (view : SameGraphView G H c (R+R)) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ R+R → x w = y w) :
    boundedAdvice hq G id R x c = boundedAdvice hq H id R y c := by
  apply Fin.ext
  change boundedValue hq G id R x c % 2 = boundedValue hq H id R y c % 2
  rw [boundedValue_eq_of_graph_view hq G H hG hH id hinj c R view x y hlabels]

end LocalDecompression.FiniteView
