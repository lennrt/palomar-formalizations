module
public import UniformStatement
public import LocalDecompression.BoundedPacket

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section

namespace LocalDecompression.FiniteView
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A concrete walk of bounded length inside one physical view transfers to
the other graph with exactly the same length and identifiers. -/
theorem transfer_walk (G H : SimpleGraph V) (hconn : G.Connected)
    (center : V) (radius : ℕ) (view : SameGraphView G H center radius)
    {u v : V} (p : G.Walk u v)
    (hmargin : G.dist center u + p.length ≤ radius) :
    ∃ q : H.Walk u v, q.length = p.length := by
  let S : Set V := {w | G.dist center w ≤ radius}
  have hsupport : ∀ w ∈ p.support, w ∈ S := by
    intro w hw
    have hd : G.dist u w ≤ p.length :=
      (SimpleGraph.dist_le (p.takeUntil w hw)).trans (p.length_takeUntil_le_length hw)
    have ht := hconn.dist_triangle (u := center) (v := u) (w := w)
    change G.dist center w ≤ radius
    omega
  have hu : u ∈ S := hsupport u p.start_mem_support
  have hv : v ∈ S := hsupport v p.end_mem_support
  let phi : G.induce S →g H :=
    { toFun := fun w => w.val
      map_rel' := by
        intro a b hab
        exact (view.edges a.val b.val a.property b.property).mp hab }
  let q := (p.induce S hsupport).map phi
  refine ⟨q, ?_⟩
  have hp := congrArg SimpleGraph.Walk.length (p.map_induce (s := S) hsupport)
  simpa only [q, SimpleGraph.Walk.length_map] using hp

/-- The view comparison is symmetric even though its edge clause is written
using the first graph's vertex ball. -/
theorem SameGraphView.symm {G H : SimpleGraph V} {center : V} {radius : ℕ}
    (view : SameGraphView G H center radius) : SameGraphView H G center radius := by
  refine ⟨fun v => (view.vertices v).symm, ?_⟩
  intro u v hu hv
  exact (view.edges u v ((view.vertices u).mpr hu) ((view.vertices v).mpr hv)).symm

/-- A physical view determines each distance between its center and a seen
vertex even when all remote edges have changed. -/
theorem center_distance_eq (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (center : V) (radius : ℕ) (view : SameGraphView G H center radius)
    (v : V) (hv : G.dist center v ≤ radius) : G.dist center v = H.dist center v := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist center v
  obtain ⟨q, hq⟩ := transfer_walk G H hG center radius view p (by simpa [hp] using hv)
  have hHG : H.dist center v ≤ G.dist center v := by
    calc _ ≤ q.length := SimpleGraph.dist_le q
         _ = G.dist center v := hq.trans hp
  obtain ⟨p', hp'⟩ := hH.exists_walk_length_eq_dist center v
  obtain ⟨q', hq'⟩ := transfer_walk H G hH center radius view.symm p'
    (by simpa [hp'] using (view.vertices v).mp hv)
  apply Nat.le_antisymm _ hHG
  calc _ ≤ q'.length := SimpleGraph.dist_le q'
       _ = H.dist center v := hq'.trans hp'

/-- Every radius-R query around a vertex at distance at most S from the
center is determined by the radius-(S+R) physical view, across topologies. -/
theorem nearby_within_iff (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (center : V) (S R : ℕ) (view : SameGraphView G H center (S+R))
    {u v : V} (hu : G.dist center u ≤ S) :
    Within G R u v ↔ Within H R u v := by
  have hu' : H.dist center u ≤ S := by
    rw [← center_distance_eq G H hG hH center (S+R) view u (by omega)]
    exact hu
  constructor
  · rintro ⟨p,hp⟩
    obtain ⟨q,hq⟩ := transfer_walk G H hG center (S+R) view p (by omega)
    exact ⟨q,by omega⟩
  · rintro ⟨p,hp⟩
    obtain ⟨q,hq⟩ := transfer_walk H G hH center (S+R) view.symm p (by omega)
    exact ⟨q,by omega⟩

/-- A larger physical view determines the entire rooted radius-R view at
any vertex within distance S of its center. This is the re-centering lemma
needed for owner, cell and packet queries. -/
theorem nearby_view (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (center : V) (S R : ℕ) (view : SameGraphView G H center (S+R))
    (u : V) (hu : G.dist center u ≤ S) : SameGraphView G H u R := by
  refine ⟨?_, ?_⟩
  · intro v
    rw [← within_iff_dist G hG R u v, ← within_iff_dist H hH R u v]
    exact nearby_within_iff G H hG hH center S R view hu
  · intro v w hv hw
    have hcv := hG.dist_triangle (u := center) (v := u) (w := v)
    have hcw := hG.dist_triangle (u := center) (v := u) (w := w)
    exact view.edges v w (by omega) (by omega)

/-- Exact candidate distances, and therefore identifier-tiebroken scores,
are preserved by a sufficiently large common physical view. -/
theorem nearby_distance_eq_of_le (G H : SimpleGraph V)
    (hG : G.Connected) (hH : H.Connected) (center : V) (S R : ℕ)
    (view : SameGraphView G H center (S+R))
    {u v : V} (hu : G.dist center u ≤ S) (hv : G.dist u v ≤ R) :
    G.dist u v = H.dist u v :=
  center_distance_eq G H hG hH u R (nearby_view G H hG hH center S R view u hu) v hv

/-- Restrict a common physical view without assuming unchanged remote
distances; center-distance equality inside the larger view proves it. -/
theorem SameGraphView.restrict {G H : SimpleGraph V} (hG : G.Connected) (hH : H.Connected)
    {center : V} {R r : ℕ} (view : SameGraphView G H center R) (hr : r ≤ R) :
    SameGraphView G H center r := by
  refine ⟨?_, ?_⟩
  · intro v
    constructor
    · intro hv
      rw [← center_distance_eq G H hG hH center R view v (hv.trans hr)]
      exact hv
    · intro hv
      rw [← center_distance_eq H G hH hG center R view.symm v (hv.trans hr)]
      exact hv
  · intro u v hu hv
    exact view.edges u v (hu.trans hr) (hv.trans hr)

end LocalDecompression.FiniteView
