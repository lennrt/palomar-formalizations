module
public import LocalDecompression.QuotientView
public import LocalDecompression.OrientationOracle

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

@[expose] public section
namespace LocalDecompression.FiniteView
open SimpleGraph MarkerLocality BoundedCells BoundedPacket
open LocalDecompression.OrientationOracle
variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Every residual quotient flooding view is contained in a bounded physical
view, on every input including malformed marker patterns. -/
theorem boundedResidual_floodBall_distance {q : ℕ}
    (G : SimpleGraph V) (hG : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R t : ℕ) (x : V → Fin (q+1)) (c v : V)
    (hv : v ∈ floodBall (boundedResidualGraph G id R x) t c) :
    G.dist c v ≤ (2*R+1)*t := by
  obtain ⟨p,hp⟩ := (mem_floodBall_iff_within _ t c v).mp hv
  have hd := walk_dist_le_mul G (boundedResidualGraph G id R x) hG (2*R+1)
    (fun _ _ h => boundedResidualGraph_edge_length G hG id hinj R x h) p
  have hm := Nat.mul_le_mul_right (2*R+1) hp
  nlinarith

/-- The complete quotient-neighbor list at every physically visible root is
fixed by the containing physical view. This includes neighbors at the fringe. -/
theorem boundedResidual_neighbors_eq_near {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R S : ℕ)
    (view : SameGraphView G H c (S+((R+1)+R))) (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ S+((R+1)+R) → x w = y w)
    (v : V) (hv : G.dist c v ≤ S) :
    neighbors (boundedResidualGraph G id R x) v =
      neighbors (boundedResidualGraph H id R y) v := by
  classical
  ext w
  simp only [neighbors, SimpleGraph.mem_neighborFinset]
  apply boundedResidualGraph_adj_iff G H hG hH id hinj v w R
    (nearby_view G H hG hH c S ((R+1)+R) view v hv) x y
  intro u hu
  rw [hlabels u (le_trans (hG.dist_triangle (u := c) (v := v) (w := u)) (by omega))]

/-- Equality of the actual finite residual quotient flooding sets follows
from physical local views, without a quotient-topology-equality assumption. -/
theorem boundedResidual_floodBall_eq {q : ℕ}
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R T : ℕ)
    (view : SameGraphView G H c ((2*R+1)*T+((R+1)+R)))
    (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ (2*R+1)*T+((R+1)+R) → x w = y w) :
    floodBall (boundedResidualGraph G id R x) T c =
      floodBall (boundedResidualGraph H id R y) T c := by
  classical
  have induction_step : ∀ t, t ≤ T →
      floodBall (boundedResidualGraph G id R x) t c =
        floodBall (boundedResidualGraph H id R y) t c := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have ht' : t ≤ T := by omega
      rw [floodBall, floodBall]
      rw [← ih ht']
      congr 1
      ext w
      simp only [Finset.mem_biUnion]
      have hn : ∀ v ∈ floodBall (boundedResidualGraph G id R x) t c,
          neighbors (boundedResidualGraph G id R x) v =
            neighbors (boundedResidualGraph H id R y) v := by
        intro v hv
        apply boundedResidual_neighbors_eq_near G H hG hH id hinj c R ((2*R+1)*T)
          view x y hlabels v
        have hd := boundedResidual_floodBall_distance G hG id hinj R t x c v hv
        exact hd.trans (Nat.mul_le_mul_left (2*R+1) ht')
      constructor
      · rintro ⟨v,hv,hw⟩
        exact ⟨v,hv,by rw [← hn v hv]; exact hw⟩
      · rintro ⟨v,hv,hw⟩
        exact ⟨v,hv,by rw [hn v hv]; exact hw⟩
  exact induction_step T le_rfl

/-- The entire actual oracle input is reconstructed uniformly from a physical
radius-(2R+1)(T+1) view: IDs, stored advice, and full residual neighbor-ID lists.
Graphs and global marker sets may both differ; no correctness, coverage,
separation, balanced-advice, or final-decoder locality premise is assumed. -/
theorem boundedResidual_oracle_view_eq {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (hG : G.Connected) (hH : H.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (c : V) (R T : ℕ)
    (physical : SameGraphView G H c ((2*R+1)*T+((R+1)+R)))
    (x y : V → Fin (q+1))
    (hlabels : ∀ w, G.dist c w ≤ (2*R+1)*T+((R+1)+R) → x w = y w) :
    LocalDecompression.OrientationOracle.view (boundedResidualGraph G id R x) id
      (boundedAdvice hq G id R x) T c =
    LocalDecompression.OrientationOracle.view (boundedResidualGraph H id R y) id
      (boundedAdvice hq H id R y) T c := by
  classical
  unfold LocalDecompression.OrientationOracle.view
  rw [← boundedResidual_floodBall_eq G H hG hH id hinj c R T physical x y hlabels]
  apply Finset.image_congr
  intro v hv
  have hd := boundedResidual_floodBall_distance G hG id hinj R T x c v hv
  have hn := boundedResidual_neighbors_eq_near G H hG hH id hinj c R ((2*R+1)*T)
    physical x y hlabels v hd
  have localview := nearby_view G H hG hH c ((2*R+1)*T) ((R+1)+R) physical v hd
  have ha : boundedAdvice hq G id R x v = boundedAdvice hq H id R y v := by
    apply boundedAdvice_eq_of_graph_view hq G H hG hH id hinj v R
      (localview.restrict hG hH (by omega)) x y
    intro w hw
    exact hlabels w (le_trans (hG.dist_triangle (u := c) (v := v) (w := w)) (by omega))
  simp only [record, hn, ha]

end LocalDecompression.FiniteView
