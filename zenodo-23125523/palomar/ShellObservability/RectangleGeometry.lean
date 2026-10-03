module

public import ShellObservability.GridRecovery

@[expose] public section

/-! Rectangular graph geometry, corner reduction, and interval detectors.
The metric proof adapts the attributed square-grid geodesic construction. -/
namespace ShellObservability.Rectangle
open ShellTomography

abbrev Grid (w h : ℕ) := Fin w × Fin h

/-- Manhattan metric on the finite grid. -/
def manhattan {w h : ℕ} (x y : Grid w h) : ℕ :=
  natAbsDiff x.1.val y.1.val + natAbsDiff x.2.val y.2.val

@[simp] theorem manhattan_self {w h} (x : Grid w h) : manhattan x x = 0 := by simp [manhattan]

theorem manhattan_eq_zero_iff {w h} (x y : Grid w h) : manhattan x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 : x.1.val = y.1.val := by
      have := Nat.eq_zero_of_add_eq_zero_right h
      exact (natAbsDiff_eq_zero_iff _ _).mp this
    have h2 : x.2.val = y.2.val := by
      have := Nat.eq_zero_of_add_eq_zero_left h
      exact (natAbsDiff_eq_zero_iff _ _).mp this
    apply Prod.ext <;> apply Fin.ext <;> assumption
  · rintro rfl
    simp

theorem manhattan_symm {w h} (x y : Grid w h) : manhattan x y = manhattan y x := by
  simp [manhattan, natAbsDiff_symm]

theorem manhattan_triangle {w h} (x y z : Grid w h) :
    manhattan x z ≤ manhattan x y + manhattan y z := by
  unfold manhattan
  have h1 := natAbsDiff_triangle x.1.val y.1.val z.1.val
  have h2 := natAbsDiff_triangle x.2.val y.2.val z.2.val
  omega

/-- The actual simple graph whose edges are unit Manhattan moves. -/
def gridGraph (w h : ℕ) : SimpleGraph (Grid w h) :=
  SimpleGraph.fromRel fun x y => manhattan x y = 1

theorem gridGraph_adj {w h} {x y : Grid w h} :
    (gridGraph w h).Adj x y ↔ manhattan x y = 1 := by
  simp only [gridGraph, SimpleGraph.fromRel_adj, manhattan_symm y x, or_self]
  constructor
  · exact And.right
  · intro h
    exact ⟨by intro he; subst y; simp at h, h⟩

/-- Every grid walk has length at least the Manhattan displacement. -/
theorem manhattan_le_walk_length {w h} {x y : Grid w h} (w : (gridGraph w h).Walk x y) :
    manhattan x y ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hxy w ih =>
      have hstep : manhattan _ _ = 1 := gridGraph_adj.mp hxy
      have htri := manhattan_triangle a b c
      have ht : manhattan a c ≤ 1 + w.length := by
        rw [hstep] at htri
        exact htri.trans (Nat.add_le_add_left ih 1)
      simpa [SimpleGraph.Walk.length_cons, Nat.add_comm] using ht

/-- A coordinate move reduces Manhattan distance by exactly one. -/
theorem grid_step_toward {w h : ℕ} (x y : Grid w h) (hne : x ≠ y) :
    ∃ x' : Grid w h, (gridGraph w h).Adj x x' ∧ manhattan x' y + 1 = manhattan x y := by
  rcases x with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  rcases y with ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; apply hne; simp_all
    by_cases hlt : b < d
    · refine ⟨(⟨a,ha⟩,⟨b+1,by omega⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
    · refine ⟨(⟨a,ha⟩,⟨b-1,by omega⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
  · by_cases hlt : a < c
    · refine ⟨(⟨a+1,by omega⟩,⟨b,hb⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
    · refine ⟨(⟨a-1,by omega⟩,⟨b,hb⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega

/-- There is a shortest coordinate walk of the Manhattan length. -/
theorem exists_grid_geodesic {w h : ℕ} (x y : Grid w h) :
    ∃ w : (gridGraph w h).Walk x y, w.length = manhattan x y := by
  generalize he : manhattan x y = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hxy : x = y
    · subst x
      exact ⟨.nil, by simpa using he⟩
    · obtain ⟨x',hadj,hstep⟩ := grid_step_toward x y hxy
      obtain ⟨w,hw⟩ := ih (manhattan x' y) (by omega) x' rfl
      exact ⟨.cons hadj w, by simp [hw]; omega⟩

/-- Graph shortest-path distance, not an assumed distance table, equals Manhattan distance. -/
theorem grid_dist_eq_manhattan {w h : ℕ} (x y : Grid w h) :
    (gridGraph w h).dist x y = manhattan x y := by
  obtain ⟨p,hp⟩ := exists_grid_geodesic x y
  apply le_antisymm
  · exact hp ▸ SimpleGraph.dist_le p
  · have hr : (gridGraph w h).Reachable x y := ⟨p⟩
    obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
    rw [← hw]
    exact manhattan_le_walk_length w

/-- The actual grid graph is connected. -/
theorem grid_connected {w h : ℕ} [NeZero w] [NeZero h] : (gridGraph w h).Connected := by
  constructor
  intro x y
  obtain ⟨w,_⟩ := exists_grid_geodesic x y
  exact ⟨w⟩


def HasIntervalDetector (W H : ℕ) (p q r s : ℕ × ℕ) : Prop :=
  ∃ a b k : ℕ, 0 < k ∧ a+k+1 ≤ W ∧ b+k+1 ≤ H ∧
    ∀ x y, ¬ ((a < x ∧ x ≤ a+k) ↔ (b < y ∧ y ≤ b+k)) →
      distancePair (x,y) p q ≠ distancePair (x,y) r s

/-- Convert the canonical parallelogram into a balanced interval detector. -/
theorem canonical_hasIntervalDetector
    (W H : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ W ∧ z.2 ≤ H)
    (a b u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hp : ({p,q} : Multiset (ℕ × ℕ)) = {(a,b+v),(a+u+v,b+u)})
    (hr : ({r,s} : Multiset (ℕ × ℕ)) = {(a+v,b),(a+u,b+u+v)}) :
    HasIntervalDetector W H p q r s := by
  have hpx : a+u+v ≤ W := by
    have hm : (a+u+v,b+u) ∈ ({p,q} : Multiset (ℕ × ℕ)) := by rw [hp]; simp
    have hh := hbound (a+u+v,b+u) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.1
  have hry : b+u+v ≤ H := by
    have hm : (a+u,b+u+v) ∈ ({r,s} : Multiset (ℕ × ℕ)) := by rw [hr]; simp
    have hh := hbound (a+u,b+u+v) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.2
  refine ⟨a,b,u+v-1,by omega,by omega,by omega,?_⟩
  intro x y hxor
  have hd := parallelogram_detected a b u v x y hu hv (by omega)
  rw [distancePair_of_pair_eq (x,y) _ _ _ _ hp,
    distancePair_of_pair_eq (x,y) _ _ _ _ hr]
  exact hd


/-- Relabelling the two points in the first population changes no detector. -/
theorem hasIntervalDetector_swap_left (W H : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalDetector W H q p r s) : HasIntervalDetector W H p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  rw [distancePair_comm (x,y) p q]
  exact hd x y hxy

/-- Interchanging the two populations changes no detector. -/
theorem hasIntervalDetector_swap_populations (W H : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalDetector W H r s p q) : HasIntervalDetector W H p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  exact Ne.symm (hd x y hxy)

/-- The leftmost-point version of the interval reduction. -/
theorem leftmost_corner_collision_hasIntervalDetector
    (W H : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ W ∧ z.2 ≤ H)
    (hpq : p.1 ≤ q.1) (hpr : p.1 ≤ r.1) (hps : p.1 ≤ s.1)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,H) p q = distancePair (0,H) r s) :
    HasIntervalDetector W H p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  obtain ⟨a,b,u,v,hu,hv,hpq',hrs'⟩ := leftmost_corner_collision_canonical H p q r s
    hp.2 hq.2 hr.2 hs.2 hpq hpr hps hne hzero htop
  exact canonical_hasIntervalDetector W H p q r s hbound a b u v hu hv hpq' hrs'

/-- Every distinct two-target population pair with equal reports at two
adjacent corners admits a nonempty equal-length interior interval detector.
In particular, this applies whenever all four corner reports agree. -/
theorem corner_collision_hasIntervalDetector
    (W H : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ W ∧ z.2 ≤ H)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,H) p q = distancePair (0,H) r s) :
    HasIntervalDetector W H p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  have hmin : (p.1 ≤ q.1 ∧ p.1 ≤ r.1 ∧ p.1 ≤ s.1) ∨
      (q.1 ≤ p.1 ∧ q.1 ≤ r.1 ∧ q.1 ≤ s.1) ∨
      (r.1 ≤ p.1 ∧ r.1 ≤ q.1 ∧ r.1 ≤ s.1) ∨
      (s.1 ≤ p.1 ∧ s.1 ≤ q.1 ∧ s.1 ≤ r.1) := by omega
  rcases hmin with hpmin | hqmin | hrmin | hsmin
  · exact leftmost_corner_collision_hasIntervalDetector W H p q r s hbound
      hpmin.1 hpmin.2.1 hpmin.2.2 hne hzero htop
  · apply hasIntervalDetector_swap_left
    apply leftmost_corner_collision_hasIntervalDetector W H q p r s
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hqmin.1
    · exact hqmin.2.1
    · exact hqmin.2.2
    · simpa only [Multiset.pair_comm] using hne
    · simpa only [distancePair_comm] using hzero
    · simpa only [distancePair_comm] using htop
  · apply hasIntervalDetector_swap_populations
    apply leftmost_corner_collision_hasIntervalDetector W H r s p q
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hrmin.2.2
    · exact hrmin.1
    · exact hrmin.2.1
    · exact Ne.symm hne
    · exact hzero.symm
    · exact htop.symm
  · apply hasIntervalDetector_swap_populations
    apply hasIntervalDetector_swap_left
    apply leftmost_corner_collision_hasIntervalDetector W H s r p q
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hsmin.2.2
    · exact hsmin.1
    · exact hsmin.2.1
    · simpa only [Multiset.pair_comm] using Ne.symm hne
    · simpa only [distancePair_comm] using hzero.symm
    · simpa only [distancePair_comm] using htop.symm


open ShellTomography

set_option maxHeartbeats 2000000 in
/-- Opposite corners carry equivalent pair reports, since complementary
vertex distances add to the constant `2N`. -/
theorem opposite_corner_pair_equality
    (W H : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ W ∧ z.2 ≤ H) :
    (distancePair (W,H) p q = distancePair (W,H) r s ↔
      distancePair (0,0) p q = distancePair (0,0) r s) ∧
    (distancePair (W,0) p q = distancePair (W,0) r s ↔
      distancePair (0,H) p q = distancePair (0,H) r s) := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  have hdiag (z : ℕ × ℕ) (hz : z.1 ≤ W ∧ z.2 ≤ H) :
      (natAbsDiff W z.1 + natAbsDiff H z.2) +
        (natAbsDiff 0 z.1 + natAbsDiff 0 z.2) = W+H := by
    unfold natAbsDiff
    omega
  have hanti (z : ℕ × ℕ) (hz : z.1 ≤ W ∧ z.2 ≤ H) :
      (natAbsDiff W z.1 + natAbsDiff 0 z.2) +
        (natAbsDiff 0 z.1 + natAbsDiff H z.2) = W+H := by
    unfold natAbsDiff
    omega
  have hp0 := hdiag p hp
  have hq0 := hdiag q hq
  have hr0 := hdiag r hr
  have hs0 := hdiag s hs
  have hp1 := hanti p hp
  have hq1 := hanti q hq
  have hr1 := hanti r hr
  have hs1 := hanti s hs
  simp only [distancePair, pair_eq_iff]
  omega

end ShellObservability.Rectangle
