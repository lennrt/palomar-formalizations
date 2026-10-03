module

public import ShellObservability.GridTrades

@[expose] public section

/-!
# Corner collisions contain a balanced interval detector

Equal anonymous reports at two adjacent corners specify the two diagonal
coordinate multisets. Distinct pairs then match those coordinates oppositely.
Choosing a leftmost point puts the resulting integer parallelogram in the
canonical form used by `parallelogram_detected`.
-/

namespace ShellObservability

open ShellTomography

@[simp] theorem distancePair_comm (sensor p q : ℕ × ℕ) :
    distancePair sensor p q = distancePair sensor q p := by
  simp only [distancePair, Multiset.pair_comm]

theorem distancePair_of_pair_eq (sensor p q r s : ℕ × ℕ)
    (h : ({p,q} : Multiset (ℕ × ℕ)) = {r,s}) :
    distancePair sensor p q = distancePair sensor r s := by
  rw [pair_eq_iff] at h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · exact distancePair_comm sensor _ _

set_option maxHeartbeats 2000000 in
/-- With the first point leftmost, a nontrivial corner collision is a canonical
positive diagonal parallelogram, allowing the two points in the other population
to occur in either order. -/
theorem leftmost_corner_collision_canonical
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hpy : p.2 ≤ N) (hqy : q.2 ≤ N) (hry : r.2 ≤ N) (hsy : s.2 ≤ N)
    (hpq : p.1 ≤ q.1) (hpr : p.1 ≤ r.1) (hps : p.1 ≤ s.1)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,N) p q = distancePair (0,N) r s) :
    ∃ a b u v : ℕ, 0 < u ∧ 0 < v ∧
      ({p,q} : Multiset (ℕ × ℕ)) = {(a,b+v),(a+u+v,b+u)} ∧
      ({r,s} : Multiset (ℕ × ℕ)) = {(a+v,b),(a+u,b+u+v)} := by
  rcases p with ⟨px,py⟩
  rcases q with ⟨qx,qy⟩
  rcases r with ⟨rx,ry⟩
  rcases s with ⟨sx,sy⟩
  simp only [ne_eq, pair_eq_iff, Prod.mk.injEq] at hne
  simp only [distancePair, pair_eq_iff] at hzero htop
  dsimp [natAbsDiff] at hzero htop
  dsimp at hpq hpr hps hpy hqy hry hsy
  simp only [Nat.zero_sub, zero_add, Nat.sub_eq_zero_of_le hpy,
    Nat.sub_eq_zero_of_le hqy, Nat.sub_eq_zero_of_le hry, Nat.sub_eq_zero_of_le hsy, add_zero] at hzero htop
  rcases hzero with hz | hz <;> rcases htop with ht | ht
  · omega
  · have hd1 : px + sy = sx + py := by omega
    have hd2 : qx + ry = rx + qy := by omega
    clear ht
    refine ⟨px, ry, sx-px, rx-px, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [pair_eq_iff]
      left
      simp only [Prod.mk.injEq]
      constructor <;> constructor <;> first | trivial | omega
    · rw [pair_eq_iff]
      left
      simp only [Prod.mk.injEq]
      constructor <;> constructor <;> first | trivial | omega
  · have hd1 : px + ry = rx + py := by omega
    have hd2 : qx + sy = sx + qy := by omega
    clear ht
    refine ⟨px, sy, rx-px, sx-px, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · rw [pair_eq_iff]
      left
      simp only [Prod.mk.injEq]
      constructor <;> constructor <;> first | trivial | omega
    · rw [pair_eq_iff]
      right
      simp only [Prod.mk.injEq]
      constructor <;> constructor <;> first | trivial | omega
  · omega

/-- A nonempty equal-length pair of interior intervals whose coordinate XOR
detects the two populations. The outer square is `[0,N]²`. -/
def HasIntervalDetector (N : ℕ) (p q r s : ℕ × ℕ) : Prop :=
  ∃ a b k : ℕ, 0 < k ∧ a+k+1 ≤ N ∧ b+k+1 ≤ N ∧
    ∀ x y, ¬ ((a < x ∧ x ≤ a+k) ↔ (b < y ∧ y ≤ b+k)) →
      distancePair (x,y) p q ≠ distancePair (x,y) r s

/-- Convert the canonical parallelogram into a balanced interval detector. -/
theorem canonical_hasIntervalDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (a b u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hp : ({p,q} : Multiset (ℕ × ℕ)) = {(a,b+v),(a+u+v,b+u)})
    (hr : ({r,s} : Multiset (ℕ × ℕ)) = {(a+v,b),(a+u,b+u+v)}) :
    HasIntervalDetector N p q r s := by
  have hpx : a+u+v ≤ N := by
    have hm : (a+u+v,b+u) ∈ ({p,q} : Multiset (ℕ × ℕ)) := by rw [hp]; simp
    have hh := hbound (a+u+v,b+u) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.1
  have hry : b+u+v ≤ N := by
    have hm : (a+u,b+u+v) ∈ ({r,s} : Multiset (ℕ × ℕ)) := by rw [hr]; simp
    have hh := hbound (a+u,b+u+v) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.2
  refine ⟨a,b,u+v-1,by omega,by omega,by omega,?_⟩
  intro x y hxor
  have hd := parallelogram_detected a b u v x y hu hv (by omega)
  rw [distancePair_of_pair_eq (x,y) _ _ _ _ hp,
    distancePair_of_pair_eq (x,y) _ _ _ _ hr]
  exact hd

end ShellObservability

namespace ShellObservability

/-- Relabelling the two points in the first population changes no detector. -/
theorem hasIntervalDetector_swap_left (N : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalDetector N q p r s) : HasIntervalDetector N p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  rw [distancePair_comm (x,y) p q]
  exact hd x y hxy

/-- Interchanging the two populations changes no detector. -/
theorem hasIntervalDetector_swap_populations (N : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalDetector N r s p q) : HasIntervalDetector N p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  exact Ne.symm (hd x y hxy)

/-- The leftmost-point version of the interval reduction. -/
theorem leftmost_corner_collision_hasIntervalDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (hpq : p.1 ≤ q.1) (hpr : p.1 ≤ r.1) (hps : p.1 ≤ s.1)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,N) p q = distancePair (0,N) r s) :
    HasIntervalDetector N p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  obtain ⟨a,b,u,v,hu,hv,hpq',hrs'⟩ := leftmost_corner_collision_canonical N p q r s
    hp.2 hq.2 hr.2 hs.2 hpq hpr hps hne hzero htop
  exact canonical_hasIntervalDetector N p q r s hbound a b u v hu hv hpq' hrs'

/-- Every distinct two-target population pair with equal reports at two
adjacent corners admits a nonempty equal-length interior interval detector.
In particular, this applies whenever all four corner reports agree. -/
theorem corner_collision_hasIntervalDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,N) p q = distancePair (0,N) r s) :
    HasIntervalDetector N p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  have hmin : (p.1 ≤ q.1 ∧ p.1 ≤ r.1 ∧ p.1 ≤ s.1) ∨
      (q.1 ≤ p.1 ∧ q.1 ≤ r.1 ∧ q.1 ≤ s.1) ∨
      (r.1 ≤ p.1 ∧ r.1 ≤ q.1 ∧ r.1 ≤ s.1) ∨
      (s.1 ≤ p.1 ∧ s.1 ≤ q.1 ∧ s.1 ≤ r.1) := by omega
  rcases hmin with hpmin | hqmin | hrmin | hsmin
  · exact leftmost_corner_collision_hasIntervalDetector N p q r s hbound
      hpmin.1 hpmin.2.1 hpmin.2.2 hne hzero htop
  · apply hasIntervalDetector_swap_left
    apply leftmost_corner_collision_hasIntervalDetector N q p r s
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
    apply leftmost_corner_collision_hasIntervalDetector N r s p q
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
    apply leftmost_corner_collision_hasIntervalDetector N s r p q
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hsmin.2.2
    · exact hsmin.1
    · exact hsmin.2.1
    · simpa only [Multiset.pair_comm] using Ne.symm hne
    · simpa only [distancePair_comm] using hzero.symm
    · simpa only [distancePair_comm] using htop.symm

end ShellObservability

namespace ShellObservability

open ShellTomography

set_option maxHeartbeats 2000000 in
/-- Opposite corners carry equivalent pair reports, since complementary
vertex distances add to the constant `2N`. -/
theorem opposite_corner_pair_equality
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N) :
    (distancePair (N,N) p q = distancePair (N,N) r s ↔
      distancePair (0,0) p q = distancePair (0,0) r s) ∧
    (distancePair (N,0) p q = distancePair (N,0) r s ↔
      distancePair (0,N) p q = distancePair (0,N) r s) := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  have hdiag (z : ℕ × ℕ) (hz : z.1 ≤ N ∧ z.2 ≤ N) :
      (natAbsDiff N z.1 + natAbsDiff N z.2) +
        (natAbsDiff 0 z.1 + natAbsDiff 0 z.2) = 2*N := by
    unfold natAbsDiff
    omega
  have hanti (z : ℕ × ℕ) (hz : z.1 ≤ N ∧ z.2 ≤ N) :
      (natAbsDiff N z.1 + natAbsDiff 0 z.2) +
        (natAbsDiff 0 z.1 + natAbsDiff N z.2) = 2*N := by
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

end ShellObservability
