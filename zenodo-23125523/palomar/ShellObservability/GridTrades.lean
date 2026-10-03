module

public import ShellTomography.Grid

@[expose] public section

/-! Explicit two-target trades and their exact sensor detector sets. -/
namespace ShellObservability
open ShellTomography

def distancePair (s p q : ℕ × ℕ) : Multiset ℕ :=
  {natAbsDiff s.1 p.1 + natAbsDiff s.2 p.2,
   natAbsDiff s.1 q.1 + natAbsDiff s.2 q.2}

theorem pair_eq_iff {α : Type*} (a b c d : α) :
    ({a, b} : Multiset α) = {c, d} ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  classical
  simp only [Multiset.insert_eq_cons, Multiset.cons_eq_cons, Multiset.singleton_inj,
    Multiset.singleton_eq_cons_iff]
  by_cases hac : a = c <;> simp_all [eq_comm, and_comm]

/-- The skinny trade is invisible exactly when both coordinates lie inside their
intervals, or both lie outside. This includes all endpoint and corner cases. -/
theorem skinny_trade_detector (a b k x y : ℕ) (hk : 1 ≤ k) :
    distancePair (x,y) (a,b+1) (a+k+1,b+k) =
      distancePair (x,y) (a+1,b) (a+k,b+k+1) ↔
    ((a < x ∧ x ≤ a+k) ↔ (b < y ∧ y ≤ b+k)) := by
  unfold distancePair
  rw [pair_eq_iff]
  dsimp [natAbsDiff]
  omega

/-- The exact skinny detector already occurs in the first moment. -/
theorem skinny_trade_moment_detector (a b k x y : ℕ) (hk : 1 ≤ k) :
    (distancePair (x,y) (a,b+1) (a+k+1,b+k)).sum =
      (distancePair (x,y) (a+1,b) (a+k,b+k+1)).sum ↔
    ((a < x ∧ x ≤ a+k) ↔ (b < y ∧ y ≤ b+k)) := by
  simp [distancePair, natAbsDiff]
  omega

set_option maxHeartbeats 2000000 in
/-- Every nondegenerate diagonal parallelogram is detected on its bounding
interval XOR. This is the sufficiency mechanism behind the grid cut reduction. -/
theorem parallelogram_detected (a b u v x y : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hxor : ¬ ((a < x ∧ x < a+u+v) ↔ (b < y ∧ y < b+u+v))) :
    distancePair (x,y) (a,b+v) (a+u+v,b+u) ≠
      distancePair (x,y) (a+v,b) (a+u,b+u+v) := by
  unfold distancePair
  simp only [ne_eq, pair_eq_iff]
  dsimp [natAbsDiff]
  omega

set_option maxHeartbeats 2000000 in
/-- A first-moment report suffices on every canonical interval detector. -/
theorem parallelogram_moment_detected (a b u v x y : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hxor : ¬ ((a < x ∧ x < a+u+v) ↔ (b < y ∧ y < b+u+v))) :
    (distancePair (x,y) (a,b+v) (a+u+v,b+u)).sum ≠
      (distancePair (x,y) (a+v,b) (a+u,b+u+v)).sum := by
  simp [distancePair, natAbsDiff]
  omega

end ShellObservability
