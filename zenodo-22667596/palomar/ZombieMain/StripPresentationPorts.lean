import ZombieMain.StripPresentationGeometry

namespace ZombieMain
open ZombieDamage
set_option maxHeartbeats 2000000

def stripStubIndex (m i : Nat) : Nat :=
  if i < 2*m then (if i<2 then 2*m+2+i%2 else 2*m+4+i%2) else i+6

def StripLocalInside (m caps u : Nat) : Prop :=
  u<2*m ∨ (1≤caps ∧ u=2*m) ∨ (2≤caps ∧ u=2*m+1)

theorem strip_local_inside_iff (m caps : Nat) (u : Fin (2*m+8)) :
    OpenStrip.inside m (leftCap caps) (rightCap caps) u=true ↔ StripLocalInside m caps u.val := by
  simp [OpenStrip.inside, leftCap, rightCap, StripLocalInside]

theorem strip_local_outside_iff (m caps : Nat) (u : Fin (2*m+8)) :
    OpenStrip.inside m (leftCap caps) (rightCap caps) u=false ↔ ¬ StripLocalInside m caps u.val := by
  rw [← strip_local_inside_iff]
  cases OpenStrip.inside m (leftCap caps) (rightCap caps) u <;> decide

theorem strip_stub_bound (m caps : Nat) (hc : caps≤2)
    (i : Fin (stripDiagram m caps).order) : stripStubIndex m i.val < 2*m+8 := by
  have hi : i.val < 2*m+caps := i.isLt
  dsimp [stripStubIndex]
  split_ifs <;> omega

/-- Exactly one specified leaf is adjacent to each degree-two internal
vertex, and no leaf is adjacent to a saturated internal vertex. -/
theorem strip_boundary_iff (m caps : Nat) (hm : 2≤m) (hc : caps≤2)
    (i : Fin (stripDiagram m caps).order) (v : Fin (2*m+8)) :
    (¬ StripLocalInside m caps v.val ∧
      OpenStrip.Adj m (leftCap caps) (rightCap caps) (stripLocalIndex m i.val) v.val) ↔
      StripPort m caps i.val ∧ v.val=stripStubIndex m i.val := by
  have hi : i.val < 2*m+caps := i.isLt
  have hv : v.val < 2*m+8 := v.isLt
  interval_cases caps <;> dsimp [leftCap,rightCap,stripLocalIndex,stripStubIndex] <;>
    split_ifs <;> simp [StripLocalInside,OpenStrip.Adj,StripPort] <;>
    simp only [Fin.ext_iff,Fin.val_zero] at * <;> omega

theorem strip_outside_neighbors (m : Nat) (hm : 2≤m) (left right : Bool)
    (u v : Fin (2*m+8)) (hu : OpenStrip.inside m left right u=false)
    (ha : OpenStrip.Adj m left right u.val v.val) : OpenStrip.inside m left right v=true := by
  have hu' := of_decide_eq_false hu
  apply decide_eq_true
  change v.val<2*m ∨ (left=true ∧ v.val=2*m) ∨ (right=true ∧ v.val=2*m+1)
  change ¬ (u.val<2*m ∨ (left=true ∧ u.val=2*m) ∨ (right=true ∧ u.val=2*m+1)) at hu'
  cases left <;> cases right <;> simp [OpenStrip.Adj] at ha <;> simp_all <;> simp only [Fin.ext_iff,Fin.val_zero] at * <;> omega

end ZombieMain
