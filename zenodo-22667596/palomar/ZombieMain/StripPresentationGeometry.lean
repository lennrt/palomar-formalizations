import ZombieMain.PortedPresentation
import ZombieMain.StripStructure
import ZombieDamage.OpenStripTask

namespace ZombieMain
open ZombieDamage
set_option maxHeartbeats 2000000

def leftCap (caps : Nat) : Bool := decide (1 ≤ caps)
def rightCap (caps : Nat) : Bool := decide (2 ≤ caps)

def stripLocalIndex (m i : Nat) : Nat :=
  if i < 2*m then (if i%2=0 then i/2 else m+i/2) else i

def stripDiagramIndex (m u : Nat) : Nat :=
  if u < 2*m then (if u<m then 2*u else 2*(u-m)+1) else u

def stripInternal (m caps : Nat) (hc : caps ≤ 2)
    (i : Fin (stripDiagram m caps).order) : Fin (2*m+8) :=
  ⟨stripLocalIndex m i.val, by
    have hi : i.val < 2*m+caps := i.isLt
    dsimp [stripLocalIndex]
    split_ifs <;> omega⟩

theorem strip_index_left_inverse (m i : Nat) :
    stripDiagramIndex m (stripLocalIndex m i) = i := by
  dsimp [stripDiagramIndex, stripLocalIndex]
  split_ifs <;> omega

theorem strip_index_right_inverse (m u : Nat) :
    stripLocalIndex m (stripDiagramIndex m u) = u := by
  dsimp [stripDiagramIndex, stripLocalIndex]
  split_ifs <;> omega

theorem stripInternal_injective (m caps : Nat) (hc : caps ≤ 2) :
    Function.Injective (stripInternal m caps hc) := by
  intro i j h
  have hval := congrArg (fun v : Fin (2*m+8) => stripDiagramIndex m v.val) h
  simp only [stripInternal, strip_index_left_inverse] at hval
  exact Fin.ext hval

theorem stripInternal_inside (m caps : Nat) (hc : caps ≤ 2)
    (i : Fin (stripDiagram m caps).order) :
    OpenStrip.inside m (leftCap caps) (rightCap caps) (stripInternal m caps hc i)=true := by
  have hi : i.val < 2*m+caps := i.isLt
  apply decide_eq_true
  change stripLocalIndex m i.val < 2*m ∨
    (leftCap caps=true ∧ stripLocalIndex m i.val=2*m) ∨
    (rightCap caps=true ∧ stripLocalIndex m i.val=2*m+1)
  interval_cases caps <;> simp [leftCap, rightCap] <;>
    dsimp [stripLocalIndex] <;> split_ifs <;> omega

theorem strip_inside_exact (m caps : Nat) (hc : caps ≤ 2) (v : Fin (2*m+8)) :
    OpenStrip.inside m (leftCap caps) (rightCap caps) v=true ↔
      ∃ i, stripInternal m caps hc i=v := by
  constructor
  · intro hv
    have hv' := of_decide_eq_true hv
    have hi : stripDiagramIndex m v.val < 2*m+caps := by
      change v.val<2*m ∨ (leftCap caps=true ∧ v.val=2*m) ∨
        (rightCap caps=true ∧ v.val=2*m+1) at hv'
      interval_cases caps <;>
        simp [leftCap, rightCap] at hv' <;>
        dsimp [stripDiagramIndex] <;> split_ifs <;> omega
    refine ⟨⟨stripDiagramIndex m v.val,hi⟩,?_⟩
    apply Fin.ext
    exact strip_index_right_inverse m v.val
  · rintro ⟨i,rfl⟩
    exact stripInternal_inside m caps hc i

def interleavedRailAdj (u v : Nat) : Prop :=
  (u/2=v/2 ∧ u%2≠v%2) ∨ (u%2=v%2 ∧ (u/2+1=v/2 ∨ v/2+1=u/2))

def localRailAdj (m u v : Nat) : Prop :=
  (u<m ∧ v<m ∧ (u+1=v ∨ v+1=u)) ∨
  (m≤u ∧ m≤v ∧ (u+1=v ∨ v+1=u)) ∨
  (u<m ∧ v=u+m) ∨ (v<m ∧ u=v+m)

theorem stripAdj_rail (m caps u v : Nat) (hu : u<2*m) (hv : v<2*m) :
    stripAdj m caps u v ↔ interleavedRailAdj u v := by
  unfold stripAdj interleavedRailAdj
  omega

theorem localAdj_rail (m u v : Nat) (left right : Bool) (hm : 2≤m)
    (hu : u<2*m) (hv : v<2*m) :
    OpenStrip.Adj m left right u v ↔ localRailAdj m u v := by
  cases left <;> cases right <;> simp [OpenStrip.Adj,localRailAdj] <;> omega

theorem strip_local_rail (m u v : Nat) (hu : u<2*m) (hv : v<2*m) :
    localRailAdj m (stripLocalIndex m u) (stripLocalIndex m v) ↔ interleavedRailAdj u v := by
  simp only [stripLocalIndex,if_pos hu,if_pos hv]
  split_ifs <;> unfold localRailAdj interleavedRailAdj <;> omega

theorem strip_internal_adj (m caps : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    (i j : Fin (stripDiagram m caps).order) :
    decide (OpenStrip.Adj m (leftCap caps) (rightCap caps)
      (stripInternal m caps hc i).val (stripInternal m caps hc j).val) =
      (stripDiagram m caps).adj i.val j.val := by
  have hi : i.val < 2*m+caps := i.isLt
  have hj : j.val < 2*m+caps := j.isLt
  apply Bool.eq_iff_iff.mpr
  change decide _ = true ↔ decide _ = true
  simp only [decide_eq_true_eq, stripInternal]
  by_cases hiold : i.val < 2*m
  · by_cases hjold : j.val < 2*m
    · have hiLocal : stripLocalIndex m i.val < 2*m := by
        simp only [stripLocalIndex,if_pos hiold]
        split_ifs <;> omega
      have hjLocal : stripLocalIndex m j.val < 2*m := by
        simp only [stripLocalIndex,if_pos hjold]
        split_ifs <;> omega
      rw [stripAdj_rail m caps i.val j.val hiold hjold,
        localAdj_rail m _ _ _ _ hm hiLocal hjLocal]
      exact strip_local_rail m i.val j.val hiold hjold
    · have hcases : j.val=2*m ∨ j.val=2*m+1 := by omega
      rcases hcases with he | he <;> rw [he] <;>
        interval_cases caps <;> simp [stripLocalIndex, hiold, leftCap, rightCap] <;>
        (try split_ifs) <;> simp [OpenStrip.Adj,stripAdj] <;> omega
  · have hcases : i.val=2*m ∨ i.val=2*m+1 := by omega
    rcases hcases with he | he <;> rw [he]
    all_goals by_cases hjold : j.val<2*m
    all_goals first
      | (have hcases : j.val=2*m ∨ j.val=2*m+1 := by omega
         rcases hcases with he' | he' <;> rw [he'] <;>
           interval_cases caps <;> simp [stripLocalIndex,leftCap,rightCap,OpenStrip.Adj,stripAdj] <;> omega)
      | (interval_cases caps <;> simp [stripLocalIndex,hjold,leftCap,rightCap] <;>
          (try split_ifs) <;> simp [OpenStrip.Adj,stripAdj] <;> omega)

end ZombieMain
