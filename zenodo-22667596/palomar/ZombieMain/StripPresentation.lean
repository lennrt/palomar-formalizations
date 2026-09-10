import ZombieMain.StripPresentationPorts

namespace ZombieMain
open ZombieDamage

/-- A faithful leaf presentation for every ladder and capped ladder length.
The rail permutation, active caps and individual boundary incidences are exact. -/
def stripPresentation (m caps : Nat) (hm : 2≤m) (hc : caps≤2)
    (target : Option (Fin (2*m+8))) (allowed : OpenStrip.Port → Bool) :
    PortedPresentation (OpenStrip.task m (leftCap caps) (rightCap caps) target allowed)
      (stripDiagram m caps) := by
  refine
    { internal := stripInternal m caps hc
      internal_injective := stripInternal_injective m caps hc
      inside_exact := strip_inside_exact m caps hc
      internal_adj := strip_internal_adj m caps hm hc
      good := OpenStrip.task_good m hm _ _ target allowed
      boundary_leaves := OpenStrip.task_boundary_leaves m hm _ _ target allowed
      outside_neighbors := ?_
      one_stub := ?_
      port_stub := ?_ }
  · intro u v hu ha
    exact strip_outside_neighbors m hm _ _ u v hu (of_decide_eq_true ha)
  · intro u v w hv hu hw huv hvw
    obtain ⟨i,rfl⟩ := (strip_inside_exact m caps hc v).mp hv
    have hrev : OpenStrip.Adj m (leftCap caps) (rightCap caps)
        (stripLocalIndex m i.val) u.val := by
      change (OpenStrip.graph m (leftCap caps) (rightCap caps) hm).adj (stripInternal m caps hc i) u
      apply (OpenStrip.graph m (leftCap caps) (rightCap caps) hm).symm
      change OpenStrip.Adj m (leftCap caps) (rightCap caps) u.val (stripLocalIndex m i.val)
      exact of_decide_eq_true huv
    have h1 := (strip_boundary_iff m caps hm hc i u).mp
      ⟨(strip_local_outside_iff m caps u).mp hu,hrev⟩
    have h2 := (strip_boundary_iff m caps hm hc i w).mp
      ⟨(strip_local_outside_iff m caps w).mp hw,of_decide_eq_true hvw⟩
    exact Fin.ext (h1.2.trans h2.2.symm)
  · intro i
    rw [strip_port_iff m caps i.val hm hc i.isLt]
    constructor
    · intro hi
      let v : Fin (2*m+8) := ⟨stripStubIndex m i.val,strip_stub_bound m caps hc i⟩
      have h := (strip_boundary_iff m caps hm hc i v).mpr ⟨hi,rfl⟩
      exact ⟨v,(strip_local_outside_iff m caps v).mpr h.1,decide_eq_true h.2⟩
    · rintro ⟨v,hv,ha⟩
      exact ((strip_boundary_iff m caps hm hc i v).mp
        ⟨(strip_local_outside_iff m caps v).mp hv,of_decide_eq_true ha⟩).1

end ZombieMain
