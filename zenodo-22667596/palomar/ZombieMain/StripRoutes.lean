import ZombieMain.RoutedPresentation
import ZombieMain.StripRouteLabels

namespace ZombieMain
open ZombieDamage ZombieDamage.OpenStrip

/-- Uniform prescribed-exit and target strategies for every ladder and capped
ladder with at least two rungs, in its exact structural diagram labelling. -/
def stripRoutes (m caps : Nat) (hm : 2≤m) (hc : caps≤2) :
    RoutedPresentation (stripDiagram m caps) where
  size := 2*m+8
  base := task m (leftCap caps) (rightCap caps) none (fun _ => false)
  presentation := stripPresentation m caps hm hc none (fun _ => false)
  exit_route p a q b hp hq ha hb hpa hqb hne := by
    obtain ⟨entry,hin,rfl,rfl⟩ := strip_boundary_label m hm _ _ p a hp ha (of_decide_eq_true hpa)
    obtain ⟨out,hout,rfl,rfl⟩ := strip_boundary_label m hm _ _ q b hq hb (of_decide_eq_true hqb)
    have hne' : out≠entry := fun h => hne (congrArg (portVertex m hm) h.symm)
    have h := metric_exit_contract m hm (leftCap caps) (rightCap caps) entry out hin hout hne'
    have h' := h.allowed_mono (fun w => decide (w=portStub m out)) (by
      intro w hw
      obtain ⟨r,_,hr,hw⟩ := strip_allowed_witness m _ _ _ _ w hw
      have he : r=out := of_decide_eq_true hr
      exact decide_eq_true (he ▸ hw))
    have h'' := h'.pad (2*m+2*caps)
    have hsum : 2*m+(2*m+2*caps)=2*(stripDiagram m caps).order := by
      change 2*m+(2*m+2*caps)=2*(2*m+caps)
      omega
    rw [hsum] at h''
    exact h''
  target_route p a x hp ha hpa hx := by
    obtain ⟨entry,hin,rfl,rfl⟩ := strip_boundary_label m hm _ _ p a hp ha (of_decide_eq_true hpa)
    have h := metric_target_contract m hm (leftCap caps) (rightCap caps) entry hin x
      ((inside_internal m _ _ x).mp hx)
    have h' := h.allowed_mono (fun w => decide (w≠portStub m entry)) (by
      intro w hw
      obtain ⟨r,_,hr,hw⟩ := strip_allowed_witness m _ _ _ _ w hw
      apply decide_eq_true
      intro he
      exact (of_decide_eq_true hr) (strip_portStub_injective m (hw.symm.trans he)))
    have h'' := h'.pad (2*m+2*caps)
    have hsum : 2*m+(2*m+2*caps)=2*(stripDiagram m caps).order := by
      change 2*m+(2*m+2*caps)=2*(2*m+caps)
      omega
    rw [hsum] at h''
    exact h''

end ZombieMain
