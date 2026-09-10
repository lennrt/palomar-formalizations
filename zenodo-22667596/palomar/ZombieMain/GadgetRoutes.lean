import ZombieMain.RoutedPresentation
import ZombieMain.FinitePresentations
import ZombieDamage.Routing

namespace ZombieMain
open ZombieDamage
set_option maxHeartbeats 1000000

theorem gadget_boundary (g : Gadget) (p a : g.Vertex)
    (hp : g.inside p=true) (ha : g.inside a=false) (hpa : g.adj p a=true) :
    g.port p=true ∧ a=g.stub p := by
  have h : ∀ g : Gadget, ∀ p a : g.Vertex,
      g.inside p=true → g.inside a=false → g.adj p a=true →
      g.port p=true ∧ a=g.stub p := by
    intro g
    cases g <;> decide
  exact h g p a hp ha hpa

theorem gadget_target_nonentry (g : Gadget) (p x w : g.Vertex)
    (hp : g.port p=true) (hw : (g.targetTask p x).allowedExit w=true) : w≠g.stub p := by
  have h : ∀ g : Gadget, ∀ p x w : g.Vertex, g.port p=true →
      (g.targetTask p x).allowedExit w=true → w≠g.stub p := by
    intro g
    cases g <;> decide
  exact h g p x w hp hw

/-- All five exceptional open components, with every entry, prescribed exit,
and internal target. The universal fields are discharged by the checked policies. -/
def gadgetRoutes (g : Gadget) : RoutedPresentation (gadgetFamily g).diagram where
  size := g.size
  base := gadgetBaseTask g
  presentation := gadgetPresentation g
  exit_route p a q b hp hq ha hb hpa hqb hne := by
    obtain ⟨hp',rfl⟩ := gadget_boundary g p a hp ha hpa
    obtain ⟨hq',rfl⟩ := gadget_boundary g q b hq hb hqb
    obtain ⟨hg,hr⟩ := (Verified.finite_component_routing g).1 p q hp' hq' hne
    have ho : (gadgetFamily g).diagram.order=g.order := by cases g <;> rfl
    rw [ho]
    exact hr
  target_route p a x hp ha hpa hx := by
    obtain ⟨hp',rfl⟩ := gadget_boundary g p a hp ha hpa
    obtain ⟨hg,hr⟩ := (Verified.finite_component_routing g).2 p x hp' hx
    have ho : (gadgetFamily g).diagram.order=g.order := by cases g <;> rfl
    rw [ho]
    exact hr.allowed_mono (fun w => decide (w≠g.stub p))
      (fun w hw => decide_eq_true (gadget_target_nonentry g p x w hp' hw))

end ZombieMain
