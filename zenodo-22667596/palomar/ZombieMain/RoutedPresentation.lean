import ZombieMain.MetricTools

namespace ZombieMain
open ZombieDamage

/-- A component's two local routing obligations. They quantify over every
actual boundary incidence of the leaf graph and every internal target. -/
structure RoutedPresentation (D : Diagram) where
  size : Nat
  base : Task size
  presentation : PortedPresentation base D
  exit_route : ∀ p a q b, base.inside p=true → base.inside q=true →
    base.inside a=false → base.inside b=false →
    base.adj p a=true → base.adj q b=true → p≠q →
    ({base with target := none, allowedExit := fun w => decide (w=b)} : Task size).MetricForcesWithin
      presentation.good (2*D.order) ⟨false,a,p⟩
  target_route : ∀ p a x, base.inside p=true → base.inside a=false →
    base.adj p a=true → base.inside x=true →
    ({base with target := some x, allowedExit := fun w => decide (w≠a)} : Task size).MetricForcesWithin
      presentation.good (2*D.order) ⟨false,a,p⟩

end ZombieMain
