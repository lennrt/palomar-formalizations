import ZombieMain.RoutedPresentation
import ZombieMain.TriangleMetric
import ZombieMain.DiamondMetric

namespace ZombieMain
open ZombieDamage

/-- The triangle's literal boundary incidences. -/
theorem triangle_boundary (p a : Fin 6) (hp : triangleBaseTask.inside p=true)
    (ha : triangleBaseTask.inside a=false) (hpa : triangleBaseTask.adj p a=true) :
    ∃ q : Fin 3,p=TriangleRoute.vertex q ∧ a=TriangleRoute.stub q := by
  exact (by decide : ∀ p a : Fin 6, triangleBaseTask.inside p=true →
    triangleBaseTask.inside a=false → triangleBaseTask.adj p a=true →
    ∃ q : Fin 3,p=TriangleRoute.vertex q ∧ a=TriangleRoute.stub q) p a hp ha hpa

def triangleRoutes : RoutedPresentation (stripDiagram 1 1) where
  size := 6
  base := triangleBaseTask
  presentation := trianglePresentation
  exit_route p a q b hp hq ha hb hpa hqb hne := by
    obtain ⟨p',rfl,rfl⟩ := triangle_boundary p a hp ha hpa
    obtain ⟨q',rfl,rfl⟩ := triangle_boundary q b hq hb hqb
    exact (triangle_metric_exit p' q' (fun h => hne (congrArg TriangleRoute.vertex h))).pad 4
  target_route p a x hp ha hpa hx := by
    obtain ⟨p',rfl,rfl⟩ := triangle_boundary p a hp ha hpa
    obtain ⟨x',rfl⟩ := (by decide : ∀ x : Fin 6, triangleBaseTask.inside x=true →
      ∃ x' : Fin 3, x=TriangleRoute.vertex x') x hx
    exact (triangle_metric_target p' x').pad 4

theorem diamond_boundary (p a : Fin 6) (hp : diamondBaseTask.inside p=true)
    (ha : diamondBaseTask.inside a=false) (hpa : diamondBaseTask.adj p a=true) :
    ∃ q : Bool,p=DiamondRoute.port q ∧ a=DiamondRoute.stub q := by
  exact (by decide : ∀ p a : Fin 6, diamondBaseTask.inside p=true →
    diamondBaseTask.inside a=false → diamondBaseTask.adj p a=true →
    ∃ q : Bool,p=DiamondRoute.port q ∧ a=DiamondRoute.stub q) p a hp ha hpa

def diamondRoutes : RoutedPresentation (stripDiagram 1 2) where
  size := 6
  base := diamondBaseTask
  presentation := diamondPresentation
  exit_route p a q b hp hq ha hb hpa hqb hne := by
    obtain ⟨p',rfl,rfl⟩ := diamond_boundary p a hp ha hpa
    obtain ⟨q',rfl,rfl⟩ := diamond_boundary q b hq hb hqb
    have hq' : q'=(!p') := by cases p' <;> cases q' <;> simp_all
    subst q'
    exact (diamond_metric_exit p').pad 5
  target_route p a x hp ha hpa hx := by
    obtain ⟨p',rfl,rfl⟩ := diamond_boundary p a hp ha hpa
    exact (diamond_metric_target p' x (of_decide_eq_true hx)).pad 5

end ZombieMain
