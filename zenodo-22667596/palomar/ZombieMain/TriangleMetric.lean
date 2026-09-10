import ZombieMain.FinitePresentations
import ZombieMain.MetricTools
import ZombieDamage.Isomorphism

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame

 def triangleTask (target : Option (Fin 6)) (allowed : Fin 6 → Bool) : Task 6 :=
   {triangleBaseTask with target:=target,allowedExit:=allowed}

 def triangleTaskIso (target : Option (Fin 6)) (allowed : Fin 6 → Bool) :
    GraphIso TriangleRoute.graph ((triangleTask target allowed).graph trianglePresentation.good) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  adjacency := by
    intro u v
    change TriangleRoute.Adj u v ↔ decide (TriangleRoute.Adj u v)=true
    simp only [decide_eq_true_eq]

 theorem triangle_metric_exit (p q : Fin 3) (hne : p≠q) :
    (triangleTask none (fun w => decide (w=TriangleRoute.stub q))).MetricForcesWithin
      trianglePresentation.good 2 ⟨false,TriangleRoute.stub p,TriangleRoute.vertex p⟩ := by
  let T := triangleTask none (fun w => decide (w=TriangleRoute.stub q))
  let s : Position 6 := ⟨false,TriangleRoute.stub p,TriangleRoute.vertex p⟩
  apply T.fullGame_metricForcesWithin trianglePresentation.good trianglePresentation.boundary_leaves
    2 s (fun _ => False)
    ((by decide : ∀ p : Fin 3, triangleBaseTask.inside (TriangleRoute.vertex p)=true) p)
    ((by decide : ∀ p : Fin 3, triangleBaseTask.adj (TriangleRoute.stub p) (TriangleRoute.vertex p)=true) p)
    (by intro v hv hd; contradiction)
  have h := TriangleRoute.prescribed_exit p q hne (Task.fullState s (fun _ => False)) rfl rfl
  apply (triangleTaskIso none (fun w => decide (w=TriangleRoute.stub q))).forcesWithin h
  intro phase t ht
  refine ⟨ht.1,?_,?_,?_⟩
  · change triangleBaseTask.inside t.survivor=false
    rw [ht.2.2.1]
    exact (by decide : ∀ q : Fin 3, triangleBaseTask.inside (TriangleRoute.stub q)=false) q
  · change decide (t.survivor=TriangleRoute.stub q)=true
    exact decide_eq_true ht.2.2.1
  · intro v hv; cases hv

 theorem triangle_metric_target (p x : Fin 3) :
    (triangleTask (some (TriangleRoute.vertex x)) (fun w => decide (w≠TriangleRoute.stub p))).MetricForcesWithin
      trianglePresentation.good 2
      ⟨false,TriangleRoute.stub p,TriangleRoute.vertex p⟩ := by
  let T := triangleTask (some (TriangleRoute.vertex x)) (fun w => decide (w≠TriangleRoute.stub p))
  let s : Position 6 := ⟨false,TriangleRoute.stub p,TriangleRoute.vertex p⟩
  apply T.fullGame_metricForcesWithin trianglePresentation.good trianglePresentation.boundary_leaves
    2 s (fun _ => False)
    ((by decide : ∀ p : Fin 3, triangleBaseTask.inside (TriangleRoute.vertex p)=true) p)
    ((by decide : ∀ p : Fin 3, triangleBaseTask.adj (TriangleRoute.stub p) (TriangleRoute.vertex p)=true) p)
    (by intro v hv hd; contradiction)
  have h := TriangleRoute.target_route p x (Task.fullState s (fun _ => False)) rfl rfl
  apply (triangleTaskIso (some (TriangleRoute.vertex x))
    (fun w => decide (w≠TriangleRoute.stub p))).forcesWithin h
  intro phase t ht
  obtain ⟨q,hq,hz,hs,hd⟩ := ht.2
  refine ⟨ht.1,?_,?_,?_⟩
  · change triangleBaseTask.inside t.survivor=false
    rw [hs]
    exact (by decide : ∀ q : Fin 3, triangleBaseTask.inside (TriangleRoute.stub q)=false) q
  · change decide (t.survivor≠TriangleRoute.stub p)=true
    rw [hs]
    exact decide_eq_true ((by decide : ∀ p q : Fin 3, q≠p → TriangleRoute.stub q≠TriangleRoute.stub p) p q hq)
  · intro v hv
    change some (TriangleRoute.vertex x)=some v at hv
    exact Option.some.inj hv ▸ hd

end ZombieMain
