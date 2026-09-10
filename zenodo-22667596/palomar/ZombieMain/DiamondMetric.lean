import ZombieMain.FinitePresentations
import ZombieMain.MetricTools
import ZombieDamage.Isomorphism

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame

def diamondTask (target : Option (Fin 6)) (allowed : Fin 6 → Bool) : Task 6 :=
  {diamondBaseTask with target:=target,allowedExit:=allowed}

def diamondTaskIso (target : Option (Fin 6)) (allowed : Fin 6 → Bool) :
    GraphIso DiamondRoute.graph ((diamondTask target allowed).graph diamondPresentation.good) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  adjacency := by
    intro u v
    change DiamondRoute.Adj u v ↔ decide (DiamondRoute.Adj u v)=true
    simp only [decide_eq_true_eq]

theorem diamond_metric_exit (p : Bool) :
    (diamondTask none (fun w => decide (w=DiamondRoute.stub (!p)))).MetricForcesWithin
      diamondPresentation.good 3 ⟨false,DiamondRoute.stub p,DiamondRoute.port p⟩ := by
  let T := diamondTask none (fun w => decide (w=DiamondRoute.stub (!p)))
  let s : Position 6 := ⟨false,DiamondRoute.stub p,DiamondRoute.port p⟩
  apply T.fullGame_metricForcesWithin diamondPresentation.good diamondPresentation.boundary_leaves
    3 s (fun _ => False)
    ((by decide : ∀ p : Bool, diamondBaseTask.inside (DiamondRoute.port p)=true) p)
    ((by decide : ∀ p : Bool, diamondBaseTask.adj (DiamondRoute.stub p) (DiamondRoute.port p)=true) p)
    (by intro v hv hd; contradiction)
  have h := DiamondRoute.through_middle p false (Task.fullState s (fun _ => False)) rfl rfl
  apply (diamondTaskIso none (fun w => decide (w=DiamondRoute.stub (!p)))).forcesWithin h
  intro phase t ht
  refine ⟨ht.1,?_,?_,?_⟩
  · change diamondBaseTask.inside t.survivor=false
    rw [ht.2.2.1]
    exact (by decide : ∀ q : Bool, diamondBaseTask.inside (DiamondRoute.stub q)=false) (!p)
  · change decide (t.survivor=DiamondRoute.stub (!p))=true
    exact decide_eq_true ht.2.2.1
  · intro v hv; cases hv

theorem diamond_metric_target (p : Bool) (x : Fin 6) (hx : x.val<4) :
    (diamondTask (some x) (fun w => decide (w≠DiamondRoute.stub p))).MetricForcesWithin
      diamondPresentation.good 3 ⟨false,DiamondRoute.stub p,DiamondRoute.port p⟩ := by
  let T := diamondTask (some x) (fun w => decide (w≠DiamondRoute.stub p))
  let s : Position 6 := ⟨false,DiamondRoute.stub p,DiamondRoute.port p⟩
  apply T.fullGame_metricForcesWithin diamondPresentation.good diamondPresentation.boundary_leaves
    3 s (fun _ => False)
    ((by decide : ∀ p : Bool, diamondBaseTask.inside (DiamondRoute.port p)=true) p)
    ((by decide : ∀ p : Bool, diamondBaseTask.adj (DiamondRoute.stub p) (DiamondRoute.port p)=true) p)
    (by intro v hv hd; contradiction)
  have h := DiamondRoute.target_route p x hx (Task.fullState s (fun _ => False)) rfl rfl
  apply (diamondTaskIso (some x) (fun w => decide (w≠DiamondRoute.stub p))).forcesWithin h
  intro phase t ht
  refine ⟨ht.1,?_,?_,?_⟩
  · change diamondBaseTask.inside t.survivor=false
    rw [ht.2.2.1]
    exact (by decide : ∀ q : Bool, diamondBaseTask.inside (DiamondRoute.stub q)=false) (!p)
  · change decide (t.survivor≠DiamondRoute.stub p)=true
    rw [ht.2.2.1]
    exact decide_eq_true ((by decide : ∀ p : Bool, DiamondRoute.stub (!p)≠DiamondRoute.stub p) p)
  · intro v hv
    change some x=some v at hv
    exact Option.some.inj hv ▸ ht.2.2.2

end ZombieMain
