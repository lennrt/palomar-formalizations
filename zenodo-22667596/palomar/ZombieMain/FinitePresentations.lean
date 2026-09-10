import ZombieMain.PortedPresentation
import ZombieDamage.Gadgets
import ZombieDamage.TriangleRoute
import ZombieDamage.DiamondRoute

namespace ZombieMain
open ZombieDamage
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

instance {N : Nat} (T : Task N) : Decidable T.BoundaryLeaves := by
  unfold Task.BoundaryLeaves
  infer_instance

def gadgetFamily : Gadget → Family
  | .k23 => .k23
  | .k33e => .k33e
  | .prism3e => .p3e
  | .cubeV => .q3v
  | .cubeE => .q3e

def gadgetBaseTask (g : Gadget) : Task g.size where
  adj := g.adj
  inside := g.inside
  target := none
  allowedExit := fun _ => false

def gadgetInternal (g : Gadget) (i : Fin (gadgetFamily g).diagram.order) : g.Vertex :=
  ⟨i.val, lt_of_lt_of_le i.isLt (by cases g <;> decide)⟩

/-- The five literal finite graphs match their checked game models,
including every boundary leaf and every degree-two port. -/
def gadgetPresentation (g : Gadget) :
    PortedPresentation (gadgetBaseTask g) (gadgetFamily g).diagram := by
  refine ⟨gadgetInternal g,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cases g <;> decide

def triangleBaseTask : Task 6 where
  adj u v := decide (TriangleRoute.Adj u v)
  inside u := decide (u.val<3)
  target := none
  allowedExit := fun _ => false

def triangleInternal (i : Fin (stripDiagram 1 1).order) : Fin 6 :=
  ⟨i.val,lt_of_lt_of_le i.isLt (by decide)⟩

def trianglePresentation : PortedPresentation triangleBaseTask (stripDiagram 1 1) := by
  refine ⟨triangleInternal,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide

def diamondBaseTask : Task 6 where
  adj u v := decide (DiamondRoute.Adj u v)
  inside u := decide (u.val<4)
  target := none
  allowedExit := fun _ => false

def diamondInternal (i : Fin (stripDiagram 1 2).order) : Fin 6 :=
  ![1,2,0,3] i

def diamondPresentation : PortedPresentation diamondBaseTask (stripDiagram 1 2) := by
  refine ⟨diamondInternal,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals decide

end ZombieMain
