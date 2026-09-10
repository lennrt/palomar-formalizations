import ZombieMain.GadgetRoutes
import ZombieMain.BaseRoutes
import ZombieMain.StripRoutes
import ZombieMain.ClosedDegree

namespace ZombieMain
open ZombieDamage

/-- Every admissible classified family possessing a port has complete local
routing proofs. Saturated closed families cannot satisfy the port hypothesis. -/
theorem Family.routes_of_port (f : Family) (hf : f.Admissible)
    (hp : ∃ i : Fin f.diagram.order,f.diagram.degree i.val=2) :
    Nonempty (RoutedPresentation f.diagram) := by
  cases f with
  | ladder m => exact ⟨stripRoutes m 0 hf (by omega)⟩
  | singleCap m =>
    by_cases hm : m=1
    · subst m; exact ⟨triangleRoutes⟩
    · have hm' : 2≤m := by change 1≤m at hf; omega
      exact ⟨stripRoutes m 1 hm' (by omega)⟩
  | doubleCap m =>
    by_cases hm : m=1
    · subst m; exact ⟨diamondRoutes⟩
    · have hm' : 2≤m := by change 1≤m at hf; omega
      exact ⟨stripRoutes m 2 hm' (by omega)⟩
  | k23 => exact ⟨gadgetRoutes .k23⟩
  | k33e => exact ⟨gadgetRoutes .k33e⟩
  | p3e => exact ⟨gadgetRoutes .prism3e⟩
  | q3v => exact ⟨gadgetRoutes .cubeV⟩
  | q3e => exact ⟨gadgetRoutes .cubeE⟩
  | prism m =>
    obtain ⟨i,hi⟩ := hp
    have hd := closed_degree m false hf i.val i.isLt
    change (closedDiagram m false).degree i.val=2 at hi
    omega
  | mobius m =>
    obtain ⟨i,hi⟩ := hp
    have hd := closed_degree m true hf i.val i.isLt
    change (closedDiagram m true).degree i.val=2 at hi
    omega
  | k4 => exact False.elim ((by decide : ¬∃i : Fin Family.k4.diagram.order,Family.k4.diagram.degree i.val=2) hp)
  | k33 => exact False.elim ((by decide : ¬∃i : Fin Family.k33.diagram.order,Family.k33.diagram.degree i.val=2) hp)

end ZombieMain
