import ZombieMain.Diagram

namespace ZombieMain.Diagram

theorem adjoinPath_one (D : Diagram) (p q u v : Nat) :
    (D.adjoinPath p q 1).adj u v = true ↔
      (u < D.order ∧ v < D.order ∧ D.adj u v = true) ∨
      (u=p ∧ v=q) ∨ (v=p ∧ u=q) := by
  simp [adjoinPath, pathAdj]
  tauto

theorem adjoinPath_two (D : Diagram) (p q u v : Nat) :
    (D.adjoinPath p q 2).adj u v = true ↔
      (u < D.order ∧ v < D.order ∧ D.adj u v = true) ∨
      (u=p ∧ v=D.order) ∨ (v=p ∧ u=D.order) ∨
      (u=D.order ∧ v=q) ∨ (v=D.order ∧ u=q) := by
  simp [adjoinPath, pathAdj, List.range_succ]
  tauto

theorem adjoinPath_three (D : Diagram) (p q u v : Nat) :
    (D.adjoinPath p q 3).adj u v = true ↔
      (u < D.order ∧ v < D.order ∧ D.adj u v = true) ∨
      (u=p ∧ v=D.order) ∨ (v=p ∧ u=D.order) ∨
      (u=D.order ∧ v=D.order+1) ∨ (v=D.order ∧ u=D.order+1) ∨
      (u=D.order+1 ∧ v=q) ∨ (v=D.order+1 ∧ u=q) := by
  simp [adjoinPath, pathAdj, List.range_succ]
  tauto

end ZombieMain.Diagram
