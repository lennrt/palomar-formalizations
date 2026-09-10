import ZombieMain.WholeGraphIso
import ZombieMain.MainDefinitions
import ZombieDamage.ExceptionTraps

namespace ZombieMain
open ZombieDamage

def prism3ExceptionLabels : Fin (closedDiagram 3 false).order ≃ Exceptions.Vertex .prism3 where
  toFun := ![0,3,1,4,2,5]
  invFun := (![0,2,4,1,3,5] : Fin 6 → Fin 6)
  left_inv := by decide
  right_inv := by decide

def cubeExceptionLabels : Fin (closedDiagram 4 false).order ≃ Exceptions.Vertex .cube where
  toFun := ![0,4,1,5,3,7,2,6]
  invFun := (![0,2,6,4,1,3,7,5] : Fin 8 → Fin 8)
  left_inv := by decide
  right_inv := by decide

def mobius3ExceptionLabels : Fin (closedDiagram 3 true).order ≃ Exceptions.Vertex .k33 where
  toFun := ![0,3,4,1,2,5]
  invFun := (![0,3,4,1,2,5] : Fin 6 → Fin 6)
  left_inv := by decide
  right_inv := by decide

theorem k4_exception_adj : ∀i j : Fin Family.k4.diagram.order,
    Family.k4.diagram.adj i.val j.val=true ↔ (Exceptions.graph .k4).adj i j := by decide

theorem k33_exception_adj : ∀i j : Fin Family.k33.diagram.order,
    Family.k33.diagram.adj i.val j.val=true ↔ (Exceptions.graph .k33).adj i j := by decide

theorem prism3_exception_adj : ∀i j : Fin (closedDiagram 3 false).order,
    (closedDiagram 3 false).adj i.val j.val=true ↔
    (Exceptions.graph .prism3).adj (prism3ExceptionLabels i) (prism3ExceptionLabels j) := by decide

theorem cube_exception_adj : ∀i j : Fin (closedDiagram 4 false).order,
    (closedDiagram 4 false).adj i.val j.val=true ↔
    (Exceptions.graph .cube).adj (cubeExceptionLabels i) (cubeExceptionLabels j) := by decide

theorem mobius3_exception_adj : ∀i j : Fin (closedDiagram 3 true).order,
    (closedDiagram 3 true).adj i.val j.val=true ↔
    (Exceptions.graph .k33).adj (mobius3ExceptionLabels i) (mobius3ExceptionLabels j) := by decide


theorem full_damage_not_exception {V : Type} {G : SimpleGraph V}
    (h : FullGame.FullDamage (gameGraph G)) : ¬IsException G := by
  rintro ⟨kind,⟨F⟩⟩
  exact Exceptions.not_full_damage kind (F.fullDamage_iff.mpr h)

theorem order_ten_not_exception {V : Type} [Fintype V] {G : SimpleGraph V}
    (hn : 10≤Fintype.card V) : ¬IsException G := by
  rintro ⟨kind,⟨F⟩⟩
  let E : Exceptions.Vertex kind ≃ V :=
    ⟨F.toFun,F.invFun,F.left_inv,F.right_inv⟩
  have hc := Fintype.card_congr E
  cases kind <;> simp [Exceptions.Vertex,Exceptions.order] at hc <;> omega

end ZombieMain
