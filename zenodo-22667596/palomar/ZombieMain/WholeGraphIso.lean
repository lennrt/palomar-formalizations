import ZombieMain.ClosedClassification
import ZombieDamage.Isomorphism

namespace ZombieMain.Diagram.Embedding
open SimpleGraph ZombieDamage
variable {V : Type} {G : SimpleGraph V} {D : Diagram}

noncomputable def wholeEquiv (e : D.Embedding (⊤ : G.Subgraph)) : Fin D.order ≃ V :=
  Equiv.ofBijective e.vertices ⟨e.injective,fun v => e.exists_label (by trivial)⟩

@[simp] theorem wholeEquiv_apply (e : D.Embedding (⊤ : G.Subgraph)) (i : Fin D.order) :
    e.wholeEquiv i=e.vertices i := rfl

/-- Relabel an explicit closed game graph onto the original vertex type. -/
noncomputable def gameIso (e : D.Embedding (⊤ : G.Subgraph))
    {W : Type} (H : Graph W) (labels : Fin D.order ≃ W)
    (hadj : ∀i j,D.adj i.val j.val=true ↔ H.adj (labels i) (labels j)) :
    GraphIso H (gameGraph G) where
  toFun u := e.wholeEquiv (labels.symm u)
  invFun v := labels (e.wholeEquiv.symm v)
  left_inv u := by simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  right_inv v := by simp only [Equiv.symm_apply_apply,Equiv.apply_symm_apply]
  adjacency u v := by
    have he := e.adjacency (labels.symm u) (labels.symm v)
    have hl := hadj (labels.symm u) (labels.symm v)
    simp only [Equiv.apply_symm_apply] at hl
    exact hl.symm.trans he

theorem whole_order [Fintype V] (e : D.Embedding (⊤ : G.Subgraph)) :
    D.order=Fintype.card V := by
  have h := Fintype.card_congr e.wholeEquiv
  simpa only [Fintype.card_fin] using h

end ZombieMain.Diagram.Embedding
