import ZombieMain.AttachOneVertex
import Mathlib.Data.Fin.VecNotation

namespace ZombieMain.Diagram.Embedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {H J : G.Subgraph} {D : Diagram}
set_option maxHeartbeats 1000000

def attachTwo (e : D.Embedding H) (p q : Fin D.order) (x y : V)
    (hx : x ∉ H.verts) (hy : y ∉ H.verts) (hxy : x ≠ y)
    (hv : ∀ v, v ∈ J.verts ↔ v ∈ H.verts ∨ v=x ∨ v=y)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=x) ∨ (v=e.vertices p ∧ u=x) ∨
      (u=x ∧ v=y) ∨ (v=x ∧ u=y) ∨
      (u=y ∧ v=e.vertices q) ∨ (v=y ∧ u=e.vertices q)) :
    (D.adjoinPath p.val q.val 3).Embedding J := by
  classical
  have hnx : ∀ i, e.vertices i ≠ x := fun i h => hx (h ▸ e.mem i)
  have hny : ∀ i, e.vertices i ≠ y := fun i h => hy (h ▸ e.mem i)
  have hnx' : ∀ i, x ≠ e.vertices i := fun i => (hnx i).symm
  have hny' : ∀ i, y ≠ e.vertices i := fun i => (hny i).symm
  have hxR : ∀ u, ¬ H.Adj u x := fun _ h => hx h.snd_mem
  have hyR : ∀ u, ¬ H.Adj u y := fun _ h => hy h.snd_mem
  have hxL : ∀ u, ¬ H.Adj x u := fun _ h => hx h.fst_mem
  have hyL : ∀ u, ¬ H.Adj y u := fun _ h => hy h.fst_mem
  have hbound : ∀ i : Fin D.order, i.val ≠ D.order ∧ i.val ≠ D.order+1 := by
    intro i
    have hi := i.isLt
    omega
  have hbound' : ∀ i : Fin D.order, D.order ≠ i.val ∧ D.order+1 ≠ i.val := by
    intro i
    exact ⟨(hbound i).1.symm, (hbound i).2.symm⟩
  refine ⟨Fin.append e.vertices ![x,y], ?_, ?_, ?_⟩
  · change Function.Injective (Fin.append e.vertices ![x,y])
    apply Fin.append_injective_iff.mpr
    refine ⟨e.injective, ?_, ?_⟩
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i j
      fin_cases j <;> simp [hnx, hny]
  · ext v
    rw [hv]
    constructor
    · rintro ⟨i,rfl⟩
      cases i using @Fin.addCases D.order 2 with
      | left i => exact Or.inl (by simpa using e.mem i)
      | right i => fin_cases i <;> simp
    · rintro (h | rfl | rfl)
      · obtain ⟨i,rfl⟩ := e.exists_label h
        exact ⟨i.castAdd 2, by simp⟩
      · exact ⟨Fin.natAdd D.order 0, by simp⟩
      · exact ⟨Fin.natAdd D.order 1, by simp⟩
  · intro u v
    rw [Diagram.adjoinPath_three, ha]
    cases u using @Fin.addCases D.order 2 with
    | left u =>
      cases v using @Fin.addCases D.order 2 with
      | left v =>
        simp [u.isLt, v.isLt, hbound, hbound', hnx, hny, hnx', hny',
          e.adjacency, @eq_comm V, @eq_comm Nat]
      | right v =>
        fin_cases v <;>
          simp [u.isLt, hbound, hbound', hnx, hny, hnx', hny', hxR, hyR, hxL, hyL,
            hxy, hxy.symm, e.injective.eq_iff, Fin.ext_iff, @eq_comm V, @eq_comm Nat]
    | right u =>
      cases v using @Fin.addCases D.order 2 with
      | left v =>
        fin_cases u <;>
          simp [v.isLt, hbound, hbound', hnx, hny, hnx', hny', hxR, hyR, hxL, hyL,
            hxy, hxy.symm, e.injective.eq_iff, Fin.ext_iff, @eq_comm V, @eq_comm Nat]
      | right v =>
        fin_cases u <;> fin_cases v <;>
          simp [hbound, hbound', hnx, hny, hnx', hny', hxR, hyR, hxL, hyL,
            hxy, hxy.symm, @eq_comm V, @eq_comm Nat]

end ZombieMain.Diagram.Embedding
