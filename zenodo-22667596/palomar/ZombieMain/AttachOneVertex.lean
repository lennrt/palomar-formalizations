import ZombieMain.EmbeddingFacts
import ZombieMain.PathAdjacency
import Mathlib.Data.Fin.Tuple.Basic

namespace ZombieMain.Diagram.Embedding
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {H J : G.Subgraph} {D : Diagram}
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

/-- Extend an exact diagram copy by a fresh vertex joined to two specified
old labels. Both the vertex set and every adjacency are checked. -/
def attachOne (e : D.Embedding H) (p q : Fin D.order) (x : V)
    (hx : x ∉ H.verts)
    (hv : ∀ v, v ∈ J.verts ↔ v ∈ H.verts ∨ v=x)
    (ha : ∀ u v, J.Adj u v ↔ H.Adj u v ∨
      (u=e.vertices p ∧ v=x) ∨ (v=e.vertices p ∧ u=x) ∨
      (u=x ∧ v=e.vertices q) ∨ (v=x ∧ u=e.vertices q)) :
    (D.adjoinPath p.val q.val 2).Embedding J := by
  classical
  have hne : ∀ i, e.vertices i ≠ x := by
    intro i h
    exact hx (h ▸ e.mem i)
  have hne' : ∀ i, x ≠ e.vertices i := fun i => (hne i).symm
  have hn : ∀ u, ¬ H.Adj u x := fun _ h => hx h.snd_mem
  have hn' : ∀ u, ¬ H.Adj x u := fun _ h => hx h.fst_mem
  refine ⟨Fin.append e.vertices (fun _ : Fin 1 => x), ?_, ?_, ?_⟩
  · change Function.Injective (Fin.append e.vertices (fun _ : Fin 1 => x))
    apply Fin.append_injective_iff.mpr
    exact ⟨e.injective, fun _ _ _ => Subsingleton.elim _ _, fun i _ => hne i⟩
  · ext v
    rw [hv]
    constructor
    · rintro ⟨i,rfl⟩
      cases i using @Fin.addCases D.order 1 with
      | left i => exact Or.inl (by simpa using e.mem i)
      | right i => exact Or.inr (by simp)
    · rintro (h | rfl)
      · obtain ⟨i,rfl⟩ := e.exists_label h
        exact ⟨i.castAdd 1, by simp⟩
      · exact ⟨Fin.natAdd D.order 0, by simp⟩
  · intro u v
    rw [Diagram.adjoinPath_two, ha]
    cases u using @Fin.addCases D.order 1 with
    | left u =>
      cases v using @Fin.addCases D.order 1 with
      | left v =>
        simp [u.isLt, v.isLt, u.isLt.ne, v.isLt.ne, hne, hn, hn',
          e.adjacency, @eq_comm V, @eq_comm Nat, @eq_comm (Fin D.order)]
      | right v =>
        have hzero : v = 0 := Subsingleton.elim _ _
        subst v
        simp [u.isLt, u.isLt.ne, hne, hn, hn', e.injective.eq_iff,
          Fin.ext_iff, @eq_comm V, @eq_comm Nat, @eq_comm (Fin D.order)]
    | right u =>
      have hzero : u = 0 := Subsingleton.elim _ _
      subst u
      cases v using @Fin.addCases D.order 1 with
      | left v =>
        simp [v.isLt, v.isLt.ne, hne, hn, hn', e.injective.eq_iff,
          Fin.ext_iff, @eq_comm V, @eq_comm Nat, @eq_comm (Fin D.order)]
      | right v =>
        have hzero : v = 0 := Subsingleton.elim _ _
        subst v
        simp [p.isLt.ne, q.isLt.ne, p.isLt.ne.symm, q.isLt.ne.symm, hne, hne', hn, hn', @eq_comm V, @eq_comm Nat, @eq_comm (Fin D.order)]

end ZombieMain.Diagram.Embedding
