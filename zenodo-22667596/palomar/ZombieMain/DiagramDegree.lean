import ZombieMain.Diagram

namespace ZombieMain.Diagram

/-- Exact degree from an explicit list of distinct, in-range neighbors. -/
theorem degree_eq_length (D : Diagram) (u : Nat) (neighbors : List Nat)
    (hbound : ∀ w ∈ neighbors, w < D.order) (hnodup : neighbors.Nodup)
    (hadj : ∀ w : Fin D.order, D.adj u w.val = true ↔ w.val ∈ neighbors) :
    D.degree u = neighbors.length := by
  let S := Finset.univ.filter (fun w : Fin D.order => D.adj u w.val)
  have heq : S.image Fin.val = neighbors.toFinset := by
    ext w
    simp only [Finset.mem_image, List.mem_toFinset]
    constructor
    · rintro ⟨v, hv, rfl⟩
      apply (hadj v).mp
      simpa [S] using hv
    · intro hw
      refine ⟨⟨w, hbound w hw⟩, ?_, rfl⟩
      simpa [S] using (hadj ⟨w, hbound w hw⟩).mpr hw
  have hc := Finset.card_image_of_injective S Fin.val_injective
  rw [heq, List.toFinset_card_of_nodup hnodup] at hc
  exact hc.symm

/-- Any integer coordinate changing by at most one on an edge changes by at
most k on a path found by the finite reachability predicate. -/
theorem reach_coordinate (D : Diagram) (coord : Nat → Int)
    (hstep : ∀ u v, u < D.order → v < D.order → D.adj u v = true →
      coord u ≤ coord v+1 ∧ coord v ≤ coord u+1) :
    ∀ k u v, u < D.order → v < D.order → D.reach k u v = true →
      coord u ≤ coord v+k ∧ coord v ≤ coord u+k := by
  intro k
  induction k with
  | zero =>
    intro u v _ _ h
    have he : u = v := by simpa [reach] using h
    subst v
    simp
  | succ k ih =>
    intro u v hu hv h
    simp only [reach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · constructor <;> omega
    · obtain ⟨w, hw, he⟩ := List.any_eq_true.mp h
      have hw' : w < D.order := List.mem_range.mp hw
      have hh : D.adj u w = true ∧ D.reach k w v = true := by simpa using he
      obtain ⟨huw, hwv⟩ := hh
      obtain ⟨h₁, h₂⟩ := hstep u w hu hw' huw
      obtain ⟨h₃, h₄⟩ := ih w v hw' hv hwv
      constructor <;> push_cast <;> omega

end ZombieMain.Diagram
