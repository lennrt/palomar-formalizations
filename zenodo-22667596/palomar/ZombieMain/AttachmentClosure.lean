import ZombieMain.FiniteAttachments
import ZombieMain.TailAttachments
import ZombieMain.ClosedDegree

namespace ZombieMain

theorem Diagram.no_path_of_saturated {D : Diagram}
    (hd : ∀ v : Fin D.order, D.degree v.val = 3) {p q r : Nat} :
    ¬ D.LegalPath p q r := by
  intro h
  have h3 : D.degree p = 3 := hd ⟨p,h.1⟩
  have h2 := h.2.2.2.1
  omega

theorem Diagram.no_matching_of_saturated {D : Diagram}
    (hd : ∀ v : Fin D.order, D.degree v.val = 3) {a b c d : Nat} :
    ¬ D.LegalMatching a b c d := by
  intro h
  have h3 : D.degree a = 3 := hd ⟨a,h.1⟩
  have h2 := h.2.2.2.2.2.1
  omega

theorem k4_saturated : ∀ v : Fin Family.k4.diagram.order,
    Family.k4.diagram.degree v.val = 3 := by decide

theorem k33_saturated : ∀ v : Fin Family.k33.diagram.order,
    Family.k33.diagram.degree v.val = 3 := by decide

/-- The complete Type A transition theorem, with unbounded family parameters. -/
theorem Family.path_classified (f : Family) (hf : f.Admissible) {p q r : Nat}
    (h : f.diagram.LegalPath p q r) : (f.diagram.adjoinPath p q r).Classified := by
  by_cases hs : f ∈ smallOpenFamilies
  · exact FiniteAttachments.small_path hs h
  cases f with
  | ladder m =>
    have hm : 5 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 2 ≤ m at hf
      omega
    exact large_ladder_path_classified hm h
  | singleCap m =>
    have hm : 4 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 1 ≤ m at hf
      omega
    exact large_singleCap_path_classified hm h
  | doubleCap m =>
    have hm : 3 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 1 ≤ m at hf
      omega
    exact False.elim (large_doubleCap_no_path hm h)
  | prism m => exact False.elim (closed_no_path hf h)
  | mobius m => exact False.elim (closed_no_path hf h)
  | k23 | k33e | p3e | q3v | q3e => exact False.elim (hs (by decide))
  | k4 => exact False.elim (Diagram.no_path_of_saturated k4_saturated h)
  | k33 => exact False.elim (Diagram.no_path_of_saturated k33_saturated h)

/-- The complete Type B transition theorem, with unbounded family parameters. -/
theorem Family.matching_classified (f : Family) (hf : f.Admissible) {a b c d : Nat}
    (h : f.diagram.LegalMatching a b c d) :
    (f.diagram.adjoinMatching a b c d).Classified := by
  by_cases hs : f ∈ smallOpenFamilies
  · exact FiniteAttachments.small_matching hs h
  cases f with
  | ladder m =>
    have hm : 3 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 2 ≤ m at hf
      omega
    exact large_ladder_matching_classified hm h
  | singleCap m =>
    have hm : 2 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 1 ≤ m at hf
      omega
    exact False.elim (capped_no_matching hm (by decide) (by decide) h)
  | doubleCap m =>
    have hm : 2 ≤ m := by
      simp [smallOpenFamilies] at hs
      change 1 ≤ m at hf
      omega
    exact False.elim (capped_no_matching hm (by decide) (by decide) h)
  | prism m => exact False.elim (closed_no_matching hf h)
  | mobius m => exact False.elim (closed_no_matching hf h)
  | k23 | k33e | p3e | q3v | q3e => exact False.elim (hs (by decide))
  | k4 => exact False.elim (Diagram.no_matching_of_saturated k4_saturated h)
  | k33 => exact False.elim (Diagram.no_matching_of_saturated k33_saturated h)

end ZombieMain
