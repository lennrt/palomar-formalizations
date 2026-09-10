import ZombieMain.StripCaps
import ZombieMain.StripExtensions
import ZombieMain.SingleCapExtension
import ZombieMain.MatchingClosures

namespace ZombieMain

theorem ladder_end_path_classified {m p q r : Nat} (hm : 2 ≤ m)
    (hpq : EndPair m p q) (hr : r=2 ∨ r=3) :
    ((stripDiagram m 0).adjoinPath p q r).Classified := by
  have he : 2*m-2+1 = 2*m-1 := by omega
  rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hr with rfl | rfl
    · exact Or.inr ⟨.singleCap m, by simp only [Family.Admissible]; omega, ⟨ladder_left_cap_iso m hm false⟩⟩
    · exact Or.inr ⟨.ladder (m+1), by simp only [Family.Admissible]; omega, ⟨ladder_extend_iso m hm false false⟩⟩
  · rcases hr with rfl | rfl
    · exact Or.inr ⟨.singleCap m, by simp only [Family.Admissible]; omega, ⟨ladder_left_cap_iso m hm true⟩⟩
    · exact Or.inr ⟨.ladder (m+1), by simp only [Family.Admissible]; omega, ⟨ladder_extend_iso m hm false true⟩⟩
  · rcases hr with rfl | rfl
    · refine Or.inr ⟨.singleCap m, by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using ladder_right_cap_iso m hm false
    · refine Or.inr ⟨.ladder (m+1), by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, endVertex, he] using ladder_extend_iso m hm true false
  · rcases hr with rfl | rfl
    · refine Or.inr ⟨.singleCap m, by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using ladder_right_cap_iso m hm true
    · refine Or.inr ⟨.ladder (m+1), by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, endVertex, he] using ladder_extend_iso m hm true true

theorem large_ladder_path_classified {m p q r : Nat} (hm : 5 ≤ m)
    (h : (stripDiagram m 0).LegalPath p q r) :
    ((stripDiagram m 0).adjoinPath p q r).Classified := by
  obtain ⟨hpq,hr⟩ := large_ladder_path_restriction hm h
  exact ladder_end_path_classified (by omega) hpq hr

theorem large_singleCap_path_classified {m p q r : Nat} (hm : 4 ≤ m)
    (h : (stripDiagram m 1).LegalPath p q r) :
    ((stripDiagram m 1).adjoinPath p q r).Classified := by
  have he : 2*m-2+1 = 2*m-1 := by omega
  obtain ⟨hpq,hr⟩ := large_singleCap_path_restriction hm h
  rcases hpq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rcases hr with rfl | rfl
    · refine Or.inr ⟨.doubleCap m, by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using singleCap_cap_iso m (by omega) false
    · refine Or.inr ⟨.singleCap (m+1), by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using singleCap_extend_iso m (by omega) false
  · rcases hr with rfl | rfl
    · refine Or.inr ⟨.doubleCap m, by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using singleCap_cap_iso m (by omega) true
    · refine Or.inr ⟨.singleCap (m+1), by simp only [Family.Admissible]; omega, ⟨?_⟩⟩
      simpa [Family.diagram, he] using singleCap_extend_iso m (by omega) true

end ZombieMain
