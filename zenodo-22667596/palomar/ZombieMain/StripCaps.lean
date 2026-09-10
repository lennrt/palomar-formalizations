import ZombieMain.StripTailRestrictions
import ZombieMain.PathAdjacency

namespace ZombieMain
set_option maxHeartbeats 1000000

def reverseStrip (m u : Nat) : Nat :=
  if u < 2*m then 2*(m-1-u/2)+u%2 else u

theorem reverseStrip_bound (m u : Nat) (hm : 2 ≤ m) (hu : u < 2*m+1) :
    reverseStrip m u < 2*m+1 := by
  dsimp [reverseStrip]
  split_ifs <;> omega

theorem reverseStrip_involutive (m u : Nat) (hm : 2 ≤ m) (hu : u < 2*m+1) :
    reverseStrip m (reverseStrip m u) = u := by
  dsimp [reverseStrip]
  split_ifs <;> omega

/-- Adding a triangle at the left end creates the left cap. -/
def ladder_left_cap_iso (m : Nat) (hm : 2 ≤ m) (flip : Bool) :
    ((stripDiagram m 0).adjoinPath (if flip then 1 else 0)
      (if flip then 0 else 1) 2).Iso (stripDiagram m 1) := by
  apply Diagram.isoOfNat _ _ id id
  · intro u hu; exact hu
  · intro u hu; exact hu
  · intro u _; rfl
  · intro u _; rfl
  · intro u v hu hv
    change u < 2*m+1 at hu
    change v < 2*m+1 at hv
    apply Bool.eq_iff_iff.mpr
    rw [Diagram.adjoinPath_two]
    simp only [stripDiagram, decide_eq_true_eq]
    cases flip <;> dsimp <;>
      simp [stripAdj] <;> omega

/-- Adding a triangle at the right end creates the same singly capped
ladder after reversal of the rung order. -/
def ladder_right_cap_iso (m : Nat) (hm : 2 ≤ m) (flip : Bool) :
    ((stripDiagram m 0).adjoinPath (2*m-2+(if flip then 1 else 0))
      (2*m-2+(if flip then 0 else 1)) 2).Iso (stripDiagram m 1) := by
  apply Diagram.isoOfNat _ _ (reverseStrip m) (reverseStrip m)
  · intro u hu; exact reverseStrip_bound m u hm hu
  · intro u hu; exact reverseStrip_bound m u hm hu
  · intro u hu; exact reverseStrip_involutive m u hm hu
  · intro u hu; exact reverseStrip_involutive m u hm hu
  · intro u v hu hv
    change u < 2*m+1 at hu
    change v < 2*m+1 at hv
    apply Bool.eq_iff_iff.mpr
    rw [Diagram.adjoinPath_two]
    simp only [stripDiagram, decide_eq_true_eq]
    cases flip <;> dsimp [reverseStrip] <;> split_ifs <;>
      simp [stripAdj] <;> omega

/-- Capping the remaining end of a singly capped ladder creates a double cap. -/
def singleCap_cap_iso (m : Nat) (hm : 2 ≤ m) (flip : Bool) :
    ((stripDiagram m 1).adjoinPath (2*m-2+(if flip then 1 else 0))
      (2*m-2+(if flip then 0 else 1)) 2).Iso (stripDiagram m 2) := by
  apply Diagram.isoOfNat _ _ id id
  · intro u hu; exact hu
  · intro u hu; exact hu
  · intro u _; rfl
  · intro u _; rfl
  · intro u v hu hv
    change u < 2*m+2 at hu
    change v < 2*m+2 at hv
    apply Bool.eq_iff_iff.mpr
    rw [Diagram.adjoinPath_two]
    simp only [stripDiagram, decide_eq_true_eq]
    cases flip <;> dsimp <;>
      simp [stripAdj] <;> omega

end ZombieMain
