import ZombieMain.StripTailRestrictions
import ZombieMain.PathAdjacency

namespace ZombieMain
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192

def extendCapForward (m : Nat) (flip : Bool) (u : Nat) : Nat :=
  if u < 2*m then u else if u=2*m then 2*m+2 else
    2*m+(if u=2*m+1 then (if flip then 1 else 0) else (if flip then 0 else 1))

def extendCapBackward (m : Nat) (flip : Bool) (u : Nat) : Nat :=
  if u < 2*m then u else if u=2*m+2 then 2*m else
    2*m+1+(if u=2*m+(if flip then 1 else 0) then 0 else 1)

/-- Extending the open end preserves the left cap. The old cap is moved
past the two new rail labels by the explicit inverse permutations. -/
def singleCap_extend_iso (m : Nat) (hm : 2 ≤ m) (flip : Bool) :
    ((stripDiagram m 1).adjoinPath (2*m-2+(if flip then 1 else 0))
      (2*m-2+(if flip then 0 else 1)) 3).Iso (stripDiagram (m+1) 1) := by
  apply Diagram.isoOfNat _ _ (extendCapForward m flip) (extendCapBackward m flip)
  · intro u hu
    change u < 2*m+1+(3-1) at hu
    change extendCapForward m flip u < 2*(m+1)+1
    cases flip <;> dsimp [extendCapForward] <;> split_ifs <;> omega
  · intro u hu
    change u < 2*(m+1)+1 at hu
    change extendCapBackward m flip u < 2*m+1+(3-1)
    cases flip <;> dsimp [extendCapBackward] <;> split_ifs <;> omega
  · intro u hu
    change u < 2*m+1+(3-1) at hu
    by_cases h : u < 2*m
    · simp [extendCapForward, extendCapBackward, h]
    · have hx : u=2*m ∨ u=2*m+1 ∨ u=2*m+2 := by omega
      rcases hx with rfl | rfl | rfl <;> cases flip <;>
        simp [extendCapForward, extendCapBackward] <;> split_ifs <;> omega
  · intro u hu
    change u < 2*(m+1)+1 at hu
    by_cases h : u < 2*m
    · simp [extendCapForward, extendCapBackward, h]
    · have hx : u=2*m ∨ u=2*m+1 ∨ u=2*m+2 := by omega
      rcases hx with rfl | rfl | rfl <;> cases flip <;>
        simp [extendCapForward, extendCapBackward] <;> split_ifs <;> omega
  · intro u v hu hv
    change u < 2*m+1+(3-1) at hu
    change v < 2*m+1+(3-1) at hv
    apply Bool.eq_iff_iff.mpr
    rw [Diagram.adjoinPath_three]
    simp only [stripDiagram, decide_eq_true_eq]
    have hcases : ∀ x : Nat, x < 2*m+3 → x < 2*m ∨ x=2*m ∨ x=2*m+1 ∨ x=2*m+2 := by
      intro x hx
      omega
    rcases hcases u (by omega) with huold | rfl | rfl | rfl
    all_goals rcases hcases v (by omega) with hvold | rfl | rfl | rfl
    all_goals cases flip <;>
      simp [extendCapForward, stripAdj, *] <;> omega

end ZombieMain
