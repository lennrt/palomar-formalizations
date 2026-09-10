import ZombieMain.StripTailRestrictions
import ZombieMain.PathAdjacency

namespace ZombieMain
set_option maxHeartbeats 1000000

def endVertex (m : Nat) (side parity : Bool) : Nat :=
  (if side then 2*m-2 else 0) + (if parity then 1 else 0)

def extendLadderForward (m : Nat) (side flip : Bool) (u : Nat) : Nat :=
  if u < 2*m then (if side then u else u+2)
  else (if side then 2*m else 0) +
    (if u = 2*m then (if flip then 1 else 0) else (if flip then 0 else 1))

def extendLadderBackward (m : Nat) (side flip : Bool) (u : Nat) : Nat :=
  if side then
    if u < 2*m then u else 2*m + (if u = 2*m+(if flip then 1 else 0) then 0 else 1)
  else
    if 2 ≤ u then u-2 else 2*m + (if u = (if flip then 1 else 0) then 0 else 1)

/-- A square on either end rung extends the ladder by exactly one rung;
the order of the new two vertices is explicitly accounted for. -/
def ladder_extend_iso (m : Nat) (hm : 2 ≤ m) (side flip : Bool) :
    ((stripDiagram m 0).adjoinPath (endVertex m side flip) (endVertex m side (!flip)) 3).Iso
      (stripDiagram (m+1) 0) := by
  apply Diagram.isoOfNat _ _ (extendLadderForward m side flip) (extendLadderBackward m side flip)
  · intro u hu
    change u < 2*m+0+(3-1) at hu
    change extendLadderForward m side flip u < 2*(m+1)+0
    cases side <;> cases flip <;> dsimp [extendLadderForward] <;> split_ifs <;> omega
  · intro u hu
    change u < 2*(m+1)+0 at hu
    change extendLadderBackward m side flip u < 2*m+0+(3-1)
    cases side <;> cases flip <;> dsimp [extendLadderBackward] <;> split_ifs <;> omega
  · intro u hu
    change u < 2*m+0+(3-1) at hu
    cases side <;> cases flip <;> dsimp [extendLadderBackward, extendLadderForward] <;>
      split_ifs <;> simp_all <;> omega
  · intro u hu
    change u < 2*(m+1)+0 at hu
    cases side <;> cases flip <;> dsimp [extendLadderBackward, extendLadderForward] <;>
      split_ifs <;> simp_all <;> omega
  · intro u v hu hv
    change u < 2*m+0+(3-1) at hu
    change v < 2*m+0+(3-1) at hv
    apply Bool.eq_iff_iff.mpr
    rw [Diagram.adjoinPath_three]
    simp only [stripDiagram, decide_eq_true_eq]
    cases side <;> cases flip <;>
      dsimp [endVertex, extendLadderForward] <;>
      split_ifs <;> simp [stripAdj] <;> omega

end ZombieMain
