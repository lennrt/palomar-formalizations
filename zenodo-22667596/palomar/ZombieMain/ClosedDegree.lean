import ZombieMain.DiagramDegree
import ZombieMain.Families

namespace ZombieMain
set_option maxHeartbeats 1000000

def closedNeighbors (m : Nat) (twisted : Bool) (u : Nat) : List Nat :=
  if u < 2 then
    [1-u, u+2, if twisted then 2*m-1-u else 2*m-2+u]
  else if 2*m ≤ u+2 then
    [2*(u/2)+(1-u%2), u-2, if twisted then 2*m-1-u else u+2-2*m]
  else [2*(u/2)+(1-u%2), u-2, u+2]

theorem closed_degree (m : Nat) (twisted : Bool) (hm : 3 ≤ m)
    (u : Nat) (hu : u < 2*m) : (closedDiagram m twisted).degree u = 3 := by
  have he : (closedDiagram m twisted).degree u = (closedNeighbors m twisted u).length := by
    apply Diagram.degree_eq_length
    · intro w hw
      change w < 2*m
      cases twisted <;> dsimp [closedNeighbors] at hw <;>
        split_ifs at hw <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hw <;> omega
    · cases twisted <;> dsimp [closedNeighbors] <;> split_ifs <;>
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          not_false_eq_true, and_true, not_or] <;> omega
    · intro w
      have hw : w.val < 2*m := w.isLt
      cases twisted <;> simp only [closedDiagram, Bool.false_eq_true, if_false,
        if_true, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      all_goals dsimp [closedNeighbors] <;> split_ifs <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false]
      all_goals simp [stripAdj] <;> omega
  rw [he]
  dsimp [closedNeighbors]
  split_ifs <;> rfl

theorem closed_no_path {m p q r : Nat} {twisted : Bool} (hm : 3 ≤ m) :
    ¬ (closedDiagram m twisted).LegalPath p q r := by
  intro h
  have hd := closed_degree m twisted hm p h.1
  have hp := h.2.2.2.1
  omega

theorem closed_no_matching {m a b c d : Nat} {twisted : Bool} (hm : 3 ≤ m) :
    ¬ (closedDiagram m twisted).LegalMatching a b c d := by
  intro h
  have hd := closed_degree m twisted hm a h.1
  have hp := h.2.2.2.2.2.1
  omega

end ZombieMain
