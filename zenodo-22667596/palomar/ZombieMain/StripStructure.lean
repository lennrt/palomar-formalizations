import ZombieMain.Families
import ZombieMain.DiagramDegree

namespace ZombieMain

def stripNeighbors (m caps u : Nat) : List Nat :=
  if u < 2*m then
    (2*(u/2)+(1-u%2)) ::
      ((if u/2 = 0 then (if 1 ≤ caps then [2*m] else []) else [u-2]) ++
       (if u/2+1 = m then (if 2 ≤ caps then [2*m+1] else []) else [u+2]))
  else if u = 2*m then [0,1] else [2*m-2,2*m-1]

def StripPort (m caps u : Nat) : Prop :=
  (u < 2*m ∧ ((u < 2 ∧ caps = 0) ∨ (2*m ≤ u+2 ∧ caps ≤ 1))) ∨ 2*m ≤ u

theorem strip_degree_neighbors (m caps u : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    (hu : u < 2*m+caps) :
    (stripDiagram m caps).degree u = (stripNeighbors m caps u).length := by
  apply Diagram.degree_eq_length
  · intro w hw
    dsimp [stripNeighbors] at hw
    split_ifs at hw <;> simp only [List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, false_or] at hw <;> change w < 2*m+caps <;> omega
  · dsimp [stripNeighbors]
    split_ifs <;> simp only [List.nil_append, List.append_nil, List.cons_append,
      List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_false_eq_true, and_true, not_or] <;> omega
  · intro w
    have hwbound : w.val < 2*m+caps := w.isLt
    change decide (stripAdj m caps u w.val) = true ↔ w.val ∈ stripNeighbors m caps u
    rw [decide_eq_true_eq]
    dsimp [stripNeighbors]
    split_ifs <;> simp only [List.mem_cons, List.mem_append, List.mem_singleton,
      List.not_mem_nil, or_false, false_or] <;> unfold stripAdj <;> omega

theorem strip_degree_bounds (m caps u : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    (hu : u < 2*m+caps) :
    2 ≤ (stripDiagram m caps).degree u ∧ (stripDiagram m caps).degree u ≤ 3 := by
  rw [strip_degree_neighbors m caps u hm hc hu]
  dsimp [stripNeighbors]
  split_ifs <;> simp_all <;> omega

theorem strip_port_iff (m caps u : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    (hu : u < 2*m+caps) :
    (stripDiagram m caps).degree u = 2 ↔ StripPort m caps u := by
  rw [strip_degree_neighbors m caps u hm hc hu]
  dsimp [stripNeighbors]
  split_ifs <;> simp only [List.length_cons, List.length_append, List.length_nil, true_iff, false_iff] <;>
    unfold StripPort <;> omega

def stripCoordinate (m u : Nat) : Int :=
  if u < 2*m then u/2 else if u = 2*m then -1 else m

theorem strip_coordinate_step (m caps : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    {u v : Nat} (hu : u < 2*m+caps) (hv : v < 2*m+caps)
    (hadj : (stripDiagram m caps).adj u v = true) :
    stripCoordinate m u ≤ stripCoordinate m v+1 ∧
      stripCoordinate m v ≤ stripCoordinate m u+1 := by
  have ha : stripAdj m caps u v := of_decide_eq_true hadj
  dsimp [stripCoordinate]
  split_ifs <;> unfold stripAdj at ha <;> omega

theorem strip_reach_coordinate (m caps k u v : Nat) (hm : 2 ≤ m) (hc : caps ≤ 2)
    (hu : u < 2*m+caps) (hv : v < 2*m+caps)
    (h : (stripDiagram m caps).reach k u v = true) :
    stripCoordinate m u ≤ stripCoordinate m v+k ∧
      stripCoordinate m v ≤ stripCoordinate m u+k := by
  exact Diagram.reach_coordinate (stripDiagram m caps) (stripCoordinate m)
    (fun _ _ hu hv he => strip_coordinate_step m caps hm hc hu hv he) k u v hu hv h

end ZombieMain
