import ZombieMain.Diagram

namespace ZombieMain

/-- Rail labels are interleaved: `2*i` and `2*i+1` form rung `i`.
The optional left and right caps have labels `2*m` and `2*m+1`. -/
def stripAdj (m caps u v : Nat) : Prop :=
  (u < 2*m ∧ v < 2*m ∧
    ((u/2 = v/2 ∧ u%2 ≠ v%2) ∨
     (u%2 = v%2 ∧ (u/2+1 = v/2 ∨ v/2+1 = u/2)))) ∨
  (1 ≤ caps ∧ ((u = 2*m ∧ (v=0 ∨ v=1)) ∨
               (v = 2*m ∧ (u=0 ∨ u=1)))) ∨
  (2 ≤ caps ∧ ((u = 2*m+1 ∧ (v=2*m-2 ∨ v=2*m-1)) ∨
               (v = 2*m+1 ∧ (u=2*m-2 ∨ u=2*m-1))))

instance (m caps u v : Nat) : Decidable (stripAdj m caps u v) := by
  unfold stripAdj
  infer_instance

def stripDiagram (m caps : Nat) : Diagram where
  order := 2*m+caps
  adj u v := decide (stripAdj m caps u v)

def closedDiagram (m : Nat) (twisted : Bool) : Diagram where
  order := 2*m
  adj u v := decide (stripAdj m 0 u v) ||
    (if twisted then
      (u == 0 && v == 2*m-1) || (v == 0 && u == 2*m-1) ||
      (u == 1 && v == 2*m-2) || (v == 1 && u == 2*m-2)
    else
      (u == 0 && v == 2*m-2) || (v == 0 && u == 2*m-2) ||
      (u == 1 && v == 2*m-1) || (v == 1 && u == 2*m-1))

def literalDiagram (n : Nat) (edges : List (Nat × Nat)) : Diagram where
  order := n
  adj u v := edges.any (fun e => (u == e.1 && v == e.2) || (u == e.2 && v == e.1))

inductive Family where
  | ladder (m : Nat)
  | singleCap (m : Nat)
  | doubleCap (m : Nat)
  | prism (m : Nat)
  | mobius (m : Nat)
  | k23 | k33e | p3e | q3v | q3e | k4 | k33
  deriving DecidableEq, Repr

def Family.diagram : Family → Diagram
  | .ladder m => stripDiagram m 0
  | .singleCap m => stripDiagram m 1
  | .doubleCap m => stripDiagram m 2
  | .prism m => closedDiagram m false
  | .mobius m => closedDiagram m true
  | .k23 => literalDiagram 5 [(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)]
  | .k33e => literalDiagram 6 [(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
  | .p3e => literalDiagram 6 [(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]
  | .q3v => literalDiagram 7 [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
  | .q3e => literalDiagram 8 [(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]
  | .k4 => literalDiagram 4 [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
  | .k33 => literalDiagram 6 [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]

def Family.Admissible : Family → Prop
  | .ladder m => 2 ≤ m
  | .singleCap m | .doubleCap m => 1 ≤ m
  | .prism m | .mobius m => 3 ≤ m
  | _ => True

instance (f : Family) : Decidable f.Admissible := by
  cases f <;> unfold Family.Admissible <;> infer_instance

/-- The finite starting rows. Parameter tails are proved separately for all
ladder lengths at least five, single caps at least four and double caps at least three. -/
def smallOpenFamilies : List Family :=
  [.ladder 2, .ladder 3, .ladder 4,
   .singleCap 1, .singleCap 2, .singleCap 3,
   .doubleCap 1, .doubleCap 2, .k23, .k33e, .p3e, .q3v, .q3e]

def Diagram.Classified (D : Diagram) : Prop :=
  D.portCount = 1 ∨ ∃ f : Family, f.Admissible ∧ Nonempty (D.Iso f.diagram)

end ZombieMain
