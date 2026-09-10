import ZombieDamage.Traps
import ZombieDamage.FiniteMetric

namespace ZombieDamage.Exceptions
open FullGame
inductive Kind where
  | k4 | k33 | prism3 | cube
  deriving DecidableEq, Repr
abbrev order : Kind → Nat
  | .k4 => 4 | .k33 => 6 | .prism3 => 6 | .cube => 8
abbrev Vertex (g : Kind) := Fin (order g)

def edge (g : Kind) (u v : Vertex g) : Bool :=
  match g with
  | .k4 => u != v
  | .k33 => (u.val<3 && v.val≥3) || (v.val<3 && u.val≥3)
  | .prism3 => u != v && (u.val/3 == v.val/3 || u.val%3 == v.val%3)
  | .cube => decide ((u.val ^^^ v.val) ∈ [1,2,4])

def graph (g : Kind) : Graph (Vertex g) where
  adj u v := edge g u v = true
  symm := by cases g <;> decide
  loopless := by cases g <;> decide

instance (g : Kind) (u v : Vertex g) : Decidable ((graph g).adj u v) := by
  change Decidable (edge g u v = true)
  infer_instance

def distance (g : Kind) (u v : Vertex g) : Nat :=
  if u=v then 0 else if edge g u v then 1 else
    match g with
    | .cube => if (u.val ^^^ v.val)=7 then 3 else 2
    | _ => 2

def metric (g : Kind) : (graph g).MetricCertificate where
  value := distance g
  zero_self := by cases g <;> decide
  zero_eq := by cases g <;> decide
  edge_bound := by cases g <;> decide
  descent := by cases g <;> decide

structure TrapData (g : Kind) where
  allowed : Vertex g → Bool
  pre : Vertex g → Vertex g → Bool
  post : Vertex g → Vertex g → Bool

def TrapData.Valid {g : Kind} (D : TrapData g) : Prop :=
  (∃ v, D.allowed v = false) ∧
  (∀ z s, D.pre z s = true → z ≠ s →
    ∃ x, edge g z x = true ∧ distance g z s = distance g x s + 1 ∧
      (x=s ∨ D.post x s = true)) ∧
  (∀ z s, D.post z s = true → D.allowed s = true) ∧
  (∀ z s, D.post z s = true → ∀ w, w ≠ z →
    (w=s ∨ edge g s w = true) → D.pre z w = true)

instance {g : Kind} (D : TrapData g) : Decidable D.Valid := by
  unfold TrapData.Valid
  infer_instance

def TrapData.toTrap {g : Kind} (D : TrapData g) (h : D.Valid) :
    PositionalTrap (graph g) where
  allowed v := D.allowed v = true
  pre z s := D.pre z s = true
  post z s := D.post z s = true
  missing := by
    obtain ⟨v,hv⟩ := h.1
    exact ⟨v,by rw [hv]; decide⟩
  zombie_move := by
    intro z s hp hne
    obtain ⟨x,hx,hd,hn⟩ := h.2.1 z s hp hne
    exact ⟨x,((metric g).geodesicReply_iff z s x).2 ⟨hx,hd⟩,hn⟩
  survivor_source := h.2.2.1
  survivor_move := h.2.2.2

def bit (mask i : Nat) : Bool := ((mask >>> i) &&& 1) == 1

end ZombieDamage.Exceptions
