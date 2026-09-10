import ZombieDamage.OpenStripTargetContract
import ZombieDamage.FullGameConverse

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (hm : 2≤m) (left right : Bool)

def inside (v : Fin (2*m+8)) : Bool :=
  decide (v.val<2*m ∨ (left=true ∧ v.val=2*m) ∨ (right=true ∧ v.val=2*m+1))

theorem inside_internal (v : Fin (2*m+8)) : inside m left right v=true ↔ Internal m left right v := by
  simp only [inside,decide_eq_true_eq]
  constructor
  · intro h
    rcases h with h | ⟨hl,h⟩ | ⟨hr,h⟩
    · by_cases hv : v.val<m
      · exact Or.inl ⟨false,v.val,hv,Fin.ext rfl⟩
      · refine Or.inl ⟨true,v.val-m,by omega,?_⟩
        apply Fin.ext
        change v.val=m+(v.val-m)
        omega
    · exact Or.inr (Or.inl ⟨hl,Fin.ext h⟩)
    · exact Or.inr (Or.inr ⟨hr,Fin.ext h⟩)
  · intro h
    rcases h with ⟨b,i,hi,h⟩ | ⟨hl,h⟩ | ⟨hr,h⟩
    · left
      rw [h]
      cases b <;> simp [rail] <;> omega
    · exact Or.inr (Or.inl ⟨hl,congrArg Fin.val h⟩)
    · exact Or.inr (Or.inr ⟨hr,congrArg Fin.val h⟩)

def allPorts : List Port := [(false,none),(false,some false),(false,some true),
  (true,none),(true,some false),(true,some true)]

theorem mem_allPorts (p : Port) : p∈allPorts := by
  rcases p with ⟨side,k⟩
  cases side <;> cases k with
  | none => decide
  | some b => cases b <;> decide

instance (p : Port) : Decidable (Active left right p) := by unfold Active; infer_instance

def task (target : Option (Fin (2*m+8))) (allowed : Port → Bool) : Task (2*m+8) where
  adj u v := decide (Adj m left right u.val v.val)
  inside := inside m left right
  target := target
  allowedExit v := allPorts.any (fun p => decide (Active left right p) && allowed p && decide (v=portStub m p))

include hm in
theorem task_good (target : Option (Fin (2*m+8))) (allowed : Port → Bool) :
    (task m left right target allowed).GoodGraph := by
  constructor
  · intro u v
    change decide (Adj m left right u.val v.val)=decide (Adj m left right v.val u.val)
    have he : Adj m left right u.val v.val ↔ Adj m left right v.val u.val :=
      ⟨(graph m left right hm).symm,(graph m left right hm).symm⟩
    simp only [he]
  · intro u
    change decide (Adj m left right u.val u.val)=false
    exact decide_eq_false ((graph m left right hm).loopless u)

def taskIso (target : Option (Fin (2*m+8))) (allowed : Port → Bool) :
    GraphIso (graph m left right hm)
      ((task m left right target allowed).graph (task_good m hm left right target allowed)) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  adjacency := by
    intro u v
    change Adj m left right u.val v.val ↔ decide (Adj m left right u.val v.val)=true
    simp only [decide_eq_true_eq]

include hm in
theorem task_boundary_leaves (target : Option (Fin (2*m+8))) (allowed : Port → Bool) :
    (task m left right target allowed).BoundaryLeaves := by
  intro v hv u w hu hw
  change decide (v.val<2*m ∨ (left=true ∧ v.val=2*m) ∨ (right=true ∧ v.val=2*m+1))=false at hv
  change decide (Adj m left right v.val u.val)=true at hu
  change decide (Adj m left right v.val w.val)=true at hw
  have hv' := of_decide_eq_false hv
  have hu' := of_decide_eq_true hu
  have hw' := of_decide_eq_true hw
  apply Fin.ext
  cases left <;> cases right <;>
    simp only [Adj, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and, or_false, false_or] at hu' hw' hv' <;> omega

theorem portStub_outside (p : Port) : inside m left right (portStub m p)=false := by
  rcases p with ⟨side,k⟩
  cases side <;> cases k with
  | none => simp [inside,portStub,capStub] <;> omega
  | some b => cases b <;> simp [inside,portStub,stub] <;> omega

theorem active_port_inside (p : Port) (hp : Active left right p) :
    inside m left right (portVertex m hm p)=true := by
  apply (inside_internal m left right _).2
  rcases p with ⟨side,k⟩
  cases k with
  | none =>
    cases side with
    | false => exact Or.inr (Or.inl ⟨hp,rfl⟩)
    | true => exact Or.inr (Or.inr ⟨hp,rfl⟩)
  | some b => exact Or.inl ⟨b,if side then m-1 else 0,by split <;> omega,rfl⟩

theorem active_port_adj (p : Port) (hp : Active left right p) :
    (graph m left right hm).adj (portStub m p) (portVertex m hm p) := by
  rcases p with ⟨side,k⟩
  cases side <;> cases k with
  | none =>
    change Adj m left right _ _
    simp [Active,capOn] at hp
    simp [portStub,portVertex,capStub,cap,Adj,hp] <;> omega
  | some b =>
    change Adj m left right _ _
    simp [Active,capOn] at hp
    cases b <;> simp [portStub,portVertex,stub,rail,Adj,hp] <;> omega

theorem task_allowed (target : Option (Fin (2*m+8))) (allowed : Port → Bool)
    (p : Port) (hp : Active left right p) (ha : allowed p=true) :
    (task m left right target allowed).allowedExit (portStub m p)=true := by
  apply List.any_eq_true.mpr
  exact ⟨p,mem_allPorts p,by simp [hp,ha]⟩

end ZombieDamage.OpenStrip
