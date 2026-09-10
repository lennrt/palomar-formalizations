import ZombieDamage.OpenStripTarget
import ZombieDamage.FullGameBounds

namespace ZombieDamage.OpenStrip
open FullGame

/-- A boundary incidence is a side and either its cap or one of its rails.
Inactive incidences are excluded by `Active`; they are never local targets. -/
abbrev Port := Bool × Option Bool

def flipPort (p : Port) : Port := (!p.1,p.2)
def capOn (left right side : Bool) : Bool := if side then right else left

def Active (left right : Bool) (p : Port) : Prop :=
  capOn left right p.1 = p.2.isNone

def portVertex (m : Nat) (hm : 2≤m) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => cap m p.1
  | some b => rail m b (if p.1 then m-1 else 0) (by split <;> omega)

def portStub (m : Nat) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => capStub m p.1
  | some b => stub m p.1 b

def Internal (m : Nat) (left right : Bool) (x : Fin (2*m+8)) : Prop :=
  (∃ b i, ∃ hi : i<m, x=rail m b i hi) ∨
  (left=true ∧ x=cap m false) ∨ (right=true ∧ x=cap m true)

def ExitAt (m : Nat) (hm : 2≤m) (q : Port) (phase : Phase) (s : State (Fin (2*m+8))) : Prop :=
  phase=.survivor ∧ s.zombie=portVertex m hm q ∧ s.survivor=portStub m q

def TargetExit (m : Nat) (hm : 2≤m) (left right : Bool) (entry : Port)
    (x : Fin (2*m+8)) (phase : Phase) (s : State (Fin (2*m+8))) : Prop :=
  ∃ q, Active left right q ∧ q≠entry ∧ ExitAt m hm q phase s ∧ s.damaged x

theorem flipPort_involutive (p : Port) : flipPort (flipPort p)=p := by
  rcases p with ⟨side,k⟩
  cases side <;> rfl

theorem flipPort_injective {p q : Port} (h : flipPort p=flipPort q) : p=q := by
  have hh := congrArg flipPort h
  simpa only [flipPort_involutive] using hh

theorem active_flip (left right : Bool) (p : Port) :
    Active right left (flipPort p) ↔ Active left right p := by
  rcases p with ⟨side,k⟩
  cases side <;> rfl

theorem reflect_portVertex (m : Nat) (hm : 2≤m) (p : Port) :
    reflect m hm (portVertex m hm p)=portVertex m hm (flipPort p) := by
  rcases p with ⟨side,k⟩
  cases side <;> cases k with
  | none => exact reflect_cap m hm _
  | some b =>
    simp only [portVertex,flipPort,reflect_rail,Bool.false_eq_true,↓reduceIte,Nat.sub_zero,Nat.sub_self]
    rfl

theorem reflect_portStub (m : Nat) (hm : 2≤m) (p : Port) :
    reflect m hm (portStub m p)=portStub m (flipPort p) := by
  rcases p with ⟨side,k⟩
  cases k with
  | none => exact reflect_capStub m hm side
  | some b => exact reflect_stub m hm side b

theorem internal_reflect (m : Nat) (hm : 2≤m) (left right : Bool)
    {x : Fin (2*m+8)} (h : Internal m left right x) :
    Internal m right left (reflect m hm x) := by
  rcases h with ⟨b,i,hi,hx⟩ | ⟨hl,hx⟩ | ⟨hr,hx⟩
  · exact Or.inl ⟨b,m-1-i,by omega,hx ▸ reflect_rail m hm b i hi⟩
  · exact Or.inr (Or.inr ⟨hl,hx ▸ reflect_cap m hm false⟩)
  · exact Or.inr (Or.inl ⟨hr,hx ▸ reflect_cap m hm true⟩)

end ZombieDamage.OpenStrip
