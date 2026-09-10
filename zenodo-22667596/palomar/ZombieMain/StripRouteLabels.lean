import ZombieMain.StripPresentation
import ZombieDamage.OpenStripMetricContract

namespace ZombieMain
open ZombieDamage ZombieDamage.OpenStrip
set_option maxHeartbeats 2000000

theorem exists_port_iff (P : Port → Prop) : (∃ p,P p) ↔
    P (false,none) ∨ P (false,some false) ∨ P (false,some true) ∨
    P (true,none) ∨ P (true,some false) ∨ P (true,some true) := by
  constructor
  · rintro ⟨⟨side,k⟩,h⟩
    cases side <;> cases k with
    | none => simp_all
    | some b => cases b <;> simp_all
  · intro h
    rcases h with h | h | h | h | h | h
    · exact ⟨(false,none),h⟩
    · exact ⟨(false,some false),h⟩
    · exact ⟨(false,some true),h⟩
    · exact ⟨(true,none),h⟩
    · exact ⟨(true,some false),h⟩
    · exact ⟨(true,some true),h⟩

theorem strip_boundary_label (m : Nat) (hm : 2≤m) (left right : Bool)
    (p a : Fin (2*m+8)) (hp : inside m left right p=true)
    (ha : inside m left right a=false) (hpa : Adj m left right p.val a.val) :
    ∃ q, Active left right q ∧ p=portVertex m hm q ∧ a=portStub m q := by
  rw [exists_port_iff]
  have hp' := of_decide_eq_true hp
  have ha' := of_decide_eq_false ha
  cases left <;> cases right <;>
    simp [Active,capOn,portVertex,portStub,cap,capStub,rail,stub,Adj] at * <;>
    simp only [Fin.ext_iff,Fin.val_zero] at * <;> omega

theorem strip_portStub_injective (m : Nat) : Function.Injective (portStub m) := by
  intro p q h
  have hp := (exists_port_iff (fun r => p=r)).mp ⟨p,rfl⟩
  have hq := (exists_port_iff (fun r => q=r)).mp ⟨q,rfl⟩
  have hv := congrArg Fin.val h
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [portStub,capStub,stub] at hv ⊢ <;> omega

theorem strip_allowed_witness (m : Nat) (left right : Bool)
    (target : Option (Fin (2*m+8))) (allowed : Port → Bool) (w : Fin (2*m+8))
    (h : (task m left right target allowed).allowedExit w=true) :
    ∃ q, Active left right q ∧ allowed q=true ∧ w=portStub m q := by
  obtain ⟨q,_,hq⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hq
  exact ⟨q,hq.1.1,hq.1.2,hq.2⟩

end ZombieMain
