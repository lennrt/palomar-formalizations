import ZombieDamage.OpenStrip
import ZombieDamage.Isomorphism

namespace ZombieDamage.OpenStrip
variable (m : Nat)

def reflectVal (v : Nat) : Nat :=
  if v<m then m-1-v else if v<2*m then 3*m-1-v else
  if v=2*m then 2*m+1 else if v=2*m+1 then 2*m else
  if v<2*m+4 then v+2 else if v<2*m+6 then v-2 else
  if v=2*m+6 then 2*m+7 else 2*m+6

theorem reflectVal_bound (hm : 2≤m) (v : Nat) (hv : v<2*m+8) :
    reflectVal m v < 2*m+8 := by
  unfold reflectVal
  repeat' first | split | omega

def reflect (hm : 2≤m) (v : Fin (2*m+8)) : Fin (2*m+8) :=
  ⟨reflectVal m v.val,reflectVal_bound m hm v.val v.isLt⟩

theorem reflectVal_involutive (hm : 2≤m) (v : Nat) (hv : v<2*m+8) :
    reflectVal m (reflectVal m v)=v := by
  generalize hw : reflectVal m v = w
  unfold reflectVal at hw ⊢
  repeat' first | split at hw | split | omega

theorem reflect_involutive (hm : 2≤m) (v : Fin (2*m+8)) :
    reflect m hm (reflect m hm v)=v :=
  Fin.ext (reflectVal_involutive m hm v.val v.isLt)

theorem reflect_rail (hm : 2≤m) (b : Bool) (i : Nat) (hi : i<m) :
    reflect m hm (rail m b i hi)=rail m b (m-1-i) (by omega) := by
  apply Fin.ext
  cases b <;> simp [reflect,reflectVal,rail] <;> (repeat' first | split | omega)

theorem reflect_cap (hm : 2≤m) (side : Bool) :
    reflect m hm (cap m side)=cap m (!side) := by
  apply Fin.ext
  cases side <;> simp [reflect,reflectVal,cap] <;> (repeat' first | split | omega)

theorem reflect_stub (hm : 2≤m) (side b : Bool) :
    reflect m hm (stub m side b)=stub m (!side) b := by
  apply Fin.ext
  cases side <;> cases b <;> simp [reflect,reflectVal,stub] <;> (repeat' first | split | omega)

theorem reflect_capStub (hm : 2≤m) (side : Bool) :
    reflect m hm (capStub m side)=capStub m (!side) := by
  apply Fin.ext
  cases side <;> simp [reflect,reflectVal,capStub] <;> (repeat' first | split | omega)

theorem reflect_low (u : Nat) (hu : u<m) : reflectVal m u=m-1-u := by
  simp [reflectVal,hu]

theorem reflect_high (u : Nat) (hu : m≤u) (hv : u<2*m) : reflectVal m u=3*m-1-u := by
  simp [reflectVal,show ¬u<m by omega,hv]

set_option maxHeartbeats 2000000 in
theorem reflect_adj_nat (hm : 2≤m) (left right : Bool) (u v : Nat)
    (h : Adj m left right u v) :
    Adj m right left (reflectVal m u) (reflectVal m v) := by
  unfold Adj at h ⊢
  rcases h with h | h | h | h | h | h | h | h
  · left
    rw [reflect_low m u h.1,reflect_low m v h.2.1]
    omega
  · right; left
    rw [reflect_high m u h.1 h.2.1,reflect_high m v h.2.2.1 h.2.2.2.1]
    omega
  · right; right; left
    have hv : m≤v ∧ v<2*m := by omega
    rw [reflect_low m u h.1,reflect_high m v hv.1 hv.2]
    omega
  · right; right; right; left
    have hu : m≤u ∧ u<2*m := by omega
    rw [reflect_high m u hu.1 hu.2,reflect_low m v h.1]
    omega
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    refine ⟨h.1,?_⟩
    rcases h.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · left
      rcases hv with hv | hv | hv
      all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split
    · right
      rcases hu with hu | hu | hu
      all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    refine ⟨h.1,?_⟩
    rcases h.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · left
      rcases hv with hv | hv | hv
      all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split
    · right
      rcases hu with hu | hu | hu
      all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
    refine ⟨h.1,?_⟩
    rcases h.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩ | ⟨hu,hv⟩ | ⟨hv,hu⟩
    all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split
  · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
    refine ⟨h.1,?_⟩
    rcases h.2 with ⟨hu,hv⟩ | ⟨hv,hu⟩ | ⟨hu,hv⟩ | ⟨hv,hu⟩
    all_goals rw [hu,hv]; unfold reflectVal; repeat' first | omega | split

theorem reflect_adj (hm : 2≤m) (left right : Bool) (u v : Fin (2*m+8))
    (h : (graph m left right hm).adj u v) :
    (graph m right left hm).adj (reflect m hm u) (reflect m hm v) :=
  reflect_adj_nat m hm left right u.val v.val h

def reflection (hm : 2≤m) (left right : Bool) :
    GraphIso (graph m left right hm) (graph m right left hm) where
  toFun := reflect m hm
  invFun := reflect m hm
  left_inv := reflect_involutive m hm
  right_inv := reflect_involutive m hm
  adjacency := by
    intro u v
    constructor
    · exact reflect_adj m hm left right u v
    · intro h
      have hr := reflect_adj m hm right left (reflect m hm u) (reflect m hm v) h
      simpa only [reflect_involutive] using hr

end ZombieDamage.OpenStrip
