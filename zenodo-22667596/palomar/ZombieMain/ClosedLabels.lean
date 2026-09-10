import ZombieMain.StripPresentationGeometry
import ZombieDamage.PrismGame
import ZombieDamage.MobiusGame

namespace ZombieMain
open ZombieDamage
set_option maxHeartbeats 2000000

def prismLabels (m : Nat) : Fin (closedDiagram m false).order ≃ (Fin m × Bool) where
  toFun i := (⟨i.val/2,by have hi : i.val<2*m := i.isLt; omega⟩,decide (i.val%2=1))
  invFun u := ⟨2*u.1.val+(if u.2 then 1 else 0),by
    have hi := u.1.isLt
    change 2*u.1.val+(if u.2 then 1 else 0)<2*m
    cases u.2 <;> simp <;> omega⟩
  left_inv i := by
    apply Fin.ext
    simp only [decide_eq_true_eq]
    split_ifs <;> omega
  right_inv u := by
    rcases u with ⟨i,b⟩
    apply Prod.ext
    · apply Fin.ext
      cases b <;> simp <;> omega
    · cases b <;> simp <;> omega

def mobiusLabels (m : Nat) : Fin (closedDiagram m true).order ≃ Fin (2*m) where
  toFun i := ⟨stripLocalIndex m i.val,by
    have hi : i.val<2*m := i.isLt
    simp only [stripLocalIndex,if_pos hi]
    split_ifs <;> omega⟩
  invFun u := ⟨stripDiagramIndex m u.val,by
    have hu : u.val<2*m := u.isLt
    change stripDiagramIndex m u.val<2*m
    simp only [stripDiagramIndex,if_pos hu]
    split_ifs <;> omega⟩
  left_inv i := Fin.ext (strip_index_left_inverse m i.val)
  right_inv u := Fin.ext (strip_index_right_inverse m u.val)

theorem mod_one_wrap (n a : Nat) (ha : a<2*n) :
    a%n = if a<n then a else a-n := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]

theorem prism_labels_adj (m : Nat) (hm : 5≤m)
    (i j : Fin (closedDiagram m false).order) :
    (closedDiagram m false).adj i.val j.val=true ↔
      (PrismGame.graph hm).adj (prismLabels m i) (prismLabels m j) := by
  have hi : i.val<2*m := i.isLt
  have hj : j.val<2*m := j.isLt
  have hi' : i.val/2<m := by omega
  have hj' : j.val/2<m := by omega
  simp only [closedDiagram,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
    Bool.false_eq_true,↓reduceIte]
  rw [stripAdj_rail m 0 i.val j.val hi hj]
  simp only [PrismGame.graph,CycleGame.graph,Cyclic.shift,prismLabels,Fin.ext_iff]
  change _ ↔ ((decide (i.val%2=1)=decide (j.val%2=1) ∧
      (j.val/2=(i.val/2+1)%m ∨ i.val/2=(j.val/2+1)%m)) ∨
      (i.val/2=j.val/2 ∧ decide (i.val%2=1)≠decide (j.val%2=1)))
  rw [mod_one_wrap m (i.val/2+1) (by omega),mod_one_wrap m (j.val/2+1) (by omega)]
  have heq : (decide (i.val%2=1)=decide (j.val%2=1)) ↔ i.val%2=j.val%2 := by
    by_cases hp : i.val%2=1 <;> by_cases hq : j.val%2=1 <;> simp [hp,hq] <;> omega
  simp only [ne_eq,heq]
  unfold interleavedRailAdj
  split_ifs <;> omega

theorem mobius_labels_adj (m : Nat) (hm : 4≤m)
    (i j : Fin (closedDiagram m true).order) :
    (closedDiagram m true).adj i.val j.val=true ↔
      (MobiusGame.graph hm).adj (mobiusLabels m i) (mobiusLabels m j) := by
  have hi : i.val<2*m := i.isLt
  have hj : j.val<2*m := j.isLt
  have hui : stripLocalIndex m i.val<2*m := (mobiusLabels m i).isLt
  have hvj : stripLocalIndex m j.val<2*m := (mobiusLabels m j).isLt
  simp only [closedDiagram,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,
    ↓reduceIte]
  rw [stripAdj_rail m 0 i.val j.val hi hj]
  simp only [MobiusGame.graph,MobiusGame.adjacency,Cyclic.shift,mobiusLabels,Fin.ext_iff]
  change _ ↔ (stripLocalIndex m j.val=(stripLocalIndex m i.val+1)%(2*m) ∨
    stripLocalIndex m j.val=(stripLocalIndex m i.val+(2*m-1))%(2*m) ∨
    stripLocalIndex m j.val=(stripLocalIndex m i.val+m)%(2*m))
  rw [mod_one_wrap (2*m) (stripLocalIndex m i.val+1) (by omega),
    mod_one_wrap (2*m) (stripLocalIndex m i.val+(2*m-1)) (by omega),
    mod_one_wrap (2*m) (stripLocalIndex m i.val+m) (by omega)]
  simp only [stripLocalIndex,if_pos hi,if_pos hj]
  split_ifs <;> unfold interleavedRailAdj <;> omega

end ZombieMain
