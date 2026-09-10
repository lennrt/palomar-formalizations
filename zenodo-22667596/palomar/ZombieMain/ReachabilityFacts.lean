import ZombieMain.Diagram

namespace ZombieMain.Diagram

theorem reach_self (D : Diagram) (k u : Nat) : D.reach k u u = true := by
  cases k <;> simp [reach]

theorem reach_step (D : Diagram) {k u v w : Nat} (hv : v < D.order)
    (huv : D.adj u v = true) (hvw : D.reach k v w = true) :
    D.reach (k+1) u w = true := by
  simp only [reach, Bool.or_eq_true]
  right
  exact List.any_eq_true.mpr ⟨v, List.mem_range.mpr hv, by simp [huv,hvw]⟩

theorem reach_adj (D : Diagram) (k : Nat) {u v : Nat} (hv : v < D.order)
    (h : D.adj u v = true) : D.reach (k+1) u v = true :=
  reach_step D hv h (reach_self D k v)

theorem reach_two (D : Diagram) (k : Nat) {u v w : Nat}
    (hv : v < D.order) (hw : w < D.order)
    (huv : D.adj u v = true) (hvw : D.adj v w = true) :
    D.reach (k+2) u w = true :=
  reach_step D hv huv (reach_adj D k hw hvw)

theorem reach_three (D : Diagram) {u v w x : Nat}
    (hv : v < D.order) (hw : w < D.order) (hx : x < D.order)
    (huv : D.adj u v = true) (hvw : D.adj v w = true) (hwx : D.adj w x = true) :
    D.reach 3 u x = true :=
  reach_step D hv huv (reach_two D 0 hw hx hvw hwx)

end ZombieMain.Diagram
