import ZombieDamage.OpenStripTask
import ZombieDamage.Ambient

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (hm : 2≤m) (left right : Bool)

/-- Prescribed exits in the exact local predicate used by the ambient
transfer theorem. The graph, boundary and initial state are explicit. -/
theorem metric_exit_contract (entry q : Port) (hin : Active left right entry)
    (hq : Active left right q) (hne : q≠entry) :
    (task m left right none (fun p => decide (p=q))).MetricForcesWithin
      (task_good m hm left right none (fun p => decide (p=q))) (2*m)
      ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  let T := task m left right none (fun p => decide (p=q))
  let hg := task_good m hm left right none (fun p => decide (p=q))
  let F := taskIso m hm left right none (fun p => decide (p=q))
  let pos : Position (2*m+8) := ⟨false,portStub m entry,portVertex m hm entry⟩
  let s := Task.fullState pos (fun _ => False)
  apply T.fullGame_metricForcesWithin hg
    (task_boundary_leaves m hm left right none (fun p => decide (p=q)))
    (2*m) pos (fun _ => False) (active_port_inside m hm left right entry hin)
    (decide_eq_true (active_port_adj m hm left right entry hin))
    (by intro v hv hd; contradiction)
  have h := exit_contract m hm left right entry q hin hq hne s rfl rfl
  have hmap := F.forcesWithin h (Q := T.FullExit) (by
    intro phase t ht
    refine ⟨ht.1,?_,?_,?_⟩
    · change inside m left right t.survivor=false
      rw [ht.2.2]
      exact portStub_outside m left right q
    · change T.allowedExit t.survivor=true
      rw [ht.2.2]
      exact task_allowed m left right none (fun p => decide (p=q)) q hq (by simp)
    · intro v hv
      cases hv)
  exact hmap

/-- Target routing in the exact local metric predicate, for every active
entry and internal target at arbitrary length. This supplies the premise of
`ShortComponentModel.metricForcesWithin_ambient` without assuming a strategy. -/
theorem metric_target_contract (entry : Port) (hin : Active left right entry)
    (x : Fin (2*m+8)) (hx : Internal m left right x) :
    (task m left right (some x) (fun p => decide (p≠entry))).MetricForcesWithin
      (task_good m hm left right (some x) (fun p => decide (p≠entry))) (2*m)
      ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  let T := task m left right (some x) (fun p => decide (p≠entry))
  let hg := task_good m hm left right (some x) (fun p => decide (p≠entry))
  let F := taskIso m hm left right (some x) (fun p => decide (p≠entry))
  let pos : Position (2*m+8) := ⟨false,portStub m entry,portVertex m hm entry⟩
  let s := Task.fullState pos (fun _ => False)
  apply T.fullGame_metricForcesWithin hg
    (task_boundary_leaves m hm left right (some x) (fun p => decide (p≠entry)))
    (2*m) pos (fun _ => False) (active_port_inside m hm left right entry hin)
    (decide_eq_true (active_port_adj m hm left right entry hin))
    (by intro v hv hd; contradiction)
  have h := target_contract m hm left right entry hin x hx s rfl rfl
  have hmap := F.forcesWithin h (Q := T.FullExit) (by
    intro phase t ht
    obtain ⟨q,hq,hneq,hex,hd⟩ := ht
    refine ⟨hex.1,?_,?_,?_⟩
    · change inside m left right t.survivor=false
      rw [hex.2.2]
      exact portStub_outside m left right q
    · change T.allowedExit t.survivor=true
      rw [hex.2.2]
      exact task_allowed m left right (some x) (fun p => decide (p≠entry)) q hq
        (decide_eq_true hneq)
    · intro v hv
      change some x=some v at hv
      change t.damaged v
      exact Option.some.inj hv ▸ hd)
  exact hmap

end ZombieDamage.OpenStrip
