import ZombieDamage.OpenStripRouting
import ZombieDamage.LeafSteps

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat)

theorem left_stub_neighbor (hm : 2≤m) (right b : Bool) (x : Fin (2*m+8))
    (h : (graph m false right hm).adj (stub m false b) x) :
    x=rail m b 0 (by omega) := by
  apply Fin.ext
  change Adj m false right _ _ at h
  cases b <;> simp [stub,rail,Adj] at * <;> omega

theorem left_stub_clean (hm : 2≤m) (right b : Bool) :
    (graph m false right hm).Clean (stub m false b) (rail m b 0 (by omega)) := by
  apply (graph m false right hm).leaf_clean
  · change Adj m false right _ _
    cases b <;> simp [stub,rail,Adj] <;> omega
  · exact left_stub_neighbor m hm right b

theorem left_capStub_neighbor (hm : 2≤m) (right : Bool) (x : Fin (2*m+8))
    (h : (graph m true right hm).adj (capStub m false) x) : x=cap m false := by
  apply Fin.ext
  change Adj m true right _ _ at h
  simp [capStub,cap,Adj] at *
  omega

theorem left_capStub_clean (hm : 2≤m) (right : Bool) :
    (graph m true right hm).Clean (capStub m false) (cap m false) := by
  apply (graph m true right hm).leaf_clean
  · change Adj m true right _ _
    simp [capStub,cap,Adj]
  · exact left_capStub_neighbor m hm right

/-- From the left cap, the next rail step has exactly one geodesic reply. -/
theorem cap_rail_step (hm : 2≤m) (right b : Bool) :
    (graph m true right hm).TwoApart (cap m false) (rail m b 1 (by omega)) ∧
    ∀ x, (graph m true right hm).GeodesicReply (cap m false)
      (rail m b 1 (by omega)) x → x=rail m b 0 (by omega) := by
  have ht : (graph m true right hm).TwoApart (cap m false) (rail m b 1 (by omega)) := by
    refine ⟨?_,?_,rail m b 0 (by omega),?_,?_⟩
    · intro he
      have hv := congrArg Fin.val he
      cases b <;> simp [cap,rail] at hv <;> omega
    · change ¬ Adj m true right _ _
      cases b <;> simp [cap,rail,Adj] <;> omega
    · change Adj m true right _ _
      cases b <;> simp [cap,rail,Adj] <;> omega
    · change Adj m true right _ _
      cases b <;> simp [rail,Adj] <;> omega
  refine ⟨ht,?_⟩
  intro x hx
  obtain ⟨h1,h2⟩ := ((graph m true right hm).geodesicReply_iff_commonNeighbor ht).1 hx
  apply Fin.ext
  change Adj m true right _ _ at h1 h2
  cases right <;> cases b <;> simp only [cap,rail, Bool.false_eq_true, ↓reduceIte] at * <;> unfold Adj at * <;> omega

end ZombieDamage.OpenStrip
