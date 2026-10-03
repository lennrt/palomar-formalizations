module

public import ShellObservability.GridRecovery

@[expose] public section

/-! Hybrid grid reports: complete bags at the four corners and only total
 distance at all other sensors. The redundant moment component at corners is
 determined by their full bag, so it adds no information. -/
namespace ShellObservability
open ShellTomography

def HasIntervalMomentDetector (N : ℕ) (p q r s : ℕ × ℕ) : Prop :=
  ∃ a b k : ℕ, 0 < k ∧ a+k+1 ≤ N ∧ b+k+1 ≤ N ∧
    ∀ x y, ¬ ((a < x ∧ x ≤ a+k) ↔ (b < y ∧ y ≤ b+k)) →
      (distancePair (x,y) p q).sum ≠ (distancePair (x,y) r s).sum

/-- Convert the canonical parallelogram into a balanced interval detector. -/
theorem canonical_hasIntervalMomentDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (a b u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hp : ({p,q} : Multiset (ℕ × ℕ)) = {(a,b+v),(a+u+v,b+u)})
    (hr : ({r,s} : Multiset (ℕ × ℕ)) = {(a+v,b),(a+u,b+u+v)}) :
    HasIntervalMomentDetector N p q r s := by
  have hpx : a+u+v ≤ N := by
    have hm : (a+u+v,b+u) ∈ ({p,q} : Multiset (ℕ × ℕ)) := by rw [hp]; simp
    have hh := hbound (a+u+v,b+u) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.1
  have hry : b+u+v ≤ N := by
    have hm : (a+u,b+u+v) ∈ ({r,s} : Multiset (ℕ × ℕ)) := by rw [hr]; simp
    have hh := hbound (a+u,b+u+v) (by simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm ⊢; tauto)
    exact hh.2
  refine ⟨a,b,u+v-1,by omega,by omega,by omega,?_⟩
  intro x y hxor
  have hd := parallelogram_moment_detected a b u v x y hu hv (by omega)
  rw [distancePair_of_pair_eq (x,y) _ _ _ _ hp,
    distancePair_of_pair_eq (x,y) _ _ _ _ hr]
  exact hd

end ShellObservability

namespace ShellObservability

/-- Relabelling the two points in the first population changes no detector. -/
theorem hasIntervalMomentDetector_swap_left (N : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalMomentDetector N q p r s) : HasIntervalMomentDetector N p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  rw [distancePair_comm (x,y) p q]
  exact hd x y hxy

/-- Interchanging the two populations changes no detector. -/
theorem hasIntervalMomentDetector_swap_populations (N : ℕ) (p q r s : ℕ × ℕ)
    (h : HasIntervalMomentDetector N r s p q) : HasIntervalMomentDetector N p q r s := by
  rcases h with ⟨a,b,k,hk,ha,hb,hd⟩
  refine ⟨a,b,k,hk,ha,hb,?_⟩
  intro x y hxy
  exact Ne.symm (hd x y hxy)

/-- The leftmost-point version of the interval reduction. -/
theorem leftmost_corner_collision_hasIntervalMomentDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (hpq : p.1 ≤ q.1) (hpr : p.1 ≤ r.1) (hps : p.1 ≤ s.1)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,N) p q = distancePair (0,N) r s) :
    HasIntervalMomentDetector N p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  obtain ⟨a,b,u,v,hu,hv,hpq',hrs'⟩ := leftmost_corner_collision_canonical N p q r s
    hp.2 hq.2 hr.2 hs.2 hpq hpr hps hne hzero htop
  exact canonical_hasIntervalMomentDetector N p q r s hbound a b u v hu hv hpq' hrs'

/-- Every distinct two-target population pair with equal reports at two
adjacent corners admits a nonempty equal-length interior interval detector.
In particular, this applies whenever all four corner reports agree. -/
theorem corner_collision_hasIntervalMomentDetector
    (N : ℕ) (p q r s : ℕ × ℕ)
    (hbound : ∀ z ∈ ({p,q,r,s} : Multiset (ℕ × ℕ)), z.1 ≤ N ∧ z.2 ≤ N)
    (hne : ({p,q} : Multiset (ℕ × ℕ)) ≠ {r,s})
    (hzero : distancePair (0,0) p q = distancePair (0,0) r s)
    (htop : distancePair (0,N) p q = distancePair (0,N) r s) :
    HasIntervalMomentDetector N p q r s := by
  have hp := hbound p (by simp)
  have hq := hbound q (by simp)
  have hr := hbound r (by simp)
  have hs := hbound s (by simp)
  have hmin : (p.1 ≤ q.1 ∧ p.1 ≤ r.1 ∧ p.1 ≤ s.1) ∨
      (q.1 ≤ p.1 ∧ q.1 ≤ r.1 ∧ q.1 ≤ s.1) ∨
      (r.1 ≤ p.1 ∧ r.1 ≤ q.1 ∧ r.1 ≤ s.1) ∨
      (s.1 ≤ p.1 ∧ s.1 ≤ q.1 ∧ s.1 ≤ r.1) := by omega
  rcases hmin with hpmin | hqmin | hrmin | hsmin
  · exact leftmost_corner_collision_hasIntervalMomentDetector N p q r s hbound
      hpmin.1 hpmin.2.1 hpmin.2.2 hne hzero htop
  · apply hasIntervalMomentDetector_swap_left
    apply leftmost_corner_collision_hasIntervalMomentDetector N q p r s
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hqmin.1
    · exact hqmin.2.1
    · exact hqmin.2.2
    · simpa only [Multiset.pair_comm] using hne
    · simpa only [distancePair_comm] using hzero
    · simpa only [distancePair_comm] using htop
  · apply hasIntervalMomentDetector_swap_populations
    apply leftmost_corner_collision_hasIntervalMomentDetector N r s p q
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hrmin.2.2
    · exact hrmin.1
    · exact hrmin.2.1
    · exact Ne.symm hne
    · exact hzero.symm
    · exact htop.symm
  · apply hasIntervalMomentDetector_swap_populations
    apply hasIntervalMomentDetector_swap_left
    apply leftmost_corner_collision_hasIntervalMomentDetector N s r p q
    · intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl <;> assumption
    · exact hsmin.2.2
    · exact hsmin.1
    · exact hsmin.2.1
    · simpa only [Multiset.pair_comm] using Ne.symm hne
    · simpa only [distancePair_comm] using hzero.symm
    · simpa only [distancePair_comm] using htop.symm

end ShellObservability

namespace ShellObservability
open ShellTomography

/-- A sensor in `full` retains its multiset. Every sensor retains its first
moment, the total of all reported distances counted with multiplicity. -/
noncomputable def mixedMomentReport {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x : Configuration V) (s : S) :
    Multiset ℕ × ℕ := by
  classical
  exact (if full s then bag δ x s else 0, (bag δ x s).sum)

theorem mixedMomentReport_bag_eq {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x y : Configuration V) (s : S)
    (hs : full s) (h : mixedMomentReport δ full x s = mixedMomentReport δ full y s) :
    bag δ x s = bag δ y s := by
  have he := congrArg Prod.fst h
  simpa [mixedMomentReport,hs] using he

theorem mixedMomentReport_sum_eq {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x y : Configuration V) (s : S)
    (h : mixedMomentReport δ full x s = mixedMomentReport δ full y s) :
    (bag δ x s).sum = (bag δ y s).sum := congrArg Prod.snd h

theorem mixedMomentReport_of_bag_eq {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x y : Configuration V) (s : S)
    (h : bag δ x s = bag δ y s) :
    mixedMomentReport δ full x s = mixedMomentReport δ full y s := by
  simp only [mixedMomentReport,h]

theorem mixedMomentReport_add {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x y : Configuration V) (s : S) :
    mixedMomentReport δ full (fun v => x v + y v) s =
      mixedMomentReport δ full x s + mixedMomentReport δ full y s := by
  classical
  have hb : bag δ (fun v => x v + y v) s = bag δ x s + bag δ y s := by
    simp only [bag, Multiset.replicate_add, Finset.sum_add_distrib]
  apply Prod.ext <;> simp [mixedMomentReport, hb]
  split_ifs <;> simp

/-- Common padding preserves hybrid reports. One surviving full sensor gives
 equality of masses, so exact-mass recovery implies recovery of smaller masses. -/
theorem mixedMomentReport_upTo_of_exact {V S : Type*} [Fintype V] [Nonempty V]
    (δ : S → V → ℕ) (full : S → Prop) (h e : ℕ)
    (hsurvive : ∀ erased : Finset S, erased.card ≤ e → ∃ s, s ∉ erased ∧ full s)
    (hexact : ToleratesErasures (mixedMomentReport δ full) (fun x => mass x = h) e) :
    ToleratesErasures (mixedMomentReport δ full) (fun x => mass x ≤ h) e := by
  classical
  intro erased herased x y hx hy hagree
  obtain ⟨s,hs,hfull⟩ := hsurvive erased herased
  have hbag := mixedMomentReport_bag_eq δ full x y s hfull (hagree s hs)
  have hmass : mass x = mass y := by
    have he := congrArg Multiset.card hbag
    simpa [bag,mass] using he
  let v₀ : V := Classical.choice (inferInstance : Nonempty V)
  let pad : Configuration V := fun v => if v = v₀ then h - mass x else 0
  have hmx : mass (fun v => x v + pad v) = h := by
    simp only [mass,Finset.sum_add_distrib]
    change mass x + (∑ v, pad v) = h
    simp only [pad,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    omega
  have hmy : mass (fun v => y v + pad v) = h := by
    simp only [mass,Finset.sum_add_distrib]
    change mass y + (∑ v, pad v) = h
    simp only [pad,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    omega
  have heq := hexact erased herased _ _ hmx hmy (by
    intro s hs
    rw [mixedMomentReport_add,mixedMomentReport_add,hagree s hs])
  funext v
  have he := congrFun heq v
  exact Nat.add_right_cancel he

/-- The full-bag labels are exactly the four grid corners. -/
def gridFullReport (m : ℕ) (p : ℕ × ℕ) : Prop :=
  p ∈ ({(0,0),(0,m+1),(m+1,0),(m+1,m+1)} : Finset (ℕ × ℕ))

noncomputable def gridMomentReport (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) : Configuration (Grid (m+2)) → S → Multiset ℕ × ℕ :=
  mixedMomentReport (gridSensorDistance m S hb) (fun s => gridFullReport m s.val)

def GridMomentRobust (m : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S) : Prop :=
  ToleratesErasures (gridMomentReport m S hb) (fun x => mass x ≤ 2) 1

/-- Necessity follows because every hybrid report is a function of its full bag.
 This implication does not require the corners to be selected. -/
theorem gridMomentRobust_implies_intervalCuts (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (h : GridMomentRobust m S hb) : GridIntervalCuts m S := by
  apply gridRobust_implies_intervalCuts m S hb
  intro erased he x y hx hy hagree
  apply h erased he x y hx hy
  intro s hs
  exact mixedMomentReport_of_bag_eq _ _ x y s (hagree s hs)

end ShellObservability

namespace ShellObservability
open ShellTomography

private theorem moment_one_erasure_leaves_one_of_two {A : Type*} [DecidableEq A]
    (erased : Finset A) (he : erased.card ≤ 1) (a b : A) (hne : a ≠ b) :
    a ∉ erased ∨ b ∉ erased := by
  by_cases ha : a ∈ erased
  · right
    intro hb
    exact hne ((Finset.card_le_one.mp he) a ha b hb)
  · exact Or.inl ha

/-- With all four corners present, the balanced interval cuts suffice for
single-erasure recovery of every mass-at-most-two configuration. -/
theorem gridIntervalCuts_implies_momentRobust (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S)
    (hcuts : GridIntervalCuts m S) : GridMomentRobust m S hb := by
  classical
  let s00 : S := ⟨(0,0),hcorners (by simp)⟩
  let s0N : S := ⟨(0,m+1),hcorners (by simp)⟩
  let sN0 : S := ⟨(m+1,0),hcorners (by simp)⟩
  let sNN : S := ⟨(m+1,m+1),hcorners (by simp)⟩
  have hdiagNe : s00 ≠ sNN := by
    intro he
    have hv := congrArg (fun z : S => z.val.1) he
    dsimp [s00,sNN] at hv
    omega
  have hantiNe : s0N ≠ sN0 := by
    intro he
    have hv := congrArg (fun z : S => z.val.1) he
    dsimp [s0N,sN0] at hv
    omega
  have hsurvive (erased : Finset S) (he : erased.card ≤ 1) : ∃ s, s ∉ erased ∧ gridFullReport m s.val := by
    rcases moment_one_erasure_leaves_one_of_two erased he s00 sNN hdiagNe with h | h
    · exact ⟨s00,h,by simp [gridFullReport,s00]⟩
    · exact ⟨sNN,h,by simp [gridFullReport,sNN]⟩
  have hexact : ToleratesErasures (gridMomentReport m S hb)
      (fun x => mass x = 2) 1 := by
    intro erased he x y hx hy hagree
    obtain ⟨p,q,rfl⟩ := (mass_two_iff_pairConfig x).mp hx
    obtain ⟨r,t,rfl⟩ := (mass_two_iff_pairConfig y).mp hy
    by_contra hne
    have hpairne : ({p,q} : Multiset (Grid (m+2))) ≠ {r,t} := by
      simpa only [ne_eq, pairConfig_eq_iff_pair_eq] using hne
    have hnatne : ({gridCoordinates p,gridCoordinates q} : Multiset (ℕ × ℕ)) ≠
        {gridCoordinates r,gridCoordinates t} := by
      intro hh
      apply hpairne
      apply Multiset.map_injective (gridCoordinates_injective (m+2))
      simpa only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] using hh
    have hbound : ∀ z ∈ ({gridCoordinates p,gridCoordinates q,gridCoordinates r,
        gridCoordinates t} : Multiset (ℕ × ℕ)), z.1 ≤ m+1 ∧ z.2 ≤ m+1 := by
      intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      all_goals dsimp [gridCoordinates]; constructor
      all_goals omega
    have hreport (sensor : S) (hs : sensor ∉ erased) (hf : gridFullReport m sensor.val) :
        distancePair sensor.val (gridCoordinates p) (gridCoordinates q) =
          distancePair sensor.val (gridCoordinates r) (gridCoordinates t) := by
      simpa only [grid_pair_report] using mixedMomentReport_bag_eq
        (gridSensorDistance m S hb) (fun z => gridFullReport m z.val)
        (pairConfig p q) (pairConfig r t) sensor hf (hagree sensor hs)
    have hmoment (sensor : S) (hs : sensor ∉ erased) :
        (distancePair sensor.val (gridCoordinates p) (gridCoordinates q)).sum =
          (distancePair sensor.val (gridCoordinates r) (gridCoordinates t)).sum := by
      simpa only [grid_pair_report] using mixedMomentReport_sum_eq
        (gridSensorDistance m S hb) (fun z => gridFullReport m z.val)
        (pairConfig p q) (pairConfig r t) sensor (hagree sensor hs)
    have hopposite := opposite_corner_pair_equality (m+1) (gridCoordinates p)
      (gridCoordinates q) (gridCoordinates r) (gridCoordinates t) hbound
    have hzero : distancePair (0,0) (gridCoordinates p) (gridCoordinates q) =
        distancePair (0,0) (gridCoordinates r) (gridCoordinates t) := by
      rcases moment_one_erasure_leaves_one_of_two erased he s00 sNN hdiagNe with hs | hs
      · exact hreport s00 hs (by simp [gridFullReport,s00])
      · exact hopposite.1.mp (hreport sNN hs (by simp [gridFullReport,sNN]))
    have htop : distancePair (0,m+1) (gridCoordinates p) (gridCoordinates q) =
        distancePair (0,m+1) (gridCoordinates r) (gridCoordinates t) := by
      rcases moment_one_erasure_leaves_one_of_two erased he s0N sN0 hantiNe with hs | hs
      · exact hreport s0N hs (by simp [gridFullReport,s0N])
      · exact hopposite.2.mp (hreport sN0 hs (by simp [gridFullReport,sN0]))
    obtain ⟨a,b,k,hk,ha,hb',hdetect⟩ := corner_collision_hasIntervalMomentDetector (m+1)
      (gridCoordinates p) (gridCoordinates q) (gridCoordinates r) (gridCoordinates t)
      hbound hnatne hzero htop
    have htwo := hcuts a b k hk (by omega) (by omega)
    obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 <
      (S.filter (fun v => ¬ ((a < v.1 ∧ v.1 ≤ a+k) ↔
        (b < v.2 ∧ v.2 ≤ b+k)))).card)
    let sz : S := ⟨z,(Finset.mem_filter.mp hz).1⟩
    let sw : S := ⟨w,(Finset.mem_filter.mp hw).1⟩
    have hlabelNe : sz ≠ sw := fun hh => hzw (congrArg Subtype.val hh)
    rcases moment_one_erasure_leaves_one_of_two erased he sz sw hlabelNe with hz' | hw'
    · exact hdetect z.1 z.2 (Finset.mem_filter.mp hz).2 (hmoment sz hz')
    · exact hdetect w.1 w.2 (Finset.mem_filter.mp hw).2 (hmoment sw hw')
  letI : Nonempty (Grid (m+2)) := ⟨(⟨0,by omega⟩,⟨0,by omega⟩)⟩
  exact mixedMomentReport_upTo_of_exact (gridSensorDistance m S hb)
    (fun s => gridFullReport m s.val) 2 1 hsurvive hexact

/-- Exact interval characterization of single-erasure hybrid recovery for all
integer populations of mass at most two, measured in actual graph distance. -/
theorem gridMomentRobust_iff_intervalCuts (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridMomentRobust m S hb ↔ GridIntervalCuts m S :=
  ⟨gridMomentRobust_implies_intervalCuts m S hb,
    gridIntervalCuts_implies_momentRobust m S hb hcorners⟩

/-- Four-corner full-bag recovery and hybrid recovery have exactly the same
sensor placements, including for repeated targets and varying total mass. -/
theorem gridMomentRobust_iff_gridRobust (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridMomentRobust m S hb ↔ GridRobust m S hb :=
  (gridMomentRobust_iff_intervalCuts m S hb hcorners).trans
    (gridRobust_iff_intervalCuts m S hb hcorners).symm

end ShellObservability
