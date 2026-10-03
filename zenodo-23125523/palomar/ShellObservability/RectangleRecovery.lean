module

public import ShellObservability.RectangleGeometry
public import ShellObservability.Populations

@[expose] public section

/-! The actual rectangular-grid-distance erasure criterion for all occupancy configurations
of mass at most two, expressed by balanced interior interval cuts. -/

namespace ShellObservability.Rectangle

open ShellTomography

/-- Natural coordinate representation of a finite grid vertex. -/
def gridCoordinates {w h : ℕ} (v : Grid w h) : ℕ × ℕ := (v.1.val,v.2.val)

/-- Every selected sensor lies in the `(M+2) (N+2)` by `(M+2) (N+2)` grid. -/
def GridSensorBounds (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, p.1 < M+2 ∧ p.2 < N+2

/-- Convert a selected natural-coordinate sensor into an actual grid vertex. -/
def gridSensorVertex (M N : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S)
    (s : S) : Grid (M+2) (N+2) :=
  (⟨s.val.1,(hb s.val s.property).1⟩,⟨s.val.2,(hb s.val s.property).2⟩)

/-- Sensor measurements are the graph's actual shortest-path distances. -/
noncomputable def gridSensorDistance (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (s : S) (v : Grid (M+2) (N+2)) : ℕ :=
  (gridGraph (M+2) (N+2)).dist (gridSensorVertex M N S hb s) v

/-- Single-erasure recovery for every occupancy configuration of mass at most two. -/
def GridRobust (M N : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S) : Prop :=
  ToleratesErasures (bag (gridSensorDistance M N S hb)) (fun x => mass x ≤ 2) 1

/-- Every nonempty equal-length pair of interior intervals has at least two
selected sensors in its coordinate XOR. -/
def GridIntervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b k : ℕ, 0 < k → a+k ≤ M → b+k ≤ N →
    2 ≤ (S.filter (fun p => ¬ ((a < p.1 ∧ p.1 ≤ a+k) ↔
      (b < p.2 ∧ p.2 ≤ b+k)))).card

/-- The four grid corners are selected. -/
def GridHasCorners (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ({(0,0),(0,N+1),(M+1,0),(M+1,N+1)} : Finset (ℕ × ℕ)) ⊆ S

end ShellObservability.Rectangle

namespace ShellObservability.Rectangle

open ShellTomography

@[simp] theorem gridCoordinates_sensor (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (s : S) :
    gridCoordinates (gridSensorVertex M N S hb s) = s.val := rfl

theorem gridCoordinates_injective (w h : ℕ) :
    Function.Injective (gridCoordinates (w := w) (h := h)) := by
  intro p q h
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Literal pair reports for the actual graph agree with their natural-coordinate
Manhattan expressions by the imported shortest-path theorem. -/
theorem grid_pair_report (M N : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S)
    (sensor : S) (p q : Grid (M+2) (N+2)) :
    bag (gridSensorDistance M N S hb) (pairConfig p q) sensor =
      distancePair sensor.val (gridCoordinates p) (gridCoordinates q) := by
  rw [bag_pairConfig]
  simp only [gridSensorDistance, grid_dist_eq_manhattan, manhattan, gridSensorVertex,
    distancePair, gridCoordinates]

/-- Necessity needs no corner assumption: the skinny trades enforce every
balanced interval cut on an arbitrary sensor set. -/
theorem gridRobust_implies_intervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hrobust : GridRobust M N S hb) : GridIntervalCuts M N S := by
  classical
  intro a b k hk ha hb'
  let p : Grid (M+2) (N+2) := (⟨a,by omega⟩,⟨b+1,by omega⟩)
  let q : Grid (M+2) (N+2) := (⟨a+k+1,by omega⟩,⟨b+k,by omega⟩)
  let r : Grid (M+2) (N+2) := (⟨a+1,by omega⟩,⟨b,by omega⟩)
  let t : Grid (M+2) (N+2) := (⟨a+k,by omega⟩,⟨b+k+1,by omega⟩)
  have hne : pairConfig p q ≠ pairConfig r t := by
    rw [ne_eq, pairConfig_eq_iff_pair_eq, pair_eq_iff]
    intro h
    rcases h with ⟨hpr,_⟩ | ⟨hpt,_⟩
    · have he := congrArg (fun v : Grid (M+2) (N+2) => v.1.val) hpr
      dsimp [p,r] at he
      omega
    · have he := congrArg (fun v : Grid (M+2) (N+2) => v.1.val) hpt
      dsimp [p,t] at he
      omega
  have hdist := (toleratesErasures_iff _ _ 1).mp hrobust (pairConfig p q) (pairConfig r t)
    (by simp) (by simp) hne
  have hreport (sensor : S) :
      bag (gridSensorDistance M N S hb) (pairConfig p q) sensor =
        bag (gridSensorDistance M N S hb) (pairConfig r t) sensor ↔
        ((a < sensor.val.1 ∧ sensor.val.1 ≤ a+k) ↔
          (b < sensor.val.2 ∧ sensor.val.2 ≤ b+k)) := by
    rw [grid_pair_report, grid_pair_report]
    exact skinny_trade_detector a b k sensor.val.1 sensor.val.2 hk
  have hcount : hammingDist
      (bag (gridSensorDistance M N S hb) (pairConfig p q))
      (bag (gridSensorDistance M N S hb) (pairConfig r t)) =
      (S.filter (fun z => ¬ ((a < z.1 ∧ z.1 ≤ a+k) ↔
        (b < z.2 ∧ z.2 ≤ b+k)))).card := by
    unfold hammingDist
    simp_rw [ne_eq, hreport]
    change (S.attach.filter _).card = _
    rw [Finset.filter_attach (fun z : ℕ × ℕ => ¬ ((a < z.1 ∧ z.1 ≤ a+k) ↔
      (b < z.2 ∧ z.2 ≤ b+k))) S]
    simp
  omega

end ShellObservability.Rectangle

namespace ShellObservability.Rectangle

open ShellTomography

private theorem one_erasure_leaves_one_of_two {A : Type*} [DecidableEq A]
    (erased : Finset A) (he : erased.card ≤ 1) (a b : A) (hne : a ≠ b) :
    a ∉ erased ∨ b ∉ erased := by
  by_cases ha : a ∈ erased
  · right
    intro hb
    exact hne ((Finset.card_le_one.mp he) a ha b hb)
  · exact Or.inl ha

/-- With all four corners present, the balanced interval cuts suffice for
single-erasure recovery of every mass-at-most-two configuration. -/
theorem gridIntervalCuts_implies_robust (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hcorners : GridHasCorners M N S)
    (hcuts : GridIntervalCuts M N S) : GridRobust M N S hb := by
  classical
  let s00 : S := ⟨(0,0),hcorners (by simp)⟩
  let s0N : S := ⟨(0,N+1),hcorners (by simp)⟩
  let sN0 : S := ⟨(M+1,0),hcorners (by simp)⟩
  let sNN : S := ⟨(M+1,N+1),hcorners (by simp)⟩
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
  have hsurvive (erased : Finset S) (he : erased.card ≤ 1) : ∃ s, s ∉ erased := by
    rcases one_erasure_leaves_one_of_two erased he s00 sNN hdiagNe with h | h
    · exact ⟨s00,h⟩
    · exact ⟨sNN,h⟩
  have hexact : ToleratesErasures (bag (gridSensorDistance M N S hb))
      (fun x => mass x = 2) 1 := by
    intro erased he x y hx hy hagree
    obtain ⟨p,q,rfl⟩ := (mass_two_iff_pairConfig x).mp hx
    obtain ⟨r,t,rfl⟩ := (mass_two_iff_pairConfig y).mp hy
    by_contra hne
    have hpairne : ({p,q} : Multiset (Grid (M+2) (N+2))) ≠ {r,t} := by
      simpa only [ne_eq, pairConfig_eq_iff_pair_eq] using hne
    have hnatne : ({gridCoordinates p,gridCoordinates q} : Multiset (ℕ × ℕ)) ≠
        {gridCoordinates r,gridCoordinates t} := by
      intro hh
      apply hpairne
      apply Multiset.map_injective (gridCoordinates_injective (M+2) (N+2))
      simpa only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] using hh
    have hbound : ∀ z ∈ ({gridCoordinates p,gridCoordinates q,gridCoordinates r,
        gridCoordinates t} : Multiset (ℕ × ℕ)), z.1 ≤ M+1 ∧ z.2 ≤ N+1 := by
      intro z hz
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl
      all_goals dsimp [gridCoordinates]; constructor
      all_goals omega
    have hreport (sensor : S) (hs : sensor ∉ erased) :
        distancePair sensor.val (gridCoordinates p) (gridCoordinates q) =
          distancePair sensor.val (gridCoordinates r) (gridCoordinates t) := by
      simpa only [grid_pair_report] using hagree sensor hs
    have hopposite := opposite_corner_pair_equality (M+1) (N+1) (gridCoordinates p)
      (gridCoordinates q) (gridCoordinates r) (gridCoordinates t) hbound
    have hzero : distancePair (0,0) (gridCoordinates p) (gridCoordinates q) =
        distancePair (0,0) (gridCoordinates r) (gridCoordinates t) := by
      rcases one_erasure_leaves_one_of_two erased he s00 sNN hdiagNe with hs | hs
      · exact hreport s00 hs
      · exact hopposite.1.mp (hreport sNN hs)
    have htop : distancePair (0,N+1) (gridCoordinates p) (gridCoordinates q) =
        distancePair (0,N+1) (gridCoordinates r) (gridCoordinates t) := by
      rcases one_erasure_leaves_one_of_two erased he s0N sN0 hantiNe with hs | hs
      · exact hreport s0N hs
      · exact hopposite.2.mp (hreport sN0 hs)
    obtain ⟨a,b,k,hk,ha,hb',hdetect⟩ := corner_collision_hasIntervalDetector (M+1) (N+1)
      (gridCoordinates p) (gridCoordinates q) (gridCoordinates r) (gridCoordinates t)
      hbound hnatne hzero htop
    have htwo := hcuts a b k hk (by omega) (by omega)
    obtain ⟨z,hz,w,hw,hzw⟩ := Finset.one_lt_card.mp (by omega : 1 <
      (S.filter (fun v => ¬ ((a < v.1 ∧ v.1 ≤ a+k) ↔
        (b < v.2 ∧ v.2 ≤ b+k)))).card)
    let sz : S := ⟨z,(Finset.mem_filter.mp hz).1⟩
    let sw : S := ⟨w,(Finset.mem_filter.mp hw).1⟩
    have hlabelNe : sz ≠ sw := fun hh => hzw (congrArg Subtype.val hh)
    rcases one_erasure_leaves_one_of_two erased he sz sw hlabelNe with hz' | hw'
    · exact hdetect z.1 z.2 (Finset.mem_filter.mp hz).2 (hreport sz hz')
    · exact hdetect w.1 w.2 (Finset.mem_filter.mp hw).2 (hreport sw hw')
  letI : Nonempty (Grid (M+2) (N+2)) := ⟨(⟨0,by omega⟩,⟨0,by omega⟩)⟩
  exact toleratesErasures_upTo_of_exact (gridSensorDistance M N S hb) 2 1 hsurvive hexact

/-- Exact interval-cut characterization for four-corner sensor sets, using
actual graph distances and all nonnegative occupancy populations of mass≤2. -/
theorem gridRobust_iff_intervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hcorners : GridHasCorners M N S) :
    GridRobust M N S hb ↔ GridIntervalCuts M N S :=
  ⟨gridRobust_implies_intervalCuts M N S hb,
    gridIntervalCuts_implies_robust M N S hb hcorners⟩

end ShellObservability.Rectangle
