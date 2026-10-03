module

public import ShellObservability.LowerBound
public import ShellObservability.OrderedStars
public import ShellObservability.GridRecovery

@[expose] public section

/-! Final extremal consequences for concrete finite sensor placements. -/
namespace ShellObservability.GridTheorems
open Finset OrderedStars

/-- The binary interval form convenient for the concrete constructions. -/
def BitCuts (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b k, 0 < k → a+k ≤ m → b+k ≤ m →
    2 ≤ (S.filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card

/-- Interior endpoint carried by a natural grid coordinate. -/
def endpoint (m x : ℕ) : Option (Fin m) :=
  if h : 1 ≤ x ∧ x < 1+m then some ⟨x-1,by omega⟩ else none

theorem endpoint_eq_some (m x : ℕ) (i : Fin m) :
    endpoint m x = some i ↔ x = i.val+1 := by
  unfold endpoint
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
    have := i.isLt
    omega
  · simp only [false_iff]
    have := i.isLt
    omega

theorem boundary_bit_iff (m x y : ℕ) :
    (endpoint m x).isSome ≠ (endpoint m y).isSome ↔ bit 1 m x ≠ bit 1 m y := by
  unfold endpoint bit
  split_ifs <;> simp_all

/-- All four actual corners of the `(m+2)` by `(m+2)` square. -/
def corners (m : ℕ) : Finset (ℕ × ℕ) :=
  {(0,0),(0,m+1),(m+1,0),(m+1,m+1)}

theorem corners_card (m : ℕ) : (corners m).card = 4 := by
  unfold corners
  repeat rw [card_insert_of_notMem]
  all_goals simp only [card_singleton, mem_insert, mem_singleton, Prod.mk.injEq]
  all_goals omega

private theorem endpoint_none_corner (m x : ℕ) (h : x = 0 ∨ x = m+1) :
    endpoint m x = none := by
  unfold endpoint
  split_ifs with hh
  · exfalso; omega
  · rfl

/-- The complete degree lower bound, now driven by literal interval counts. -/
theorem interval_count_lower_bound_refined (m : ℕ) (S : Finset (ℕ × ℕ))
    (hcuts : BitCuts m S) :
    6*m + (S.filter (fun p => bit 1 m p.1 ≠ bit 1 m p.2)).card +
      4*(S.filter (fun p => (endpoint m p.1).isNone ∧ (endpoint m p.2).isNone)).card ≤
      4*S.card := by
  let row : S → Option (Fin m) := fun s => endpoint m s.val.1
  let col : S → Option (Fin m) := fun s => endpoint m s.val.2
  have hcross : ∀ i j, 2 ≤ crossDetectorCount row col i j := by
    intro i j
    have hh := hcuts i.val j.val 1 (by omega) (by have := i.isLt; omega)
      (by have := j.isLt; omega)
    have heq : crossDetectorCount row col i j =
        (S.filter (fun p => bit (i.val+1) 1 p.1 ≠ bit (j.val+1) 1 p.2)).card := by
      unfold crossDetectorCount row col
      simp only [ne_eq, endpoint_eq_some, card_filter]
      rw [sum_coe_sort S (fun p => if (p.1 = i.val+1 ∧ ¬p.2 = j.val+1) ∨
        (¬p.1 = i.val+1 ∧ p.2 = j.val+1) then 1 else 0)]
      apply sum_congr rfl
      intro p hp
      unfold bit
      split_ifs <;> simp_all <;> omega
    rwa [heq]
  have hh := cross_detector_sensor_lower_bound row col rfl hcross
  have hB : boundaryCount row col =
      (S.filter (fun p => bit 1 m p.1 ≠ bit 1 m p.2)).card := by
    unfold boundaryCount row col
    simp only [card_filter, boundary_bit_iff]
    exact sum_coe_sort S (fun p => if bit 1 m p.1 ≠ bit 1 m p.2 then 1 else 0)
  have hC : cornerCount row col =
      (S.filter (fun p => (endpoint m p.1).isNone ∧ (endpoint m p.2).isNone)).card := by
    unfold cornerCount row col
    simp only [card_filter]
    exact sum_coe_sort S (fun p => if (endpoint m p.1).isNone ∧ (endpoint m p.2).isNone then 1 else 0)
  simpa only [Fintype.card_fin, Fintype.card_coe, hB, hC] using hh

/-- Every robust placement has strictly more than `3m/2` sensors. -/
theorem interval_count_lower_bound (m : ℕ) (S : Finset (ℕ × ℕ)) (hm : 0 < m)
    (hcuts : BitCuts m S) : 3*m < 2*S.card := by
  have h := interval_count_lower_bound_refined m S hcuts
  have hb := hcuts 0 0 m hm (by omega) (by omega)
  simp only [Nat.zero_add] at hb
  omega

/-- Retaining the four corners costs exactly the additional term needed for
optimality of the split-edge construction on `m=4q`. -/
theorem interval_count_corner_lower_bound (q : ℕ) (S : Finset (ℕ × ℕ))
    (hq : 0 < q) (hcorners : corners (4*q) ⊆ S) (hcuts : BitCuts (4*q) S) :
    6*q+5 ≤ S.card := by
  have h := interval_count_lower_bound_refined (4*q) S hcuts
  have hb := hcuts 0 0 (4*q) (by omega) (by omega) (by omega)
  simp only [Nat.zero_add] at hb
  have hc : 4 ≤ (S.filter (fun p => (endpoint (4*q) p.1).isNone ∧
      (endpoint (4*q) p.2).isNone)).card := by
    calc
      4 = (corners (4*q)).card := (corners_card (4*q)).symm
      _ ≤ _ := card_le_card ?_
    intro p hp
    refine mem_filter.mpr ⟨hcorners hp, ?_⟩
    simp only [corners, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp [endpoint_none_corner (4*q) 0 (Or.inl rfl),
        endpoint_none_corner (4*q) (4*q+1) (Or.inr rfl)]
  omega

/-- Exact minimum for the interval-cut formulation with all four corners. -/
theorem exact_corner_interval_minimum (q : ℕ) (hq : 0 < q) :
    (∃ S : Finset (ℕ × ℕ), S.card = 6*q+5 ∧
      (∀ p ∈ S, p.1 < 4*q+2 ∧ p.2 < 4*q+2) ∧
      corners (4*q) ⊆ S ∧ BitCuts (4*q) S) ∧
    (∀ S : Finset (ℕ × ℕ), corners (4*q) ⊆ S → BitCuts (4*q) S → 6*q+5 ≤ S.card) := by
  constructor
  · refine ⟨splitPlacement q,splitPlacement_card hq,?_,?_,?_⟩
    · exact fun _ hp => splitPlacement_bounds hp
    · intro p hp
      simp only [corners,mem_insert,mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · exact fun a b k hk ha hb => splitPlacement_interval_cut_ge_two hq hk ha hb
  · exact fun S hc hi => interval_count_corner_lower_bound q S hq hc hi

/-- The executable binary membership form and the geometric interval form
express the identical set of sensor detectors. -/
theorem bitCuts_iff_gridIntervalCuts (m : ℕ) (S : Finset (ℕ × ℕ)) :
    BitCuts m S ↔ GridIntervalCuts m S := by
  have hpoint (a b k : ℕ) (p : ℕ × ℕ) :
      (bit (a+1) k p.1 ≠ bit (b+1) k p.2) ↔
      ¬ ((a < p.1 ∧ p.1 ≤ a+k) ↔ (b < p.2 ∧ p.2 ≤ b+k)) := by
    unfold bit
    split_ifs <;> simp_all <;> omega
  simp only [BitCuts, GridIntervalCuts, hpoint]

/-- Universal lower bound for actual shortest-path histogram recovery after
one arbitrary sensor erasure. No corner requirement is imposed. -/
theorem grid_robust_sensor_lower_bound (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hm : 0 < m) (hr : GridRobust m S hb) :
    3*m < 2*S.card := by
  exact interval_count_lower_bound m S hm
    ((bitCuts_iff_gridIntervalCuts m S).mpr (gridRobust_implies_intervalCuts m S hb hr))

/-- Every actual robust placement containing the four corners meets the sharp
`6q+5` lower bound on a `(4q+2)` by `(4q+2)` grid. -/
theorem grid_robust_corner_lower_bound (q : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds (4*q) S) (hq : 0 < q)
    (hc : GridHasCorners (4*q) S) (hr : GridRobust (4*q) S hb) :
    6*q+5 ≤ S.card := by
  exact interval_count_corner_lower_bound q S hq hc
    ((bitCuts_iff_gridIntervalCuts (4*q) S).mpr
      (gridRobust_implies_intervalCuts (4*q) S hb hr))

/-- Exact constrained optimum for the actual graph and all nonnegative integer
occupancies of mass at most two, including repeated targets and the empty case. -/
theorem exact_corner_grid_robust_minimum (q : ℕ) (hq : 0 < q) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds (4*q) S),
      S.card = 6*q+5 ∧ GridHasCorners (4*q) S ∧ GridRobust (4*q) S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds (4*q) S),
      GridHasCorners (4*q) S → GridRobust (4*q) S hb → 6*q+5 ≤ S.card) := by
  obtain ⟨hexists,hlower⟩ := exact_corner_interval_minimum q hq
  constructor
  · obtain ⟨S,hcard,hb,hc,hi⟩ := hexists
    refine ⟨S,hb,hcard,hc,?_⟩
    exact gridIntervalCuts_implies_robust (4*q) S hb hc
      ((bitCuts_iff_gridIntervalCuts (4*q) S).mp hi)
  · exact fun S hb hc hr => grid_robust_corner_lower_bound q S hb hq hc hr

/-- The explicit remainder-dependent upper bound at every grid order n=m+2≥6. -/
theorem exists_grid_robust_placement (m : ℕ) (hm : 4 ≤ m) :
    ∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      S.card ≤ 6*(m/4)+5+4*(m%4) ∧ GridHasCorners m S ∧ GridRobust m S hb := by
  have hq : 0 < m/4 := by omega
  have hdecomp : 4*(m/4)+m%4 = m := by omega
  let S := paddedPlacement (m/4) (m%4)
  have hb : GridSensorBounds m S := by
    intro p hp
    simpa only [hdecomp] using paddedPlacement_bounds hp
  have hc : GridHasCorners m S := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact paddedPlacement_corner00 _ _
    · simpa only [hdecomp] using paddedPlacement_corner0N (m/4) (m%4)
    · simpa only [hdecomp] using paddedPlacement_cornerN0 (m/4) (m%4)
    · simpa only [hdecomp] using paddedPlacement_cornerNN (m/4) (m%4)
  have hi : BitCuts m S := by
    intro a b k hk ha hb'
    apply paddedPlacement_interval_cut_ge_two hq hk <;> omega
  refine ⟨S,hb,paddedPlacement_card_le hq,hc,?_⟩
  exact gridIntervalCuts_implies_robust m S hb hc ((bitCuts_iff_gridIntervalCuts m S).mp hi)

/-- A single theorem packages the sharp leading lower and upper coefficients,
without assuming the interval reduction or any recoverability conclusion. -/
theorem all_orders_grid_robust_bounds (m : ℕ) (hm : 4 ≤ m) :
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      GridRobust m S hb → 3*m < 2*S.card) ∧
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      2*S.card ≤ 3*m+25 ∧ GridHasCorners m S ∧ GridRobust m S hb) := by
  constructor
  · exact fun S hb hr => grid_robust_sensor_lower_bound m S hb (by omega) hr
  · obtain ⟨S,hb,hcard,hc,hr⟩ := exists_grid_robust_placement m hm
    refine ⟨S,hb,?_,hc,hr⟩
    have hmod := Nat.mod_lt m (by omega : 0 < 4)
    have hdecomp : 4*(m/4)+m%4 = m := by omega
    omega

end ShellObservability.GridTheorems
