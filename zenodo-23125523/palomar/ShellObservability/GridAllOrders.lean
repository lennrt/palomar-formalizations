module

public import ShellObservability.GridTheorems
public import ShellObservability.LeafStars

@[expose] public section

/-!
# The exact four-corner one-erasure optimum on every square grid

For every interior size `m ≥ 1`, the minimum number of sensors of a
one-erasure-robust placement on the `(m+2)` by `(m+2)` grid containing the four
corners is `⌈(3m+9)/2⌉ = (3*m+10)/2`. The lower bound is the refined degree
count with the corner term; the upper bound is the leaf-star placement.
-/
namespace ShellObservability.GridTheorems
open Finset OrderedStars

/-- Boundary coordinates carry no interior endpoint. -/
theorem endpoint_none_of_boundary (m x : ℕ) (h : x = 0 ∨ x = m+1) :
    endpoint m x = none := by
  unfold endpoint
  split_ifs with hh
  · exfalso; omega
  · rfl

/-- Interval-cut lower bound with all four corners at every interior size:
`6m+18 ≤ 4|S|`. -/
theorem interval_count_corner_lower_bound_all (m : ℕ) (S : Finset (ℕ × ℕ))
    (hm : 0 < m) (hcorners : corners m ⊆ S) (hcuts : BitCuts m S) :
    (3*m+10)/2 ≤ S.card := by
  have h := interval_count_lower_bound_refined m S hcuts
  have hb := hcuts 0 0 m hm (by omega) (by omega)
  simp only [Nat.zero_add] at hb
  have hc : 4 ≤ (S.filter (fun p => (endpoint m p.1).isNone ∧
      (endpoint m p.2).isNone)).card := by
    calc
      4 = (corners m).card := (corners_card m).symm
      _ ≤ _ := card_le_card ?_
    intro p hp
    refine mem_filter.mpr ⟨hcorners hp, ?_⟩
    simp only [corners, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      simp [endpoint_none_of_boundary m 0 (Or.inl rfl),
        endpoint_none_of_boundary m (m+1) (Or.inr rfl)]
  omega

/-- Exact minimum for the interval-cut formulation with all four corners, at
every interior size. -/
theorem exact_corner_interval_minimum_all (m : ℕ) (hm : 0 < m) :
    (∃ S : Finset (ℕ × ℕ), S.card = (3*m+10)/2 ∧
      (∀ p ∈ S, p.1 < m+2 ∧ p.2 < m+2) ∧
      corners m ⊆ S ∧ BitCuts m S) ∧
    (∀ S : Finset (ℕ × ℕ), corners m ⊆ S → BitCuts m S → (3*m+10)/2 ≤ S.card) := by
  constructor
  · obtain ⟨S, hcard, hbounds, h00, h0N, hN0, hNN, hcuts⟩ :=
      LeafStars.all_orders_optimal_interval_placement m hm
    refine ⟨S, hcard, hbounds, ?_, hcuts⟩
    intro p hp
    simp only [corners, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption
  · exact fun S hc hi => interval_count_corner_lower_bound_all m S hm hc hi

/-- Lower bound for every interior size: corners force 4·|S| ≥ 6m+18. -/
theorem grid_robust_corner_lower_bound_all (m : ℕ) (hm : 0 < m) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hc : GridHasCorners m S) (hr : GridRobust m S hb) :
    (3*m+10)/2 ≤ S.card := by
  exact interval_count_corner_lower_bound_all m S hm hc
    ((bitCuts_iff_gridIntervalCuts m S).mpr (gridRobust_implies_intervalCuts m S hb hr))

/-- Exact corner-constrained one-erasure optimum on every (m+2)×(m+2) grid. -/
theorem exact_corner_grid_robust_minimum_all (m : ℕ) (hm : 0 < m) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      S.card = (3*m+10)/2 ∧ GridHasCorners m S ∧ GridRobust m S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      GridHasCorners m S → GridRobust m S hb → (3*m+10)/2 ≤ S.card) := by
  obtain ⟨hexists, _⟩ := exact_corner_interval_minimum_all m hm
  constructor
  · obtain ⟨S, hcard, hb, hc, hi⟩ := hexists
    refine ⟨S, hb, hcard, hc, ?_⟩
    exact gridIntervalCuts_implies_robust m S hb hc
      ((bitCuts_iff_gridIntervalCuts m S).mp hi)
  · exact fun S hb hc hr => grid_robust_corner_lower_bound_all m hm S hb hc hr

end ShellObservability.GridTheorems
