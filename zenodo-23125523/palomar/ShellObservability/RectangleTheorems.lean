module

public import ShellObservability.RectangleRecovery
public import ShellObservability.RectangleBounds
public import ShellObservability.GridTheorems

@[expose] public section

/-! Exact recovery and structure of optimal sufficiently long rectangular grids. -/
namespace ShellObservability.Rectangle
open Finset ShellTomography
open GridTheorems (endpoint endpoint_eq_some)

/-- Interior coordinate endpoints of the concrete sensor incidence graph. -/
def rowEndpoint (M : ℕ) (S : Finset (ℕ × ℕ)) (s : S) : Option (Fin M) :=
  endpoint M s.val.1

def colEndpoint (N : ℕ) (S : Finset (ℕ × ℕ)) (s : S) : Option (Fin N) :=
  endpoint N s.val.2

/-- Singleton interval trades give all the incidence cross inequalities. -/
theorem intervalCuts_cross (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hcuts : GridIntervalCuts M N S) :
    ∀ i j, 2 ≤ crossDetectorCount (rowEndpoint M S) (colEndpoint N S) i j := by
  classical
  intro i j
  have hh := hcuts i.val j.val 1 (by omega) (by have := i.isLt; omega)
    (by have := j.isLt; omega)
  have heq : crossDetectorCount (rowEndpoint M S) (colEndpoint N S) i j =
      (S.filter (fun p => ¬ ((i.val < p.1 ∧ p.1 ≤ i.val+1) ↔
        (j.val < p.2 ∧ p.2 ≤ j.val+1)))).card := by
    unfold crossDetectorCount rowEndpoint colEndpoint
    simp only [ne_eq, endpoint_eq_some, card_filter]
    rw [sum_coe_sort S (fun p => if (p.1 = i.val+1 ∧ ¬p.2 = j.val+1) ∨
      (¬p.1 = i.val+1 ∧ p.2 = j.val+1) then 1 else 0)]
    apply sum_congr rfl
    intro p hp
    split_ifs <;> (try simp_all) <;> omega
  rwa [heq]

/-- Four distinct rectangular corners. -/
def corners (M N : ℕ) : Finset (ℕ × ℕ) :=
  {(0,0),(0,N+1),(M+1,0),(M+1,N+1)}

theorem corners_card (M N : ℕ) : (corners M N).card = 4 := by
  unfold corners
  repeat rw [card_insert_of_notMem]
  all_goals simp only [card_singleton, mem_insert, mem_singleton, Prod.mk.injEq]
  all_goals omega

private theorem endpoint_none_iff_boundary (m x : ℕ) (hx : x < m+2) :
    (endpoint m x).isNone ↔ x = 0 ∨ x = m+1 := by
  unfold endpoint
  split_ifs <;> (try simp_all) <;> omega

/-- On the bounded rectangle, incidence corners are exactly geometric corners. -/
theorem cornerCount_eq_four (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hc : GridHasCorners M N S) :
    cornerCount (rowEndpoint M S) (colEndpoint N S) = 4 := by
  classical
  have heq : cornerCount (rowEndpoint M S) (colEndpoint N S) =
      (S.filter (fun p => (endpoint M p.1).isNone ∧ (endpoint N p.2).isNone)).card := by
    unfold cornerCount rowEndpoint colEndpoint
    simp only [card_filter]
    exact sum_coe_sort S (fun p => if (endpoint M p.1).isNone ∧ (endpoint N p.2).isNone then (1 : ℕ) else 0)
  rw [heq, ← corners_card M N]
  congr 1
  ext p
  constructor
  · intro hp
    obtain ⟨hs,hx,hy⟩ := mem_filter.mp hp
    rw [endpoint_none_iff_boundary M p.1 (hb p hs).1] at hx
    rw [endpoint_none_iff_boundary N p.2 (hb p hs).2] at hy
    simp only [corners, mem_insert, mem_singleton, Prod.ext_iff]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp_all
  · intro hp
    refine mem_filter.mpr ⟨hc hp,?_⟩
    rw [endpoint_none_iff_boundary M p.1 (hb p (hc hp)).1,
      endpoint_none_iff_boundary N p.2 (hb p (hc hp)).2]
    simp only [corners, mem_insert, mem_singleton, Prod.ext_iff] at hp
    rcases hp with hp | hp | hp | hp <;> simp_all

/-- The short side controls the sharp lower bound beyond the 5/3 threshold. -/
theorem long_rectangle_robust_lower (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hc : GridHasCorners M N S)
    (hsize : N ≤ M) (hratio : 5*N ≤ 3*M) (hr : GridRobust M N S hb) :
    2*N+4 ≤ S.card := by
  have hh := RectangleBounds.long_rectangle_lower_bound (rowEndpoint M S)
    (colEndpoint N S) (by simpa using hsize) (by simpa using hratio)
    (intervalCuts_cross M N S (gridRobust_implies_intervalCuts M N S hb hr))
  simpa only [Fintype.card_fin, Fintype.card_coe, cornerCount_eq_four M N S hb hc] using hh

/-- All sensors in the two long-axis boundary columns. -/
def boundaryColumns (M N : ℕ) : Finset (ℕ × ℕ) :=
  ({0,M+1} : Finset ℕ) ×ˢ range (N+2)

theorem boundaryColumns_card (M N : ℕ) : (boundaryColumns M N).card = 2*N+4 := by
  simp [boundaryColumns, card_product]
  omega

theorem boundaryColumns_bounds (M N : ℕ) : GridSensorBounds M N (boundaryColumns M N) := by
  intro p hp
  simp only [boundaryColumns, mem_product, mem_insert, mem_singleton, mem_range] at hp
  rcases hp with ⟨hx,hy⟩
  rcases hx with hx | hx <;> constructor <;> omega

theorem boundaryColumns_corners (M N : ℕ) : GridHasCorners M N (boundaryColumns M N) := by
  intro p hp
  simp only [GridHasCorners, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> simp [boundaryColumns]

/-- Every balanced interval trade is detected at both boundary columns in
all of its short-direction levels. -/
theorem boundaryColumns_cuts (M N : ℕ) : GridIntervalCuts M N (boundaryColumns M N) := by
  intro a b k hk ha hb
  have hsub : ({(0,b+1),(M+1,b+1)} : Finset (ℕ × ℕ)) ⊆
      (boundaryColumns M N).filter (fun p => ¬ ((a < p.1 ∧ p.1 ≤ a+k) ↔
        (b < p.2 ∧ p.2 ≤ b+k))) := by
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    all_goals apply mem_filter.mpr; constructor
    all_goals first | (simp [boundaryColumns]; omega) | omega
  have hh := card_le_card hsub
  have hcard : ({(0,b+1),(M+1,b+1)} : Finset (ℕ × ℕ)).card = 2 := by
    rw [card_pair]; simp
  omega

/-- Exact corner-constrained optimum for sufficiently long rectangles, using
actual shortest-path bags and all populations of mass at most two. -/
theorem exact_long_rectangle_robust_minimum (M N : ℕ)
    (hsize : N ≤ M) (hratio : 5*N ≤ 3*M) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      S.card = 2*N+4 ∧ GridHasCorners M N S ∧ GridRobust M N S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      GridHasCorners M N S → GridRobust M N S hb → 2*N+4 ≤ S.card) := by
  constructor
  · refine ⟨boundaryColumns M N, boundaryColumns_bounds M N,
      boundaryColumns_card M N, boundaryColumns_corners M N, ?_⟩
    exact gridIntervalCuts_implies_robust M N _ (boundaryColumns_bounds M N)
      (boundaryColumns_corners M N) (boundaryColumns_cuts M N)
  · exact fun S hb hc hr => long_rectangle_robust_lower M N S hb hc hsize hratio hr

/-- Every optimal placement above the strict aspect threshold has an empty
long-direction line, exactly two sensors in each short-direction interior line,
only corners on the short boundary, and at most N occupied long interior lines. -/
theorem optimal_long_rectangle_rigidity (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hc : GridHasCorners M N S)
    (hratio : 5*N < 3*M) (hr : GridRobust M N S hb) (hcard : S.card = 2*N+4) :
    (∃ r, endpointDegree (rowEndpoint M S) r = 0) ∧
    (∀ c, endpointDegree (colEndpoint N S) c = 2) ∧
    (∀ s, colEndpoint N S s = none → rowEndpoint M S s = none) ∧
    ((univ.filter (fun r => 0 < endpointDegree (rowEndpoint M S) r)).card ≤ N) := by
  have hcuts := intervalCuts_cross M N S (gridRobust_implies_intervalCuts M N S hb hr)
  have hc' : Fintype.card S = 2*Fintype.card (Fin N)+
      cornerCount (rowEndpoint M S) (colEndpoint N S) := by
    simpa only [Fintype.card_coe, Fintype.card_fin, cornerCount_eq_four M N S hb hc] using hcard
  have hd := RectangleBounds.long_rectangle_optimal_degrees (rowEndpoint M S)
    (colEndpoint N S) (by simpa using hratio) hcuts hc'
  have hs := RectangleBounds.long_rectangle_optimal_support (rowEndpoint M S)
    (colEndpoint N S) (by simpa using hratio) hcuts hc'
  exact ⟨hd.1,hd.2,hs.1,by simpa using hs.2⟩

end ShellObservability.Rectangle
