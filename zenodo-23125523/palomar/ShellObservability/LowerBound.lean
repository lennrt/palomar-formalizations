module

public import Mathlib.Tactic

@[expose] public section

/-!
# Counting sensors by interior-line incidences

An interior sensor is an edge between a row and a column, a noncorner boundary
sensor is a half-edge, and a corner has no interior-line incidence. Degree-one
lines charge high-degree incidences or boundary half-edges. This module records
the complete counting argument, independently of its geometric premise.
-/

namespace ShellObservability

/-- The exact algebra behind the low/high degree charge. -/
theorem degree_charge_identity (L M H h B : ℤ) :
    2 * (L + 2 * M + h + B) - 3 * (L + M + H) =
      M + (h + B - L) + (h - 3 * H) + B := by ring

/-- Degree statistics give the strengthened bound, retaining boundary and
corner contributions. -/
theorem degree_statistics_lower_bound
    (L M H h D B C N lines : ℕ)
    (hline : L + M + H = lines)
    (hsum : D = L + 2 * M + h)
    (hcharge : L ≤ h + B)
    (hhigh : 3 * H ≤ h)
    (hinc : D + B + 2 * C = 2 * N) :
    3 * lines + B + 4 * C ≤ 4 * N := by omega

/-- In the square case there are exactly `2m` interior lines. -/
theorem square_degree_statistics_lower_bound
    (L M H h D B C N m : ℕ)
    (hline : L + M + H = 2 * m)
    (hsum : D = L + 2 * M + h)
    (hcharge : L ≤ h + B)
    (hhigh : 3 * H ≤ h)
    (hinc : D + B + 2 * C = 2 * N) :
    6 * m + B + 4 * C ≤ 4 * N := by
  have hh := degree_statistics_lower_bound L M H h D B C N (2 * m)
    hline hsum hcharge hhigh hinc
  omega

section Incidences

variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

/-- A sensor endpoint is an interior line or `none` for a boundary coordinate. -/
def endpointDegree (endpoint : T → Option V) (v : V) : ℕ :=
  ∑ t, if endpoint t = some v then 1 else 0

/-- Double counting endpoint incidences with arbitrary natural weights. -/
theorem sum_weighted_endpointDegree (endpoint : T → Option V) (weight : V → ℕ) :
    (∑ v, weight v * endpointDegree endpoint v) =
      ∑ t, (endpoint t).elim 0 weight := by
  classical
  simp only [endpointDegree, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases he : endpoint t with
  | none => simp
  | some v => simp

def lowCount (degree : V → ℕ) : ℕ := ∑ v, if degree v = 1 then 1 else 0

def middleCount (degree : V → ℕ) : ℕ := ∑ v, if degree v = 2 then 1 else 0

def highCount (degree : V → ℕ) : ℕ := ∑ v, if 3 ≤ degree v then 1 else 0

def highDegreeSum (degree : V → ℕ) : ℕ :=
  ∑ v, if 3 ≤ degree v then degree v else 0

omit [DecidableEq V] in
/-- Every positive-degree line belongs to one of the three degree classes. -/
theorem degree_class_partition (degree : V → ℕ) (hpos : ∀ v, 0 < degree v) :
    lowCount degree + middleCount degree + highCount degree = Fintype.card V := by
  unfold lowCount middleCount highCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  trans ∑ _v : V, 1
  · apply Finset.sum_congr rfl
    intro v _
    have hv := hpos v
    split_ifs <;> omega
  · simp

omit [DecidableEq V] in
/-- Decompose the sum of degrees into the three classes. -/
theorem degree_class_sum (degree : V → ℕ) (hpos : ∀ v, 0 < degree v) :
    (∑ v, degree v) = lowCount degree + 2 * middleCount degree + highDegreeSum degree := by
  unfold lowCount middleCount highDegreeSum
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hv := hpos v
  split_ifs <;> omega

omit [DecidableEq V] in
/-- Every high line supplies at least three incidences. -/
theorem high_degree_bound (degree : V → ℕ) :
    3 * highCount degree ≤ highDegreeSum degree := by
  unfold highCount highDegreeSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  split_ifs <;> omega

/-- Degree-one lines count once at their unique incident sensor. -/
theorem lowCount_eq_endpoint_sum (endpoint : T → Option V) :
    lowCount (endpointDegree endpoint) =
      ∑ t, (endpoint t).elim 0 (fun v => if endpointDegree endpoint v = 1 then 1 else 0) := by
  rw [← sum_weighted_endpointDegree]
  unfold lowCount
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp_all

/-- High-line incidences can equally be counted at the sensors. -/
theorem highDegreeSum_eq_endpoint_sum (endpoint : T → Option V) :
    highDegreeSum (endpointDegree endpoint) =
      ∑ t, (endpoint t).elim 0 (fun v => if 3 ≤ endpointDegree endpoint v then 1 else 0) := by
  rw [← sum_weighted_endpointDegree]
  unfold highDegreeSum
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp_all

end Incidences

end ShellObservability

namespace ShellObservability

section BipartiteIncidences

variable {T R C : Type*} [Fintype T] [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C]

/-- A sensor with exactly one interior coordinate is a boundary half-edge. -/
def boundaryCount (row : T → Option R) (col : T → Option C) : ℕ :=
  ∑ t, if (row t).isSome ≠ (col t).isSome then 1 else 0

/-- A sensor with no interior coordinates is a corner. -/
def cornerCount (row : T → Option R) (col : T → Option C) : ℕ :=
  ∑ t, if (row t).isNone ∧ (col t).isNone then 1 else 0

/-- Counting all row/column incidences, boundary half-edges, and corners. -/
theorem bipartite_incidence_identity (row : T → Option R) (col : T → Option C) :
    (∑ r, endpointDegree row r) + (∑ c, endpointDegree col c) +
      boundaryCount row col + 2 * cornerCount row col = 2 * Fintype.card T := by
  have hr := sum_weighted_endpointDegree row (fun _ => 1)
  have hc := sum_weighted_endpointDegree col (fun _ => 1)
  simp only [one_mul] at hr hc
  rw [hr, hc]
  unfold boundaryCount cornerCount
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  trans ∑ _t : T, 2
  · apply Finset.sum_congr rfl
    intro t _
    cases row t <;> cases col t <;> simp
  · simp [Nat.mul_comm]

/-- The selected-intersection cross inequality forbids low-low and low-middle
edges. Each low incidence can therefore be charged to a high incidence or a
boundary half-edge. -/
theorem bipartite_low_charge (row : T → Option R) (col : T → Option C)
    (hcross : ∀ t r c, row t = some r → col t = some c →
      4 ≤ endpointDegree row r + endpointDegree col c) :
    lowCount (endpointDegree row) + lowCount (endpointDegree col) ≤
      highDegreeSum (endpointDegree row) + highDegreeSum (endpointDegree col) +
        boundaryCount row col := by
  rw [lowCount_eq_endpoint_sum, lowCount_eq_endpoint_sum,
    highDegreeSum_eq_endpoint_sum, highDegreeSum_eq_endpoint_sum]
  unfold boundaryCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro t _
  cases hr : row t with
  | none =>
    cases hc : col t with
    | none => simp
    | some c =>
      simp only [Option.elim_none, Option.elim_some, Option.isSome_none, Option.isSome_some]
      split_ifs <;> simp_all
  | some r =>
    cases hc : col t with
    | none =>
      simp only [Option.elim_none, Option.elim_some, Option.isSome_none, Option.isSome_some]
      split_ifs <;> simp_all
    | some c =>
      have hh := hcross t r c hr hc
      simp only [Option.elim_some, Option.isSome_some, ne_eq, not_true_eq_false,
        ↓reduceIte, add_zero]
      split_ifs <;> omega

/-- The boundary-aware `3/2` counting bound follows directly from the incidence
model and cross constraints whenever all interior line degrees are positive. -/
theorem bipartite_sensor_lower_bound (row : T → Option R) (col : T → Option C)
    (hrow : ∀ r, 0 < endpointDegree row r)
    (hcol : ∀ c, 0 < endpointDegree col c)
    (hcross : ∀ t r c, row t = some r → col t = some c →
      4 ≤ endpointDegree row r + endpointDegree col c) :
    3 * (Fintype.card R + Fintype.card C) + boundaryCount row col +
      4 * cornerCount row col ≤ 4 * Fintype.card T := by
  have hrpart := degree_class_partition (endpointDegree row) hrow
  have hcpart := degree_class_partition (endpointDegree col) hcol
  have hrsum := degree_class_sum (endpointDegree row) hrow
  have hcsum := degree_class_sum (endpointDegree col) hcol
  have hrhigh := high_degree_bound (endpointDegree row)
  have hchigh := high_degree_bound (endpointDegree col)
  have hcharge := bipartite_low_charge row col hcross
  have hinc := bipartite_incidence_identity row col
  omega

end BipartiteIncidences

end ShellObservability

namespace ShellObservability

section ZeroLines

variable {T R C : Type*} [Fintype T] [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C]

omit [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C] in
theorem boundary_add_corner_le (row : T → Option R) (col : T → Option C) :
    boundaryCount row col + cornerCount row col ≤ Fintype.card T := by
  unfold boundaryCount cornerCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _t : T, 1 := by
      apply Finset.sum_le_sum
      intro t _
      cases row t <;> cases col t <;> simp
    _ = _ := by simp

omit [Fintype R] [DecidableEq R] in
theorem column_incidences_add_corners_le (row : T → Option R) (col : T → Option C) :
    (∑ c, endpointDegree col c) + cornerCount row col ≤ Fintype.card T := by
  have hc := sum_weighted_endpointDegree col (fun _ => 1)
  simp only [one_mul] at hc
  rw [hc]
  unfold cornerCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _t : T, 1 := by
      apply Finset.sum_le_sum
      intro t _
      cases row t <;> cases col t <;> simp
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem row_incidences_add_corners_le (row : T → Option R) (col : T → Option C) :
    (∑ r, endpointDegree row r) + cornerCount row col ≤ Fintype.card T := by
  have hr := sum_weighted_endpointDegree row (fun _ => 1)
  simp only [one_mul] at hr
  rw [hr]
  unfold cornerCount
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _t : T, 1 := by
      apply Finset.sum_le_sum
      intro t _
      cases row t <;> cases col t <;> simp
    _ = _ := by simp

/-- The complete square counting bound, including zero-degree interior lines.
The two premises are precisely the weak cross inequality for every intersection
and its stronger form at selected interior intersections. -/
theorem square_bipartite_sensor_lower_bound (row : T → Option R) (col : T → Option C)
    (hsize : Fintype.card R = Fintype.card C)
    (hweak : ∀ r c, 2 ≤ endpointDegree row r + endpointDegree col c)
    (hcross : ∀ t r c, row t = some r → col t = some c →
      4 ≤ endpointDegree row r + endpointDegree col c) :
    6 * Fintype.card R + boundaryCount row col + 4 * cornerCount row col ≤
      4 * Fintype.card T := by
  have hBC := boundary_add_corner_le row col
  by_cases hrow : ∀ r, 0 < endpointDegree row r
  · by_cases hcol : ∀ c, 0 < endpointDegree col c
    · have h := bipartite_sensor_lower_bound row col hrow hcol hcross
      omega
    · push Not at hcol
      obtain ⟨c, hc⟩ := hcol
      have hsum : 2 * Fintype.card R ≤ ∑ r, endpointDegree row r := by
        calc
          _ = ∑ _r : R, 2 := by simp [Nat.mul_comm]
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro r _
            have hw := hweak r c
            omega
      have hN := row_incidences_add_corners_le row col
      omega
  · push Not at hrow
    obtain ⟨r, hr⟩ := hrow
    have hsum : 2 * Fintype.card C ≤ ∑ c, endpointDegree col c := by
      calc
        _ = ∑ _c : C, 2 := by simp [Nat.mul_comm]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro c _
          have hw := hweak r c
          omega
    have hN := column_incidences_add_corners_le row col
    omega

/-- Dropping the nonnegative boundary terms gives the asymptotic lower bound. -/
theorem square_sensor_count_lower_bound (row : T → Option R) (col : T → Option C)
    (hsize : Fintype.card R = Fintype.card C)
    (hweak : ∀ r c, 2 ≤ endpointDegree row r + endpointDegree col c)
    (hcross : ∀ t r c, row t = some r → col t = some c →
      4 ≤ endpointDegree row r + endpointDegree col c) :
    3 * Fintype.card R ≤ 2 * Fintype.card T := by
  have h := square_bipartite_sensor_lower_bound row col hsize hweak hcross
  omega

end ZeroLines

end ShellObservability

namespace ShellObservability

section CrossDetectors

variable {T R C : Type*} [Fintype T] [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C]

/-- Sensors lying on exactly one of a chosen interior row and column. -/
def crossDetectorCount (row : T → Option R) (col : T → Option C) (r : R) (c : C) : ℕ :=
  ∑ t, if (row t = some r ∧ col t ≠ some c) ∨ (row t ≠ some r ∧ col t = some c)
    then 1 else 0

/-- Sensors lying at the chosen interior intersection. -/
def intersectionCount (row : T → Option R) (col : T → Option C) (r : R) (c : C) : ℕ :=
  ∑ t, if row t = some r ∧ col t = some c then 1 else 0

omit [Fintype R] [Fintype C] in
/-- The cross detector count is the degree sum minus twice the intersection. -/
theorem cross_incidence_identity (row : T → Option R) (col : T → Option C) (r : R) (c : C) :
    crossDetectorCount row col r c + 2 * intersectionCount row col r c =
      endpointDegree row r + endpointDegree col c := by
  unfold crossDetectorCount intersectionCount endpointDegree
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hr : row t = some r <;> by_cases hc : col t = some c <;> simp [hr, hc]

omit [Fintype R] [Fintype C] in
/-- A selected intersection contributes at least one sensor to its intersection count. -/
theorem selected_intersection_positive (row : T → Option R) (col : T → Option C)
    (t : T) (r : R) (c : C) (hr : row t = some r) (hc : col t = some c) :
    1 ≤ intersectionCount row col r c := by
  unfold intersectionCount
  calc
    1 = (if row t = some r ∧ col t = some c then 1 else 0) := by simp [hr, hc]
    _ ≤ _ := Finset.single_le_sum
      (f := fun u : T => if row u = some r ∧ col u = some c then 1 else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)

/-- Two detectors for each singleton cross force the universal square lower
bound. This theorem derives the complete degree argument from cross counts. -/
theorem cross_detector_sensor_lower_bound (row : T → Option R) (col : T → Option C)
    (hsize : Fintype.card R = Fintype.card C)
    (hcut : ∀ r c, 2 ≤ crossDetectorCount row col r c) :
    6 * Fintype.card R + boundaryCount row col + 4 * cornerCount row col ≤
      4 * Fintype.card T := by
  apply square_bipartite_sensor_lower_bound row col hsize
  · intro r c
    have hidentity := cross_incidence_identity row col r c
    have htwo := hcut r c
    omega
  · intro t r c hr hc
    have hidentity := cross_incidence_identity row col r c
    have htwo := hcut r c
    have hselected := selected_intersection_positive row col t r c hr hc
    omega

end CrossDetectors

end ShellObservability

namespace ShellObservability

section GridCoordinates

variable {T : Type*} [Fintype T] {m : ℕ}

/-- Identify the `m` interior coordinates of an `(m+2)`-vertex path; boundary
coordinates have no interior-line endpoint. -/
def interiorCoordinate (x : Fin (m + 2)) : Option (Fin m) :=
  if h : 0 < x.val ∧ x.val < m + 1 then
    some ⟨x.val - 1, by omega⟩
  else none

/-- Interior index `i` represents the actual grid coordinate `i+1`. -/
theorem interiorCoordinate_eq_some (x : Fin (m + 2)) (i : Fin m) :
    interiorCoordinate x = some i ↔ x.val = i.val + 1 := by
  unfold interiorCoordinate
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
    omega
  · simp only [false_iff]
    have hi := i.isLt
    omega

/-- Singleton-cross detector count expressed directly in grid coordinates. -/
def gridCrossCount (location : T → Fin (m + 2) × Fin (m + 2)) (r c : Fin m) : ℕ :=
  ∑ t, if ((location t).1.val = r.val + 1 ∧ (location t).2.val ≠ c.val + 1) ∨
      ((location t).1.val ≠ r.val + 1 ∧ (location t).2.val = c.val + 1)
    then 1 else 0

theorem gridCrossCount_eq (location : T → Fin (m + 2) × Fin (m + 2)) (r c : Fin m) :
    gridCrossCount location r c =
      crossDetectorCount (fun t => interiorCoordinate (location t).1)
        (fun t => interiorCoordinate (location t).2) r c := by
  simp only [gridCrossCount, crossDetectorCount, interiorCoordinate_eq_some, ne_eq]

/-- Concrete square-grid form: two detectors for each interior singleton cross
force at least `3m/2` selected sensor vertices. -/
theorem grid_cross_sensor_lower_bound (location : T → Fin (m + 2) × Fin (m + 2))
    (hcut : ∀ r c : Fin m, 2 ≤ gridCrossCount location r c) :
    3 * m ≤ 2 * Fintype.card T := by
  have h := cross_detector_sensor_lower_bound
    (fun t => interiorCoordinate (location t).1)
    (fun t => interiorCoordinate (location t).2) rfl
    (by intro r c; rw [← gridCrossCount_eq]; exact hcut r c)
  simp only [Fintype.card_fin] at h
  omega

/-- Retaining boundary and corner terms strengthens the concrete grid bound. -/
theorem grid_cross_sensor_lower_bound_refined (location : T → Fin (m + 2) × Fin (m + 2))
    (hcut : ∀ r c : Fin m, 2 ≤ gridCrossCount location r c) :
    6 * m + boundaryCount (fun t => interiorCoordinate (location t).1)
      (fun t => interiorCoordinate (location t).2) +
      4 * cornerCount (fun t => interiorCoordinate (location t).1)
        (fun t => interiorCoordinate (location t).2) ≤ 4 * Fintype.card T := by
  simpa only [Fintype.card_fin] using cross_detector_sensor_lower_bound
    (fun t => interiorCoordinate (location t).1)
    (fun t => interiorCoordinate (location t).2) rfl
    (by intro r c; rw [← gridCrossCount_eq]; exact hcut r c)

/-- A pair of necessary boundary detectors excludes equality in the leading
`3m/2` bound. -/
theorem grid_cross_sensor_lower_bound_strict (location : T → Fin (m + 2) × Fin (m + 2))
    (hcut : ∀ r c : Fin m, 2 ≤ gridCrossCount location r c)
    (hboundary : 2 ≤ boundaryCount (fun t => interiorCoordinate (location t).1)
      (fun t => interiorCoordinate (location t).2)) :
    3 * m < 2 * Fintype.card T := by
  have h := grid_cross_sensor_lower_bound_refined location hcut
  omega

end GridCoordinates

end ShellObservability
