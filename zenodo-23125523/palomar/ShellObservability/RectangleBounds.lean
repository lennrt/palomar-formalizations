module

public import ShellObservability.LowerBound

@[expose] public section

/-! Rectangular sensor counting and rigidity beyond the aspect-ratio threshold.
The incidence hypotheses are supplied geometrically by singleton interval cuts. -/
namespace ShellObservability.RectangleBounds
open ShellObservability

variable {T R C : Type*} [Fintype T] [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C]

/-- A rectangular placement either pays the positive-line charge or has a zero
line forcing two sensors for every line in the other direction. -/
theorem rectangular_cross_lower_alternatives
    (row : T → Option R) (col : T → Option C)
    (hcut : ∀ r c, 2 ≤ crossDetectorCount row col r c) :
    (3*(Fintype.card R+Fintype.card C)+boundaryCount row col+
      4*cornerCount row col ≤ 4*Fintype.card T) ∨
    (2*Fintype.card R+cornerCount row col ≤ Fintype.card T) ∨
    (2*Fintype.card C+cornerCount row col ≤ Fintype.card T) := by
  by_cases hr : ∀ r, 0 < endpointDegree row r
  · by_cases hc : ∀ c, 0 < endpointDegree col c
    · left
      apply bipartite_sensor_lower_bound row col hr hc
      intro t r c htr htc
      have hi := cross_incidence_identity row col r c
      have hp := selected_intersection_positive row col t r c htr htc
      have hh := hcut r c
      omega
    · push Not at hc
      obtain ⟨c,hc⟩ := hc
      have hd (r : R) : 2 ≤ endpointDegree row r := by
        have hi := cross_incidence_identity row col r c
        have hh := hcut r c
        omega
      have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) => hd r)
      have hi := row_incidences_add_corners_le row col
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
      exact Or.inr (Or.inl (by omega))
  · push Not at hr
    obtain ⟨r,hr⟩ := hr
    have hd (c : C) : 2 ≤ endpointDegree col c := by
      have hi := cross_incidence_identity row col r c
      have hh := hcut r c
      omega
    have hs := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) => hd c)
    have hi := column_incidences_add_corners_le row col
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
    exact Or.inr (Or.inr (by omega))

/-- Beyond aspect ratio 5/3, the short direction controls the lower bound. -/
theorem long_rectangle_lower_bound
    (row : T → Option R) (col : T → Option C)
    (hsize : Fintype.card C ≤ Fintype.card R)
    (hratio : 5*Fintype.card C ≤ 3*Fintype.card R)
    (hcut : ∀ r c, 2 ≤ crossDetectorCount row col r c) :
    2*Fintype.card C+cornerCount row col ≤ Fintype.card T := by
  have h := rectangular_cross_lower_alternatives row col hcut
  rcases h with h | h | h <;> omega

/-- At the short-direction optimum above the strict transition, an empty
long-direction line is necessary; every short-direction line has degree two. -/
theorem long_rectangle_optimal_degrees
    (row : T → Option R) (col : T → Option C)
    (hratio : 5*Fintype.card C < 3*Fintype.card R)
    (hcut : ∀ r c, 2 ≤ crossDetectorCount row col r c)
    (hcard : Fintype.card T = 2*Fintype.card C+cornerCount row col) :
    (∃ r, endpointDegree row r = 0) ∧ (∀ c, endpointDegree col c = 2) := by
  have hzero : ∃ r, endpointDegree row r = 0 := by
    by_contra hn
    push Not at hn
    have hr (r : R) : 0 < endpointDegree row r := by have := hn r; omega
    have hc (c : C) : 0 < endpointDegree col c := by
      by_contra hh
      have hd (r : R) : 2 ≤ endpointDegree row r := by
        have hi := cross_incidence_identity row col r c
        have hh' := hcut r c
        omega
      have hs := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset R)) => hd r)
      have hi := row_incidences_add_corners_le row col
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs
      omega
    have hp := bipartite_sensor_lower_bound row col hr hc (by
      intro t r c htr htc
      have hi := cross_incidence_identity row col r c
      have hp := selected_intersection_positive row col t r c htr htc
      have hh := hcut r c
      omega)
    omega
  obtain ⟨r,hr⟩ := hzero
  have hd (c : C) : 2 ≤ endpointDegree col c := by
    have hi := cross_incidence_identity row col r c
    have hh := hcut r c
    omega
  have hs := Finset.sum_le_sum (fun c (_ : c ∈ (Finset.univ : Finset C)) => hd c)
  have hi := column_incidences_add_corners_le row col
  have heq : (∑ c : C, 2) = ∑ c, endpointDegree col c := by
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hs ⊢
    omega
  refine ⟨⟨r,hr⟩,fun c => ?_⟩
  exact ((Finset.sum_eq_sum_iff_of_le (fun c _ => hd c)).mp heq c (Finset.mem_univ c)).symm

/-- Count the sensors that miss every short-direction interior line. -/
theorem short_direction_accounting (row : T → Option R) (col : T → Option C) :
    (∑ c, endpointDegree col c)+cornerCount row col+
      (∑ t, if (row t).isSome ∧ (col t).isNone then 1 else 0) = Fintype.card T := by
  have hc := sum_weighted_endpointDegree col (fun _ => 1)
  simp only [one_mul] at hc
  rw [hc]
  unfold cornerCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  trans ∑ _t : T, 1
  · apply Finset.sum_congr rfl
    intro t _
    cases row t <;> cases col t <;> simp
  · simp

/-- Optimal long rectangles have no noncorner short-boundary sensors, and at
most as many occupied long-direction interior lines as short-direction lines. -/
theorem long_rectangle_optimal_support
    (row : T → Option R) (col : T → Option C)
    (hratio : 5*Fintype.card C < 3*Fintype.card R)
    (hcut : ∀ r c, 2 ≤ crossDetectorCount row col r c)
    (hcard : Fintype.card T = 2*Fintype.card C+cornerCount row col) :
    (∀ t, col t = none → row t = none) ∧
    ((Finset.univ.filter (fun r => 0 < endpointDegree row r)).card ≤ Fintype.card C) := by
  classical
  have hd := (long_rectangle_optimal_degrees row col hratio hcut hcard).2
  have hi := short_direction_accounting row col
  simp only [hd, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hi
  have hnone (t : T) (hc : col t = none) : row t = none := by
    have hsum : (∑ t, if (row t).isSome ∧ (col t).isNone then 1 else 0) = 0 := by omega
    have ht := (Finset.sum_eq_zero_iff.mp hsum) t (Finset.mem_univ t)
    cases hr : row t with
    | none => rfl
    | some r => simp [hr,hc] at ht
  refine ⟨hnone,?_⟩
  have hrow (r : R) (hr : 0 < endpointDegree row r) : 2 ≤ endpointDegree row r := by
    obtain ⟨t,_,ht⟩ := Finset.sum_pos_iff.mp hr
    have htr : row t = some r := by
      by_contra hn
      simp [hn] at ht
    cases hc : col t with
    | none => have := hnone t hc; rw [htr] at this; contradiction
    | some c =>
      have hi := cross_incidence_identity row col r c
      have hp := selected_intersection_positive row col t r c htr hc
      have hh := hcut r c
      have hdc := hd c
      omega
  have hs : 2*(Finset.univ.filter (fun r => 0 < endpointDegree row r)).card ≤
      ∑ r, endpointDegree row r := by
    rw [Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r _
    split_ifs with hr
    · simpa using hrow r hr
    · simp
  have hi := row_incidences_add_corners_le row col
  omega

end ShellObservability.RectangleBounds
