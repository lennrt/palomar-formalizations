module
public import Expansion
public import ShellObservability.GridTheorems
public import ShellObservability.GridMomentRecovery
public import ShellObservability.HypercubeReduction
public import ShellObservability.BishopUpper
public import ShellObservability.PetersenCounterexample
public import ShellObservability.PetersenSecond
public import ShellObservability.FractionalCounterexample
public import ShellObservability.DefectSyndrome

/-! Proved counterparts of the independent Challenge declarations.
This file deliberately does not import Challenge. -/
@[expose] public section

namespace PalomarResults.Grid
open ShellObservability
open ShellTomography

theorem gridRobust_iff_intervalCuts (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridRobust m S hb ↔ GridIntervalCuts m S := by
  exact ShellObservability.gridRobust_iff_intervalCuts m S hb hcorners

theorem gridMomentRobust_iff_gridRobust (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridMomentRobust m S hb ↔ GridRobust m S hb := by
  exact ShellObservability.gridMomentRobust_iff_gridRobust m S hb hcorners

theorem grid_robust_sensor_lower_bound (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hm : 0 < m) (hr : GridRobust m S hb) :
    3*m < 2*S.card := by
  exact ShellObservability.GridTheorems.grid_robust_sensor_lower_bound m S hb hm hr

theorem exact_corner_grid_robust_minimum (q : ℕ) (hq : 0 < q) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds (4*q) S),
      S.card = 6*q+5 ∧ GridHasCorners (4*q) S ∧ GridRobust (4*q) S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds (4*q) S),
      GridHasCorners (4*q) S → GridRobust (4*q) S hb → 6*q+5 ≤ S.card) := by
  exact ShellObservability.GridTheorems.exact_corner_grid_robust_minimum q hq

theorem exists_grid_robust_placement (m : ℕ) (hm : 4 ≤ m) :
    ∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      S.card ≤ 6*(m/4)+5+4*(m%4) ∧ GridHasCorners m S ∧ GridRobust m S hb := by
  exact ShellObservability.GridTheorems.exists_grid_robust_placement m hm

theorem all_orders_grid_robust_bounds (m : ℕ) (hm : 4 ≤ m) :
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      GridRobust m S hb → 3*m < 2*S.card) ∧
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      2*S.card ≤ 3*m+25 ∧ GridHasCorners m S ∧ GridRobust m S hb) := by
  exact ShellObservability.GridTheorems.all_orders_grid_robust_bounds m hm

theorem exact_corner_grid_robust_minimum_all (m : ℕ) (hm : 0 < m) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      S.card = (3*m+10)/2 ∧ GridHasCorners m S ∧ GridRobust m S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      GridHasCorners m S → GridRobust m S hb → (3*m+10)/2 ≤ S.card) := by
  exact ShellObservability.GridTheorems.exact_corner_grid_robust_minimum_all m hm

end PalomarResults.Grid

namespace PalomarResults.Hypercube
open ShellObservability.Hypercube

theorem prefixEqualizer_isDistanceEqualizer (q : ℕ) (hq : 0 < q) :
    IsDistanceEqualizer (prefixEqualizer q) := by
  exact ShellObservability.Hypercube.prefixEqualizer_isDistanceEqualizer q hq

theorem prefixEqualizer_card (q : ℕ) (hq : 0 < q) :
    (prefixEqualizer q).card = 2^(4*q-1) + 2*q := by
  exact ShellObservability.Hypercube.prefixEqualizer_card q hq

theorem infinite_counterexample_family (q : ℕ) (hq : 3 ≤ q) :
    ∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧
      S.card < 2^(4*q-1) + 2^((4*q)/2-2) := by
  exact ShellObservability.Hypercube.infinite_counterexample_family q hq

theorem dimension_twelve_counterexample :
    ∃ S : Finset (Cube 12), IsDistanceEqualizer S ∧ S.card = 2054 ∧
      S.card < 2^(12-1) + 2^(12/2-2) := by
  exact ShellObservability.Hypercube.dimension_twelve_counterexample

theorem equalizer_contains_parity_class {n : ℕ} (S : Finset (Cube n))
    (hS : IsDistanceEqualizer S) :
    (∀ x, weight x % 2 = 1 → x ∈ S) ∨ (∀ x, weight x % 2 = 0 → x ∈ S) := by
  exact ShellObservability.Hypercube.equalizer_contains_parity_class S hS

theorem odd_union_equalizer_iff_antipodal_cover (q : ℕ) (hq : 0 < q)
    (T : Finset (Cube (4*q))) :
    IsDistanceEqualizer (oddWords (4*q) ∪ T) ↔
      ∀ x, weight x % 2 = 0 →
        x ∈ T ∨ antipode x ∈ T ∨ ∃ z ∈ T, hammingDist z x = 2*q := by
  exact ShellObservability.Hypercube.odd_union_equalizer_iff_antipodal_cover q hq T

theorem evenPrefix_distance {n i j : ℕ} (hi : 2*i ≤ n) (hj : 2*j ≤ n) :
    hammingDist (evenPrefix n i) (evenPrefix n j) = 2*Nat.dist i j := by
  exact ShellObservability.Hypercube.evenPrefix_distance hi hj

theorem evenPrefix_orthogonal_iff (q i j : ℕ) (hi : i < 2*q) (hj : j < 2*q) :
    hammingDist (evenPrefix (4*q) i) (evenPrefix (4*q) j) = 2*q ↔
      i+q=j ∨ j+q=i := by
  exact ShellObservability.Hypercube.evenPrefix_orthogonal_iff q i j hi hj

theorem evenPrefix_unique_orthogonal_partner (q i : ℕ) (hi : i < 2*q) :
    ∃! j, j < 2*q ∧ hammingDist (evenPrefix (4*q) i) (evenPrefix (4*q) j) = 2*q := by
  exact ShellObservability.Hypercube.evenPrefix_unique_orthogonal_partner q i hi

theorem equalizer_card_lower_bound (q : ℕ) (hq : 0 < q) (S : Finset (Cube (4*q)))
    (hS : IsDistanceEqualizer S) : 2^(4*q-1) + 2*q - 1 ≤ S.card := by
  exact ShellObservability.Hypercube.equalizer_card_lower_bound q hq S hS

theorem equidistant_dimension_within_one (q : ℕ) (hq : 0 < q) :
    (∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧ S.card = 2^(4*q-1) + 2*q) ∧
    (∀ S : Finset (Cube (4*q)), IsDistanceEqualizer S → 2^(4*q-1) + 2*q - 1 ≤ S.card) := by
  exact ShellObservability.Hypercube.equidistant_dimension_within_one q hq

end PalomarResults.Hypercube

namespace PalomarResults.Bishop
open ShellObservability.BishopParity

theorem exact_two_domination {N : ℕ} (hN : N % 2 = 1) :
    (∃ S : Finset (Square N), TwoDominates S ∧ S.card = 2*(N+1)) ∧
    (∀ S : Finset (Square N), TwoDominates S → 2*(N+1) ≤ S.card) := by
  exact ShellObservability.BishopParity.exact_two_domination hN

end PalomarResults.Bishop

namespace PalomarResults.Petersen11
open ShellObservability.Petersen

theorem exact_domination :
    (∃ S : Finset V, S.card = 16 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 16 ≤ S.card) := by
  exact ShellObservability.Petersen.exact_domination

end PalomarResults.Petersen11

namespace PalomarResults.Petersen16
open ShellObservability.PetersenSecond

theorem exact_domination :
    (∃ S : Finset V, S.card = 24 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 24 ≤ S.card) := by
  exact ShellObservability.PetersenSecond.exact_domination

end PalomarResults.Petersen16

namespace PalomarResults.Fractional
open ShellObservability.FractionalCounterexample

theorem graph_connected : graph.Connected := by
  exact ShellObservability.FractionalCounterexample.graph_connected

theorem counterexample : ClassI ∧ ¬ ∃ v, DominationNull v ∧ PackingNull v := by
  exact ShellObservability.FractionalCounterexample.counterexample

end PalomarResults.Fractional

namespace PalomarResults.Syndrome
open ShellObservability
variable {L R C K : Type*} [Fintype R] [Fintype C]
variable [DecidableEq R] [DecidableEq C] [Semiring K]
variable (incidence : R → C → Prop) [DecidableRel incidence]

theorem syndrome_packing_bound (W : Matrix L R K) (selected : Finset C) (k ell : ℕ)
    (hregular : ∀ c ∈ selected, (Finset.univ.filter (fun r => incidence r c)).card = k)
    (hWA : W * incidenceMatrix (K := K) incidence = 0)
    (hpacking : IsIncidencePacking incidence selected)
    (hexclude : ∀ D : Finset R, D.card < ell → supportSyndrome W D ≠ W.mulVec 1) :
    k * selected.card + ell ≤ Fintype.card R := by
  exact ShellObservability.syndrome_packing_bound incidence W selected k ell hregular hWA hpacking hexclude

end PalomarResults.Syndrome

-- Add this import to the module header:
-- public import ShellObservability.CubeTriple

namespace PalomarResults.Hypercube
open ShellObservability.Hypercube

theorem three_even_words_common_middle_graph (q : ℕ) (a b c : Cube (4*q))
    (ha : weight a % 2 = 0) (hb : weight b % 2 = 0) (hc : weight c % 2 = 0) :
    ∃ z : Cube (4*q), weight z % 2 = 0 ∧
      (cubeGraph (4*q)).dist z a = 2*q ∧
      (cubeGraph (4*q)).dist z b = 2*q ∧
      (cubeGraph (4*q)).dist z c = 2*q := by
  exact ShellObservability.Hypercube.three_even_words_common_middle_graph q a b c ha hb hc

theorem four_word_no_common_graph_distance {n : ℕ} (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ ∃ x : Cube n,
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord i j) ∧
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord i k) ∧
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord j k) := by
  exact ShellObservability.Hypercube.four_word_no_common_graph_distance i j k hij hik hjk

end PalomarResults.Hypercube


namespace PalomarResults.Rectangle
open ShellObservability.Rectangle
theorem gridRobust_iff_intervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hcorners : GridHasCorners M N S) :
    GridRobust M N S hb ↔ GridIntervalCuts M N S := ShellObservability.Rectangle.gridRobust_iff_intervalCuts M N S hb hcorners

theorem exact_long_rectangle_robust_minimum (M N : ℕ)
    (hsize : N ≤ M) (hratio : 5*N ≤ 3*M) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      S.card = 2*N+4 ∧ GridHasCorners M N S ∧ GridRobust M N S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      GridHasCorners M N S → GridRobust M N S hb → 2*N+4 ≤ S.card) := ShellObservability.Rectangle.exact_long_rectangle_robust_minimum M N hsize hratio
end PalomarResults.Rectangle

namespace PalomarResults.AdditiveFields
open ShellObservability.AdditiveFields
variable {R C A : Type*} [Fintype R] [Fintype C] [AddCommGroup A] [DecidableEq A]
variable [Nonempty R] [Nonempty C] [Nontrivial A]
theorem recovers_iff_connected (seen : Set (R × C)) :
    Recovers (A := A) seen ↔ (observationGraph seen).Connected := ShellObservability.AdditiveFields.recovers_iff_connected seen

theorem tolerates_erasures_iff (e : ℕ) :
    ShellObservability.ToleratesErasures (fun f : R × C → A => f) IsAdditive e ↔
      e < min (Fintype.card R) (Fintype.card C) := ShellObservability.AdditiveFields.tolerates_erasures_iff e
end PalomarResults.AdditiveFields

-- Add public imports of ShellObservability.TensorMoments and ShellObservability.BooleanSampling above the public section.
namespace PalomarResults.Moments
open ShellObservability.TensorMoments
variable {A B : Type*} [Fintype A] [Fintype B]

theorem tensor_detector (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) :
    profile (fun p : A × B => da p.1 + db p.2) (tensor a b) ≠ 0 ↔
      profile da a ≠ 0 ∧ profile db b ≠ 0 := by
  exact profile_tensor_ne_zero_iff da db a b

theorem first_surviving_moment (da : A → ℕ) (db : B → ℕ)
    (a : A → ℤ) (b : B → ℤ) (p q : ℕ)
    (ha : ∀ i < p, moment da a i = 0)
    (hb : ∀ i < q, moment db b i = 0)
    (hap : moment da a p ≠ 0) (hbq : moment db b q ≠ 0) :
    (∀ k < p + q,
      moment (fun v : A × B => da v.1 + db v.2) (tensor a b) k = 0) ∧
    moment (fun v : A × B => da v.1 + db v.2) (tensor a b) (p + q) =
      ((p + q).choose p : ℤ) * moment da a p * moment db b q ∧
    moment (fun v : A × B => da v.1 + db v.2) (tensor a b) (p + q) ≠ 0 := by
  exact ⟨fun k hk => moment_tensor_eq_zero_of_lt da db a b p q k ha hb hk,
    moment_tensor_leading da db a b p q ha hb,
    moment_tensor_leading_ne_zero da db a b p q ha hb hap hbq⟩

end PalomarResults.Moments

namespace PalomarResults.BooleanSampling
open ShellObservability.BooleanSampling
variable {ι : Type*} [DecidableEq ι]

theorem lower_ball_sampling (a b : Finset ι → ℚ) (k : ℕ)
    (ha : DegreeAtMost a k) (hb : DegreeAtMost b k)
    (hball : ∀ s, s.card ≤ k → evaluate a s = evaluate b s) : a = b := by
  exact coefficients_eq_of_lower_ball a b k ha hb hball

end PalomarResults.BooleanSampling
