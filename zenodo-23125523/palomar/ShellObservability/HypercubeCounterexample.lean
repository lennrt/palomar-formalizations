module

public import ShellObservability.HypercubeGeometry
public import ShellObservability.HypercubePrefixes

@[expose] public section

/-! An explicit distance equalizer refuting the hypercube conjecture of
Gispert-Fernández, Rodríguez-Velázquez, and Yero (2026), Conjecture 1.
All distances below are shortest-path distances in the actual hypercube graph. -/

namespace ShellObservability.Hypercube

/-- A distance equalizer supplies an equidistant selected vertex for every
pair of distinct unselected vertices. -/
def IsDistanceEqualizer {n : ℕ} (S : Finset (Cube n)) : Prop :=
  ∀ x, x ∉ S → ∀ y, y ∉ S → x ≠ y →
    ∃ z ∈ S, (cubeGraph n).dist z x = (cubeGraph n).dist z y

/-- One parity class together with the linearly sized prefix balancing family. -/
def prefixEqualizer (q : ℕ) : Finset (Cube (4*q)) := oddWords (4*q) ∪ prefixSet q

theorem prefixEqualizer_isDistanceEqualizer (q : ℕ) (hq : 0 < q) :
    IsDistanceEqualizer (prefixEqualizer q) := by
  classical
  intro x hx y hy _
  have hxodd : weight x % 2 ≠ 1 := by
    intro hx'
    apply hx
    exact Finset.mem_union_left _ (by simpa [oddWords] using hx')
  have hyodd : weight y % 2 ≠ 1 := by
    intro hy'
    apply hy
    exact Finset.mem_union_left _ (by simpa [oddWords] using hy')
  have hxeven : weight x % 2 = 0 := by omega
  have hyeven : weight y % 2 = 0 := by omega
  by_cases hcommon : ∃ i, x i = y i
  · obtain ⟨z,hz,heq⟩ := exists_odd_graph_bisector x y hxeven hyeven hcommon
    exact ⟨z, Finset.mem_union_left _ (by simpa [oddWords] using hz), heq⟩
  · have hanti : ∀ i, x i ≠ y i := by simpa only [not_exists] using hcommon
    obtain ⟨z,hz,hbal⟩ := prefixSet_balances q hq x hxeven
    have hsum := hamming_antipodal_sum x y z hanti
    refine ⟨z, Finset.mem_union_right _ hz, ?_⟩
    rw [cube_dist_eq_hamming, cube_dist_eq_hamming]
    rw [hammingDist_comm x z] at hbal
    omega

theorem prefixEqualizer_card (q : ℕ) (hq : 0 < q) :
    (prefixEqualizer q).card = 2^(4*q-1) + 2*q := by
  classical
  have hd : Disjoint (oddWords (4*q)) (prefixSet q) := by
    rw [Finset.disjoint_left]
    intro z hz hp
    have ho : weight z % 2 = 1 := by simpa [oddWords] using hz
    have he := prefixSet_even hp
    omega
  rw [prefixEqualizer, Finset.card_union_of_disjoint hd, card_oddWords (4*q) (by omega),
    prefixSet_card]

lemma linear_excess_lt_conjectured (q : ℕ) (hq : 3 ≤ q) :
    2*q < 2^(2*q-2) := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have he : 2*(q+1)-2 = (2*q-2)+2 := by omega
    rw [he, pow_add]
    norm_num
    omega

/-- Every dimension divisible by four and at least twelve contradicts the
conjectured exponential correction. -/
theorem infinite_counterexample_family (q : ℕ) (hq : 3 ≤ q) :
    ∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧
      S.card < 2^(4*q-1) + 2^((4*q)/2-2) := by
  refine ⟨prefixEqualizer q, prefixEqualizer_isDistanceEqualizer q (by omega), ?_⟩
  rw [prefixEqualizer_card q (by omega)]
  have he : (4*q)/2 = 2*q := by omega
  rw [he]
  exact Nat.add_lt_add_left (linear_excess_lt_conjectured q hq) _

/-- A fully explicit counterexample: the conjectured value at dimension twelve
is 2064, whereas this distance equalizer has only 2054 vertices. -/
theorem dimension_twelve_counterexample :
    ∃ S : Finset (Cube 12), IsDistanceEqualizer S ∧ S.card = 2054 ∧
      S.card < 2^(12-1) + 2^(12/2-2) := by
  refine ⟨prefixEqualizer 3, prefixEqualizer_isDistanceEqualizer 3 (by norm_num), ?_⟩
  have hc := prefixEqualizer_card 3 (by norm_num)
  norm_num at hc ⊢
  omega

end ShellObservability.Hypercube
