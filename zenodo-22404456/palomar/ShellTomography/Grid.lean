import ShellTomography.Product
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The square-grid SimpleGraph and its shortest-path/Manhattan-distance bridge. -/

namespace ShellTomography

abbrev Grid (n : ℕ) := Fin n × Fin n

/-- Natural absolute difference. -/
def natAbsDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

@[simp] theorem natAbsDiff_self (a : ℕ) : natAbsDiff a a = 0 := by simp [natAbsDiff]

theorem natAbsDiff_eq_zero_iff (a b : ℕ) : natAbsDiff a b = 0 ↔ a = b := by
  unfold natAbsDiff
  omega

theorem natAbsDiff_symm (a b : ℕ) : natAbsDiff a b = natAbsDiff b a := by
  unfold natAbsDiff
  omega

theorem natAbsDiff_triangle (a b c : ℕ) : natAbsDiff a c ≤ natAbsDiff a b + natAbsDiff b c := by
  unfold natAbsDiff
  omega

/-- Manhattan metric on the finite grid. -/
def manhattan {n : ℕ} (x y : Grid n) : ℕ :=
  natAbsDiff x.1.val y.1.val + natAbsDiff x.2.val y.2.val

@[simp] theorem manhattan_self {n} (x : Grid n) : manhattan x x = 0 := by simp [manhattan]

theorem manhattan_eq_zero_iff {n} (x y : Grid n) : manhattan x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h1 : x.1.val = y.1.val := by
      have := Nat.eq_zero_of_add_eq_zero_right h
      exact (natAbsDiff_eq_zero_iff _ _).mp this
    have h2 : x.2.val = y.2.val := by
      have := Nat.eq_zero_of_add_eq_zero_left h
      exact (natAbsDiff_eq_zero_iff _ _).mp this
    apply Prod.ext <;> apply Fin.ext <;> assumption
  · rintro rfl
    simp

theorem manhattan_symm {n} (x y : Grid n) : manhattan x y = manhattan y x := by
  simp [manhattan, natAbsDiff_symm]

theorem manhattan_triangle {n} (x y z : Grid n) :
    manhattan x z ≤ manhattan x y + manhattan y z := by
  unfold manhattan
  have h1 := natAbsDiff_triangle x.1.val y.1.val z.1.val
  have h2 := natAbsDiff_triangle x.2.val y.2.val z.2.val
  omega

/-- The actual simple graph whose edges are unit Manhattan moves. -/
def gridGraph (n : ℕ) : SimpleGraph (Grid n) :=
  SimpleGraph.fromRel fun x y => manhattan x y = 1

theorem gridGraph_adj {n} {x y : Grid n} :
    (gridGraph n).Adj x y ↔ manhattan x y = 1 := by
  simp only [gridGraph, SimpleGraph.fromRel_adj, manhattan_symm y x, or_self]
  constructor
  · exact And.right
  · intro h
    exact ⟨by intro he; subst y; simp at h, h⟩

/-- Every grid walk has length at least the Manhattan displacement. -/
theorem manhattan_le_walk_length {n} {x y : Grid n} (w : (gridGraph n).Walk x y) :
    manhattan x y ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hxy w ih =>
      have hstep : manhattan _ _ = 1 := gridGraph_adj.mp hxy
      have htri := manhattan_triangle a b c
      have ht : manhattan a c ≤ 1 + w.length := by
        rw [hstep] at htri
        exact htri.trans (Nat.add_le_add_left ih 1)
      simpa [SimpleGraph.Walk.length_cons, Nat.add_comm] using ht

/-- A coordinate move reduces Manhattan distance by exactly one. -/
theorem grid_step_toward {n : ℕ} (x y : Grid n) (hne : x ≠ y) :
    ∃ x' : Grid n, (gridGraph n).Adj x x' ∧ manhattan x' y + 1 = manhattan x y := by
  rcases x with ⟨⟨a,ha⟩,⟨b,hb⟩⟩
  rcases y with ⟨⟨c,hc⟩,⟨d,hd⟩⟩
  by_cases hac : a = c
  · have hbd : b ≠ d := by
      intro h; apply hne; simp_all
    by_cases hlt : b < d
    · refine ⟨(⟨a,ha⟩,⟨b+1,by omega⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
    · refine ⟨(⟨a,ha⟩,⟨b-1,by omega⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
  · by_cases hlt : a < c
    · refine ⟨(⟨a+1,by omega⟩,⟨b,hb⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega
    · refine ⟨(⟨a-1,by omega⟩,⟨b,hb⟩), ?_, ?_⟩
      · rw [gridGraph_adj]; dsimp [manhattan, natAbsDiff]; omega
      · dsimp [manhattan, natAbsDiff]; omega

/-- There is a shortest coordinate walk of the Manhattan length. -/
theorem exists_grid_geodesic {n : ℕ} (x y : Grid n) :
    ∃ w : (gridGraph n).Walk x y, w.length = manhattan x y := by
  generalize he : manhattan x y = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hxy : x = y
    · subst x
      exact ⟨.nil, by simpa using he⟩
    · obtain ⟨x',hadj,hstep⟩ := grid_step_toward x y hxy
      obtain ⟨w,hw⟩ := ih (manhattan x' y) (by omega) x' rfl
      exact ⟨.cons hadj w, by simp [hw]; omega⟩

/-- Graph shortest-path distance, not an assumed distance table, equals Manhattan distance. -/
theorem grid_dist_eq_manhattan {n : ℕ} (x y : Grid n) :
    (gridGraph n).dist x y = manhattan x y := by
  obtain ⟨p,hp⟩ := exists_grid_geodesic x y
  apply le_antisymm
  · exact hp ▸ SimpleGraph.dist_le p
  · have hr : (gridGraph n).Reachable x y := ⟨p⟩
    obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
    rw [← hw]
    exact manhattan_le_walk_length w

/-- The actual grid graph is connected. -/
theorem grid_connected {n : ℕ} [NeZero n] : (gridGraph n).Connected := by
  constructor
  intro x y
  obtain ⟨w,_⟩ := exists_grid_geodesic x y
  exact ⟨w⟩

/-- Sensor-distance table for the actual graph, expressed through the proved bridge. -/
def gridDistance (n : ℕ) : Grid n → Grid n → ℕ := fun x y => manhattan x y

/-- MetricLike property required by product lifting. -/
theorem gridDistance_metricLike (n : ℕ) : MetricLike (gridDistance n) := by
  intro x y
  exact manhattan_eq_zero_iff x y

end ShellTomography
