module

public import ShellObservability.HypercubeBasic
public import ShellObservability.Robust

@[expose] public section

/-! Actual hypercube shortest-path distance and odd equidistant witnesses. -/

namespace ShellObservability.Hypercube

/-- Changing one coordinate changes its Hamming contribution and no other. -/
theorem hamming_update_balance {n : ℕ} (x y : Cube n) (i : Fin n) (b : Bool) :
    hammingDist (Function.update x i b) y + (if x i ≠ y i then 1 else 0) =
      hammingDist x y + (if b ≠ y i then 1 else 0) := by
  classical
  have heq : (fun j => if Function.update x i b j ≠ y j then 1 else 0) =
      Function.update (fun j => if x j ≠ y j then 1 else 0) i
        (if b ≠ y i then 1 else 0) := by
    funext j
    by_cases hj : j = i
    · subst j; simp
    · simp [hj]
  rw [hamming_eq_sum, hamming_eq_sum, heq]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase]
  have hf := Finset.sum_erase_add Finset.univ
    (fun j => if x j ≠ y j then (1 : ℕ) else 0) (Finset.mem_univ i)
  omega

/-- Flipping one Boolean coordinate changes exactly one Hamming entry. -/
theorem hamming_flip_one {n : ℕ} (x : Cube n) (i : Fin n) :
    hammingDist x (Function.update x i (!x i)) = 1 := by
  have h := hamming_update_balance x x i (!x i)
  rw [hammingDist_comm]
  cases hx : x i <;> simpa [hx] using h

/-- The hypercube as an actual simple graph with unit Hamming edges. -/
def cubeGraph (n : ℕ) : SimpleGraph (Cube n) :=
  SimpleGraph.fromRel (fun x y => hammingDist x y = 1)

theorem cubeGraph_adj {n : ℕ} (x y : Cube n) :
    (cubeGraph n).Adj x y ↔ hammingDist x y = 1 := by
  simp only [cubeGraph, SimpleGraph.fromRel_adj, hammingDist_comm y x, or_self]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    intro he
    subst y
    simp at h

/-- Every hypercube walk is at least as long as its Hamming displacement. -/
theorem hamming_le_walk_length {n : ℕ} {x y : Cube n} (w : (cubeGraph n).Walk x y) :
    hammingDist x y ≤ w.length := by
  induction w with
  | nil => simp
  | @cons a b c hab w ih =>
    have hstep := (cubeGraph_adj a b).mp hab
    have htri := hammingDist_triangle a b c
    simp only [SimpleGraph.Walk.length_cons]
    omega

/-- Correcting one differing coordinate is an edge and decreases the remaining
distance by exactly one. -/
theorem cube_step_toward {n : ℕ} (x y : Cube n) (hne : x ≠ y) :
    ∃ x', (cubeGraph n).Adj x x' ∧ hammingDist x' y + 1 = hammingDist x y := by
  classical
  obtain ⟨i,hi⟩ : ∃ i, x i ≠ y i := by simpa only [ne_eq, funext_iff, not_forall] using hne
  let x' := Function.update x i (y i)
  have hmove := hamming_update_balance x x i (y i)
  have hdecrease := hamming_update_balance x y i (y i)
  refine ⟨x', (cubeGraph_adj x x').mpr ?_, ?_⟩
  · rw [hammingDist_comm]
    simpa [x',hi,Ne.symm hi] using hmove
  · simpa [x',hi] using hdecrease

/-- A geodesic is obtained by correcting the differing coordinates one by one. -/
theorem exists_cube_geodesic {n : ℕ} (x y : Cube n) :
    ∃ w : (cubeGraph n).Walk x y, w.length = hammingDist x y := by
  generalize he : hammingDist x y = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases hxy : x = y
    · subst x
      exact ⟨.nil, by simpa using he⟩
    · obtain ⟨x',hadj,hstep⟩ := cube_step_toward x y hxy
      obtain ⟨w,hw⟩ := ih (hammingDist x' y) (by omega) x' rfl
      exact ⟨.cons hadj w, by simp [hw]; omega⟩

/-- Actual graph shortest-path distance equals Hamming distance. -/
theorem cube_dist_eq_hamming {n : ℕ} (x y : Cube n) :
    (cubeGraph n).dist x y = hammingDist x y := by
  obtain ⟨p,hp⟩ := exists_cube_geodesic x y
  apply le_antisymm
  · exact hp ▸ SimpleGraph.dist_le p
  · have hr : (cubeGraph n).Reachable x y := ⟨p⟩
    obtain ⟨w,hw⟩ := hr.exists_walk_length_eq_dist
    rw [← hw]
    exact hamming_le_walk_length w

/-- Boolean hypercubes are connected, including the zero-dimensional case. -/
theorem cube_connected (n : ℕ) : (cubeGraph n).Connected := by
  constructor
  intro x y
  obtain ⟨w,_⟩ := exists_cube_geodesic x y
  exact ⟨w⟩

/-- Even Hamming distance admits an equidistant midpoint. -/
theorem exists_hamming_midpoint {n : ℕ} (x y : Cube n)
    (heven : hammingDist x y % 2 = 0) :
    ∃ z : Cube n, hammingDist z x = hammingDist z y := by
  have hd : hammingDist x y = 2 * (hammingDist x y / 2) := by omega
  obtain ⟨z,hx,hy⟩ := ShellObservability.exists_common_received x y
    (hammingDist x y / 2) (by omega)
  have htri := hammingDist_triangle_right x y z
  refine ⟨z,?_⟩
  rw [hammingDist_comm z x, hammingDist_comm z y]
  omega

/-- For two even-weight words with a common coordinate, an odd-weight word
bisects them. A shared coordinate allows parity to be toggled without changing
the equality of distances. -/
theorem exists_odd_hamming_bisector {n : ℕ} (x y : Cube n)
    (hx : weight x % 2 = 0) (hy : weight y % 2 = 0)
    (hcommon : ∃ i, x i = y i) :
    ∃ z : Cube n, weight z % 2 = 1 ∧ hammingDist z x = hammingDist z y := by
  have heven : hammingDist x y % 2 = 0 := by
    rw [hamming_weight_parity]
    omega
  obtain ⟨z,hz⟩ := exists_hamming_midpoint x y heven
  by_cases hodd : weight z % 2 = 1
  · exact ⟨z,hodd,hz⟩
  · obtain ⟨i,hi⟩ := hcommon
    let z' := Function.update z i (!z i)
    have hzx := hamming_update_balance z x i (!z i)
    have hzy := hamming_update_balance z y i (!z i)
    rw [hi] at hzx
    have heq : hammingDist z' x = hammingDist z' y := by
      dsimp [z']
      omega
    have hflip := hamming_flip_one z i
    have hp := hamming_weight_parity z z'
    have hnewodd : weight z' % 2 = 1 := by
      dsimp [z']
      dsimp [z'] at hp
      rw [hflip] at hp
      omega
    exact ⟨z',hnewodd,heq⟩

/-- Graph-distance form of the odd-bisector theorem. -/
theorem exists_odd_graph_bisector {n : ℕ} (x y : Cube n)
    (hx : weight x % 2 = 0) (hy : weight y % 2 = 0)
    (hcommon : ∃ i, x i = y i) :
    ∃ z : Cube n, weight z % 2 = 1 ∧ (cubeGraph n).dist z x = (cubeGraph n).dist z y := by
  simpa only [cube_dist_eq_hamming] using exists_odd_hamming_bisector x y hx hy hcommon

end ShellObservability.Hypercube

namespace ShellObservability.Hypercube

/-- Complementary words partition the coordinates in every distance sum. -/
theorem hamming_antipodal_sum {n : ℕ} (x y z : Cube n)
    (hantipodal : ∀ i, x i ≠ y i) :
    hammingDist z x + hammingDist z y = n := by
  rw [hamming_eq_sum, hamming_eq_sum, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _i : Fin n, 1 := by
      apply Finset.sum_congr rfl
      intro i _
      have hi := hantipodal i
      cases hx : x i <;> cases hy : y i <;> cases hz : z i <;> simp_all
    _ = _ := by simp

/-- Flip a chosen coordinate. -/
def flipCoordinate {n : ℕ} (i : Fin n) (x : Cube n) : Cube n :=
  Function.update x i (!x i)

theorem flipCoordinate_involutive {n : ℕ} (i : Fin n) :
    Function.Involutive (flipCoordinate i) := by
  intro x
  funext j
  by_cases hj : j = i
  · subst j
    simp [flipCoordinate]
  · simp [flipCoordinate,hj]

/-- A coordinate flip switches the weight parity. -/
theorem weight_flip_parity {n : ℕ} (x : Cube n) (i : Fin n) :
    weight x % 2 + weight (flipCoordinate i x) % 2 = 1 := by
  have hp := hamming_weight_parity x (flipCoordinate i x)
  have hd : hammingDist x (flipCoordinate i x) = 1 := hamming_flip_one x i
  rw [hd] at hp
  omega

/-- The odd-weight words, a canonical half-cube sensor family. -/
def oddWords (n : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => weight x % 2 = 1)

/-- The even-weight words. -/
def evenWords (n : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => weight x % 2 = 0)

@[simp] theorem mem_oddWords {n : ℕ} (x : Cube n) :
    x ∈ oddWords n ↔ weight x % 2 = 1 := by simp [oddWords]

@[simp] theorem mem_evenWords {n : ℕ} (x : Cube n) :
    x ∈ evenWords n ↔ weight x % 2 = 0 := by simp [evenWords]

/-- Flipping one fixed coordinate bijects the two parity classes. -/
theorem card_evenWords_eq_oddWords {n : ℕ} (i : Fin n) :
    (evenWords n).card = (oddWords n).card := by
  apply Finset.card_bij (fun x _ => flipCoordinate i x)
  · intro x hx
    rw [mem_evenWords] at hx
    rw [mem_oddWords]
    have hp := weight_flip_parity x i
    omega
  · intro x hx y hy hxy
    exact (flipCoordinate_involutive i).injective hxy
  · intro y hy
    refine ⟨flipCoordinate i y, ?_, (flipCoordinate_involutive i) y⟩
    rw [mem_oddWords] at hy
    rw [mem_evenWords]
    have hp := weight_flip_parity y i
    omega

/-- An `(n+1)`-dimensional cube has exactly `2^n` odd-weight vertices. -/
theorem card_oddWords_succ (n : ℕ) : (oddWords (n+1)).card = 2^n := by
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ) (fun x : Cube (n+1) => weight x % 2 = 0)
  have hnot : (Finset.univ.filter (fun x : Cube (n+1) => ¬ weight x % 2 = 0)) =
      oddWords (n+1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_oddWords]
    omega
  rw [hnot] at hpartition
  change (evenWords (n+1)).card + (oddWords (n+1)).card = Fintype.card (Cube (n+1))
    at hpartition
  have heq := card_evenWords_eq_oddWords (⟨0,by omega⟩ : Fin (n+1))
  simp only [Cube, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, pow_succ]
    at hpartition
  omega

/-- Positive-dimensional half-cube cardinality. -/
theorem card_oddWords (n : ℕ) (hn : 0 < n) : (oddWords n).card = 2^(n-1) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simpa using card_oddWords_succ k

end ShellObservability.Hypercube
