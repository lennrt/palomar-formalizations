module
public import ShellObservability.CubeExpansion

/-! Common middle neighbors of three even cube words. -/
@[expose] public section
namespace ShellObservability.Hypercube
open Finset

private lemma support_weight {n : ℕ} (Z : Finset (Fin n)) :
    weight (fun i => decide (i ∈ Z)) = Z.card := by
  simp [weight]

private lemma support_meet {n : ℕ} (Z : Finset (Fin n)) (a : Cube n) :
    (∑ i, if (decide (i ∈ Z)) && a i then 1 else 0) =
      (Z.filter (fun i => a i = true)).card := by
  have he (i : Fin n) : (if (decide (i ∈ Z)) && a i then 1 else 0) =
      (if i ∈ Z.filter (fun i => a i = true) then (1 : ℕ) else 0) := by
    by_cases hi : i ∈ Z <;> cases ha : a i <;> simp [hi,ha]
  simp_rw [he]
  simp only [sum_boole]
  apply congrArg Finset.card
  ext i
  simp

/-- Simultaneously halve two even subsets while selecting exactly half of an
ambient set of size divisible by four. -/
theorem two_even_words_have_balanced_selector (q : ℕ) (a b : Cube (4*q))
    (ha : weight a % 2 = 0) (hb : weight b % 2 = 0) :
    ∃ z : Cube (4*q), weight z = 2*q ∧
      hammingDist z a = 2*q ∧ hammingDist z b = 2*q := by
  classical
  let A := univ.filter (fun i => a i = false ∧ b i = false)
  let B := univ.filter (fun i => a i = false ∧ b i = true)
  let C := univ.filter (fun i => a i = true ∧ b i = false)
  let D := univ.filter (fun i => a i = true ∧ b i = true)
  have hn : A.card + B.card + C.card + D.card = 4*q := by
    simp only [A,B,C,D,Finset.card_filter]
    rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
    calc
      _ = ∑ _i : Fin (4*q), 1 := by
        apply sum_congr rfl
        intro i _
        cases a i <;> cases b i <;> simp
      _ = _ := by simp
  have hwa : weight a = C.card + D.card := by
    simp only [weight,C,D,Finset.card_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases a i <;> cases b i <;> simp
  have hwb : weight b = B.card + D.card := by
    simp only [weight,B,D,Finset.card_filter,← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases a i <;> cases b i <;> simp
  have hp : A.card % 2 = D.card % 2 ∧ B.card % 2 = D.card % 2 ∧
      C.card % 2 = D.card % 2 := by omega
  obtain ⟨A',hA',hcA⟩ := exists_subset_card_eq (s := A)
    (show (A.card + A.card%2)/2 ≤ A.card by omega)
  obtain ⟨B',hB',hcB⟩ := exists_subset_card_eq (s := B) (Nat.div_le_self B.card 2)
  obtain ⟨C',hC',hcC⟩ := exists_subset_card_eq (s := C) (Nat.div_le_self C.card 2)
  obtain ⟨D',hD',hcD⟩ := exists_subset_card_eq (s := D)
    (show (D.card + D.card%2)/2 ≤ D.card by omega)
  have hAB : Disjoint A' B' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hA' hi)).2
    have := (mem_filter.mp (hB' hj)).2
    simp_all
  have hAC : Disjoint A' C' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hA' hi)).2
    have := (mem_filter.mp (hC' hj)).2
    simp_all
  have hAD : Disjoint A' D' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hA' hi)).2
    have := (mem_filter.mp (hD' hj)).2
    simp_all
  have hBC : Disjoint B' C' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hB' hi)).2
    have := (mem_filter.mp (hC' hj)).2
    simp_all
  have hBD : Disjoint B' D' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hB' hi)).2
    have := (mem_filter.mp (hD' hj)).2
    simp_all
  have hCD : Disjoint C' D' := by
    apply disjoint_left.mpr
    intro i hi hj
    have := (mem_filter.mp (hC' hi)).2
    have := (mem_filter.mp (hD' hj)).2
    simp_all
  let Z := A' ∪ B' ∪ C' ∪ D'
  have hcZ : Z.card = A'.card + B'.card + C'.card + D'.card := by
    simp only [Z, card_union_of_disjoint (disjoint_union_left.mpr
      ⟨disjoint_union_left.mpr ⟨hAD,hBD⟩,hCD⟩),
      card_union_of_disjoint (disjoint_union_left.mpr ⟨hAC,hBC⟩),
      card_union_of_disjoint hAB]
  have hZa : Z.filter (fun i => a i = true) = C' ∪ D' := by
    ext i
    simp only [Z,mem_filter,mem_union]
    have hA (hi : i ∈ A') := (mem_filter.mp (hA' hi)).2.1
    have hB (hi : i ∈ B') := (mem_filter.mp (hB' hi)).2.1
    have hC (hi : i ∈ C') := (mem_filter.mp (hC' hi)).2.1
    have hD (hi : i ∈ D') := (mem_filter.mp (hD' hi)).2.1
    cases hai : a i <;> simp_all
  have hZb : Z.filter (fun i => b i = true) = B' ∪ D' := by
    ext i
    simp only [Z,mem_filter,mem_union]
    have hA (hi : i ∈ A') := (mem_filter.mp (hA' hi)).2.2
    have hB (hi : i ∈ B') := (mem_filter.mp (hB' hi)).2.2
    have hC (hi : i ∈ C') := (mem_filter.mp (hC' hi)).2.2
    have hD (hi : i ∈ D') := (mem_filter.mp (hD' hi)).2.2
    cases hbi : b i <;> simp_all
  let z : Cube (4*q) := fun i => decide (i ∈ Z)
  have hwz : weight z = 2*q := by
    rw [support_weight]
    omega
  refine ⟨z,hwz,?_,?_⟩
  · have h := hamming_weight_identity z a
    change hammingDist z a + 2*(∑ i, if (decide (i ∈ Z)) && a i then 1 else 0) =
      weight z + weight a at h
    rw [support_meet,hZa,card_union_of_disjoint hCD] at h
    omega
  · have h := hamming_weight_identity z b
    change hammingDist z b + 2*(∑ i, if (decide (i ∈ Z)) && b i then 1 else 0) =
      weight z + weight b at h
    rw [support_meet,hZb,card_union_of_disjoint hBD] at h
    omega

/-- Binary translation of cube vertices. -/
def translateWord (t x : Cube n) : Cube n := fun i => Bool.xor (t i) (x i)

@[simp] theorem translateWord_involutive (t x : Cube n) :
    translateWord t (translateWord t x) = x := by
  funext i
  by_cases ht : t i = true <;> by_cases hx : x i = true <;> simp_all [translateWord]

@[simp] theorem translateWord_zero (t : Cube n) :
    translateWord t (fun _ => false) = t := by
  funext i
  by_cases ht : t i = true <;> simp_all [translateWord]

theorem hamming_translateWord (t x y : Cube n) :
    hammingDist (translateWord t x) (translateWord t y) = hammingDist x y := by
  simp only [hamming_eq_sum]
  apply sum_congr rfl
  intro i _
  by_cases ht : t i = true <;> by_cases hx : x i = true <;>
    by_cases hy : y i = true <;> simp_all [translateWord]

theorem weight_translateWord (t x : Cube n) :
    weight (translateWord t x) = hammingDist t x := by
  simp only [weight,hamming_eq_sum,translateWord]
  apply sum_congr rfl
  intro i _
  by_cases ht : t i = true <;> by_cases hx : x i = true <;> simp_all

/-- Every three even words in a dimension divisible by four have a common
middle-distance even word. No distinctness or positive-dimension assumption
is needed for this word-level statement. -/
theorem three_even_words_common_middle (q : ℕ) (a b c : Cube (4*q))
    (ha : weight a % 2 = 0) (hb : weight b % 2 = 0) (hc : weight c % 2 = 0) :
    ∃ z : Cube (4*q), weight z % 2 = 0 ∧
      hammingDist z a = 2*q ∧ hammingDist z b = 2*q ∧ hammingDist z c = 2*q := by
  have hab : weight (translateWord a b) % 2 = 0 := by
    rw [weight_translateWord,hamming_weight_parity]
    omega
  have hac : weight (translateWord a c) % 2 = 0 := by
    rw [weight_translateWord,hamming_weight_parity]
    omega
  obtain ⟨z,hz,hzb,hzc⟩ := two_even_words_have_balanced_selector q
    (translateWord a b) (translateWord a c) hab hac
  have hza : hammingDist (translateWord a z) a = 2*q := by
    have h := hamming_translateWord a z (fun _ => false)
    simpa only [translateWord_zero,distance_zero,hz] using h
  have hzb' : hammingDist (translateWord a z) b = 2*q := by
    have h := hamming_translateWord a z (translateWord a b)
    simpa only [translateWord_involutive,hzb] using h
  have hzc' : hammingDist (translateWord a z) c = 2*q := by
    have h := hamming_translateWord a z (translateWord a c)
    simpa only [translateWord_involutive,hzc] using h
  refine ⟨translateWord a z,?_,hza,hzb',hzc'⟩
  have hp := hamming_weight_parity (translateWord a z) a
  omega

/-- The common-neighbor geometry is expressed in actual graph distance. -/
theorem three_even_words_common_middle_graph (q : ℕ) (a b c : Cube (4*q))
    (ha : weight a % 2 = 0) (hb : weight b % 2 = 0) (hc : weight c % 2 = 0) :
    ∃ z : Cube (4*q), weight z % 2 = 0 ∧
      (cubeGraph (4*q)).dist z a = 2*q ∧
      (cubeGraph (4*q)).dist z b = 2*q ∧
      (cubeGraph (4*q)).dist z c = 2*q := by
  simpa only [cube_dist_eq_hamming] using three_even_words_common_middle q a b c ha hb hc

end ShellObservability.Hypercube
