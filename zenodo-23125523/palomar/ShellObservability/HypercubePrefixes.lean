module

public import ShellObservability.HypercubeBasic

@[expose] public section

namespace ShellObservability.Hypercube

lemma evenPrefix_weight (n j : ℕ) : weight (evenPrefix n j) = min n (2 * j) := by
  rw [weight_eq_card]
  simpa only [evenPrefix, decide_eq_true_eq] using (Fin.card_filter_val_lt (n := n) (m := 2*j))

lemma evenPrefix_step {n j : ℕ} (hj : 2 * (j + 1) ≤ n) :
    hammingDist (evenPrefix n j) (evenPrefix n (j + 1)) = 2 := by
  have h := hamming_weight_identity (evenPrefix n j) (evenPrefix n (j + 1))
  have hi : (∑ i, if evenPrefix n j i && evenPrefix n (j + 1) i then 1 else 0) =
      weight (evenPrefix n j) := by
    unfold weight
    apply Finset.sum_congr rfl
    intro i _
    simp only [evenPrefix]
    by_cases hlt : i.val < 2*j
    · have hlt' : i.val < 2*(j+1) := by omega
      simp [hlt, hlt']
    · simp [hlt]
  rw [hi, evenPrefix_weight, evenPrefix_weight, min_eq_right (by omega), min_eq_right hj] at h
  omega

lemma evenPrefix_zero (n : ℕ) : evenPrefix n 0 = fun _ => false := by
  funext i
  simp [evenPrefix]

lemma hamming_false {n : ℕ} (x : Cube n) : hammingDist x (fun _ => false) = weight x := by
  rw [hamming_eq_sum]
  unfold weight
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> simp

lemma evenPrefix_final (q : ℕ) : evenPrefix (4*q) (2*q) = fun _ => true := by
  funext i
  simp [evenPrefix, show i.val < 2*(2*q) by omega]

lemma hamming_true_add_weight {n : ℕ} (x : Cube n) :
    hammingDist x (fun _ => true) + weight x = n := by
  rw [hamming_eq_sum, weight, ← Finset.sum_add_distrib]
  have h : ∀ i : Fin n, (if x i ≠ true then 1 else 0) + (if x i then 1 else 0) = 1 := by
    intro i
    cases x i <;> simp
  simp_rw [h]
  simp

/-- A nearest-neighbor walk on the even integers cannot jump over its midpoint. -/
lemma even_walk_intermediate (f : ℕ → ℕ) (N M : ℕ)
    (hm : M % 2 = 0) (he : ∀ j ≤ N, f j % 2 = 0)
    (hstep : ∀ j < N, f (j+1) ≤ f j + 2 ∧ f j ≤ f (j+1) + 2)
    (hend : f 0 + f N = 2*M) : ∃ j ≤ N, f j = M := by
  by_contra h
  push Not at h
  have hzero : f 0 ≠ M := h 0 (by omega)
  have hn : f N ≠ M := h N (by omega)
  rcases lt_or_gt_of_ne hzero with hlow | hhigh
  · have hall : ∀ j ≤ N, f j < M := by
      intro j
      induction j with
      | zero => intro _; exact hlow
      | succ j ih =>
        intro hj
        have hp := ih (by omega)
        have hs := (hstep j (by omega)).1
        have ep := he j (by omega)
        have en := he (j+1) hj
        have hn := h (j+1) hj
        omega
    have := hall N (by omega)
    omega
  · have hall : ∀ j ≤ N, M < f j := by
      intro j
      induction j with
      | zero => intro _; exact hhigh
      | succ j ih =>
        intro hj
        have hp := ih (by omega)
        have hs := (hstep j (by omega)).2
        have ep := he j (by omega)
        have en := he (j+1) hj
        have hn := h (j+1) hj
        omega
    have := hall N (by omega)
    omega

/-- Only linearly many even prefixes bisect every even word from its antipode. -/
theorem evenPrefix_balances (q : ℕ) (hq : 0 < q) (x : Cube (4*q))
    (heven : weight x % 2 = 0) :
    ∃ j < 2*q, hammingDist x (evenPrefix (4*q) j) = 2*q := by
  let f := fun j => hammingDist x (evenPrefix (4*q) j)
  have he : ∀ j ≤ 2*q, f j % 2 = 0 := by
    intro j hj
    dsimp [f]
    rw [hamming_weight_parity, evenPrefix_weight, min_eq_right (by omega)]
    omega
  have hs : ∀ j < 2*q, f (j+1) ≤ f j + 2 ∧ f j ≤ f (j+1) + 2 := by
    intro j hj
    have hdist := evenPrefix_step (n := 4*q) (j := j) (by omega)
    have h1 := hammingDist_triangle x (evenPrefix (4*q) j) (evenPrefix (4*q) (j+1))
    have h2 := hammingDist_triangle x (evenPrefix (4*q) (j+1)) (evenPrefix (4*q) j)
    rw [hdist] at h1
    rw [hammingDist_comm (evenPrefix (4*q) (j+1)), hdist] at h2
    exact ⟨h1,h2⟩
  have h0 : f 0 = weight x := by dsimp [f]; rw [evenPrefix_zero, hamming_false]
  have hf : f (2*q) + weight x = 4*q := by
    dsimp [f]
    rw [evenPrefix_final]
    exact hamming_true_add_weight x
  obtain ⟨j,hj,hbal⟩ := even_walk_intermediate f (2*q) (2*q) (by omega) he hs (by omega)
  by_cases hj' : j < 2*q
  · exact ⟨j,hj',hbal⟩
  · have hjj : j = 2*q := by omega
    subst j
    refine ⟨0, by omega, ?_⟩
    change f 0 = 2*q
    omega

/-- The explicit family of even prefixes, excluding the redundant full prefix. -/
def prefixSet (q : ℕ) : Finset (Cube (4*q)) :=
  (Finset.range (2*q)).image (evenPrefix (4*q))

lemma mem_prefixSet {q : ℕ} {z : Cube (4*q)} :
    z ∈ prefixSet q ↔ ∃ j < 2*q, evenPrefix (4*q) j = z := by
  simp [prefixSet]

lemma prefixSet_card (q : ℕ) : (prefixSet q).card = 2*q := by
  rw [prefixSet, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hw := congrArg weight hij
  have hi' : i < 2*q := Finset.mem_range.mp hi
  have hj' : j < 2*q := Finset.mem_range.mp hj
  rw [evenPrefix_weight, evenPrefix_weight, min_eq_right (by omega),
    min_eq_right (by omega)] at hw
  omega

lemma prefixSet_even {q : ℕ} {z : Cube (4*q)} (hz : z ∈ prefixSet q) :
    weight z % 2 = 0 := by
  obtain ⟨j,hj,rfl⟩ := mem_prefixSet.mp hz
  rw [evenPrefix_weight, min_eq_right (by omega)]
  omega

lemma prefixSet_balances (q : ℕ) (hq : 0 < q) (x : Cube (4*q))
    (heven : weight x % 2 = 0) :
    ∃ z ∈ prefixSet q, hammingDist x z = 2*q := by
  obtain ⟨j,hj,hbal⟩ := evenPrefix_balances q hq x heven
  exact ⟨evenPrefix (4*q) j, mem_prefixSet.mpr ⟨j,hj,rfl⟩, hbal⟩

lemma evenPrefix_distance_of_le {n i j : ℕ} (hij : i ≤ j) (hj : 2*j ≤ n) :
    hammingDist (evenPrefix n i) (evenPrefix n j) = 2*(j-i) := by
  have h := hamming_weight_identity (evenPrefix n i) (evenPrefix n j)
  have hi : (∑ k, if evenPrefix n i k && evenPrefix n j k then 1 else 0) =
      weight (evenPrefix n i) := by
    unfold weight
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k.val < 2*i
    · have hk' : k.val < 2*j := by omega
      simp [evenPrefix,hk,hk']
    · simp [evenPrefix,hk]
  rw [hi,evenPrefix_weight,evenPrefix_weight,min_eq_right (by omega),min_eq_right hj] at h
  omega

/-- Prefix labels inherit twice the usual distance along the index path. -/
theorem evenPrefix_distance {n i j : ℕ} (hi : 2*i ≤ n) (hj : 2*j ≤ n) :
    hammingDist (evenPrefix n i) (evenPrefix n j) = 2*Nat.dist i j := by
  rcases le_total i j with hij | hji
  · rw [Nat.dist_eq_sub_of_le hij]
    exact evenPrefix_distance_of_le hij hj
  · rw [hammingDist_comm, Nat.dist_eq_sub_of_le_right hji]
    exact evenPrefix_distance_of_le hji hi

/-- Among the selected prefixes, middle-distance edges join indices q apart. -/
theorem evenPrefix_orthogonal_iff (q i j : ℕ) (hi : i < 2*q) (hj : j < 2*q) :
    hammingDist (evenPrefix (4*q) i) (evenPrefix (4*q) j) = 2*q ↔
      i+q=j ∨ j+q=i := by
  rw [evenPrefix_distance (by omega) (by omega)]
  unfold Nat.dist
  omega

/-- The selected prefixes induce a perfect matching in the middle-distance
relation, with one partner for every selected prefix. -/
theorem evenPrefix_unique_orthogonal_partner (q i : ℕ) (hi : i < 2*q) :
    ∃! j, j < 2*q ∧ hammingDist (evenPrefix (4*q) i) (evenPrefix (4*q) j) = 2*q := by
  by_cases hlow : i < q
  · refine ⟨i+q, ⟨by omega, ?_⟩, ?_⟩
    · rw [evenPrefix_orthogonal_iff q i (i+q) hi (by omega)]
      exact Or.inl rfl
    · intro j hj
      rw [evenPrefix_orthogonal_iff q i j hi hj.1] at hj
      omega
  · refine ⟨i-q, ⟨by omega, ?_⟩, ?_⟩
    · rw [evenPrefix_orthogonal_iff q i (i-q) hi (by omega)]
      right
      omega
    · intro j hj
      rw [evenPrefix_orthogonal_iff q i j hi hj.1] at hj
      omega

end ShellObservability.Hypercube
