module

public import ShellObservability.HypercubeReduction

@[expose] public section

/-! A linear lower bound for distance equalizers of the hypercube `Q_{4q}`.

The argument is a polynomial-method computation with the top Walsh character:
a product of fewer than `n` linear forms in the sign coordinates is orthogonal
to the parity character. Applied to the square of a product of the linear forms
attached to an antipodal cover, this forces a kernel vector of the cover's sign
matrix to vanish, so the cover has at least `2q - 1` members. -/

namespace ShellObservability.Hypercube

/-- The `±1` sign coordinates of a Boolean word. -/
def signVec {n : ℕ} (x : Cube n) (i : Fin n) : ℚ := if x i then -1 else 1

/-- The parity (top Walsh) character. -/
def parityChar {n : ℕ} (x : Cube n) : ℚ := ∏ i, signVec x i

/-- (F1) Sign vectors have inner product `n - 2 * hammingDist`. -/
lemma signVec_inner {n : ℕ} (b y : Cube n) :
    ∑ i, signVec b i * signVec y i = (n : ℚ) - 2 * (hammingDist b y : ℚ) := by
  rw [hamming_eq_sum]
  push_cast
  rw [Finset.mul_sum]
  have hn : (n : ℚ) = ∑ _i : Fin n, (1 : ℚ) := by simp
  rw [hn, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hb : b i <;> cases hy : y i <;> norm_num [signVec, hb, hy]

/-- (F2) The antipode negates every sign coordinate. -/
lemma signVec_antipode {n : ℕ} (x : Cube n) (i : Fin n) :
    signVec (antipode x) i = - signVec x i := by
  cases hx : x i <;> simp [signVec, antipode, hx]

lemma signVec_flip_same {n : ℕ} (j : Fin n) (y : Cube n) :
    signVec (flipCoordinate j y) j = - signVec y j := by
  cases hy : y j <;> simp [signVec, flipCoordinate, hy]

lemma signVec_flip_other {n : ℕ} (j : Fin n) (y : Cube n) (i : Fin n) (hi : i ≠ j) :
    signVec (flipCoordinate j y) i = signVec y i := by
  simp [signVec, flipCoordinate, hi]

/-- (F3) Flipping a coordinate negates the parity character. -/
lemma parityChar_flip {n : ℕ} (j : Fin n) (y : Cube n) :
    parityChar (flipCoordinate j y) = - parityChar y := by
  unfold parityChar
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i => signVec y i) (Finset.mem_univ j),
    signVec_flip_same, neg_mul]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact signVec_flip_other j y i (Finset.ne_of_mem_erase hi)

lemma parityChar_eq_neg_one_pow {n : ℕ} (y : Cube n) :
    parityChar y = (-1 : ℚ) ^ weight y := by
  unfold parityChar weight
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro i _
  cases hy : y i <;> simp [signVec, hy]

lemma parityChar_of_even {n : ℕ} (y : Cube n) (hy : weight y % 2 = 0) :
    parityChar y = 1 := by
  rw [parityChar_eq_neg_one_pow]
  exact Even.neg_one_pow (Nat.even_iff.mpr hy)

lemma parityChar_of_odd {n : ℕ} (y : Cube n) (hy : weight y % 2 = 1) :
    parityChar y = -1 := by
  rw [parityChar_eq_neg_one_pow]
  exact Odd.neg_one_pow (Nat.odd_iff.mpr hy)

/-- A monomial in the sign coordinates that misses a coordinate is orthogonal
to the parity character. -/
lemma parityChar_monomial_sum_eq_zero {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℚ) (φ : ι → Fin n) (j0 : Fin n) (hj0 : ∀ i, φ i ≠ j0) :
    ∑ y : Cube n, parityChar y * ∏ i : ι, (c i * signVec y (φ i)) = 0 := by
  set f : Cube n → ℚ := fun y => parityChar y * ∏ i : ι, (c i * signVec y (φ i)) with hf
  have hneg : ∀ y, f (flipCoordinate j0 y) = - f y := by
    intro y
    simp only [hf]
    rw [parityChar_flip, neg_mul]
    congr 2
    apply Finset.prod_congr rfl
    intro i _
    rw [signVec_flip_other j0 y (φ i) (hj0 i)]
  have hre : ∑ y, f ((flipCoordinate_involutive j0).toPerm _ y) = ∑ y, f y :=
    Equiv.sum_comp ((flipCoordinate_involutive j0).toPerm _) f
  have hre' : ∑ y, f ((flipCoordinate_involutive j0).toPerm _ y) = - ∑ y, f y := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y _
    exact hneg y
  have : ∑ y, f y = - ∑ y, f y := by rw [← hre']; exact hre.symm
  linarith

/-- **Lemma A (top-character orthogonality).** A product of fewer than `n`
linear forms in the sign coordinates is orthogonal to the parity character. -/
theorem parityChar_orthogonal_low_degree {n : ℕ} {ι : Type*} [Fintype ι]
    (hcard : Fintype.card ι < n) (a : ι → Fin n → ℚ) :
    ∑ y : Cube n, parityChar y * ∏ i : ι, (∑ j, a i j * signVec y j) = 0 := by
  classical
  have hexp : ∀ y : Cube n, ∏ i : ι, (∑ j, a i j * signVec y j) =
      ∑ φ : ι → Fin n, ∏ i : ι, (a i (φ i) * signVec y (φ i)) := by
    intro y
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro φ _
  have hns : ¬ Function.Surjective φ := by
    intro hsurj
    have := Fintype.card_le_of_surjective φ hsurj
    simp only [Fintype.card_fin] at this
    omega
  obtain ⟨j0, hj0⟩ : ∃ j0, ∀ i, φ i ≠ j0 := by
    simpa [Function.Surjective] using hns
  have h := parityChar_monomial_sum_eq_zero (fun i => a i (φ i)) φ j0 hj0
  exact h

/-- The word with a single `true` entry. -/
def unitWord {n : ℕ} (i : Fin n) : Cube n := fun j => decide (j = i)

lemma weight_unitWord {n : ℕ} (i : Fin n) : weight (unitWord i) = 1 := by
  simp [weight, unitWord]

lemma signVec_unitWord_sum {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    ∑ j, v j * signVec (unitWord i) j = (∑ j, v j) - 2 * v i := by
  have h : ∀ j, v j * signVec (unitWord i) j = v j - 2 * (if j = i then v j else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [signVec, unitWord]; ring
    · simp [signVec, unitWord, hj]
  simp_rw [h]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

/-- A vector annihilating the sign vectors of all odd-weight words vanishes
(in dimension `4q`, indeed in every dimension other than two). -/
lemma eq_zero_of_orthogonal_odd (q : ℕ) (hq : 0 < q) (v : Fin (4*q) → ℚ)
    (hv : ∀ y : Cube (4*q), weight y % 2 = 1 → ∑ j, v j * signVec y j = 0) : v = 0 := by
  have hi : ∀ i, 2 * v i = ∑ j, v j := by
    intro i
    have h := hv (unitWord i) (by rw [weight_unitWord])
    rw [signVec_unitWord_sum] at h
    linarith
  set s := ∑ j, v j with hs
  have hsum : 2 * s = (4 * q : ℚ) * s := by
    calc 2 * s = ∑ j, 2 * v j := by rw [hs, Finset.mul_sum]
      _ = ∑ _j : Fin (4*q), s := by
        apply Finset.sum_congr rfl
        intro j _
        exact hi j
      _ = (4 * q : ℚ) * s := by simp
  have hq' : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hs0 : s = 0 := by
    have h2 : ((4 * q : ℚ) - 2) * s = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · linarith
    · exact h
  funext i
  have := hi i
  rw [hs0] at this
  simpa using this

/-- Any set T of words meeting the antipodal cover condition in dimension 4q has at least 2q-1 members. -/
theorem antipodal_cover_card_lower_bound (q : ℕ) (hq : 0 < q) (T : Finset (Cube (4*q)))
    (hcover : ∀ x, weight x % 2 = 0 →
      x ∈ T ∨ antipode x ∈ T ∨ ∃ z ∈ T, hammingDist z x = 2*q) :
    2*q - 1 ≤ T.card := by
  classical
  by_contra hlt
  have hcard : T.card + 2 ≤ 2 * q := by omega
  -- Step 1: a nonzero kernel vector of the sign matrix of `T`.
  let L : (Fin (4*q) → ℚ) →ₗ[ℚ] (↥T → ℚ) :=
    { toFun := fun v b => ∑ j, v j * signVec b.1 j
      map_add' := by
        intro v w
        funext b
        simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c v
        funext b
        simp [Finset.mul_sum, mul_assoc] }
  have hker : LinearMap.ker L ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, Fintype.card_coe]
    omega
  obtain ⟨v, hvker, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hvT : ∀ b ∈ T, ∑ j, v j * signVec b j = 0 := by
    intro b hb
    have := congrFun (LinearMap.mem_ker.mp hvker) ⟨b, hb⟩
    simpa [L] using this
  -- Step 2: the even members and the test polynomial.
  set T' : Finset (Cube (4*q)) := T.filter (fun b => weight b % 2 = 0) with hT'
  have hT'card : T'.card ≤ T.card := Finset.card_filter_le _ _
  let a : Bool × Option ↥T' → Fin (4*q) → ℚ := fun p =>
    match p.2 with
    | none => v
    | some b => signVec b.1
  let Q : Cube (4*q) → ℚ := fun y =>
    (∑ j, v j * signVec y j) * ∏ b : ↥T', (∑ j, signVec b.1 j * signVec y j)
  have hPQ : ∀ y, ∏ p : Bool × Option ↥T', (∑ j, a p j * signVec y j) = Q y ^ 2 := by
    intro y
    rw [Fintype.prod_prod_type, Fintype.prod_bool, Fintype.prod_option]
    simp only [a, Q]
    ring
  have hιcard : Fintype.card (Bool × Option ↥T') < 4*q := by
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_option, Fintype.card_coe]
    omega
  have horth := parityChar_orthogonal_low_degree hιcard a
  simp_rw [hPQ] at horth
  -- Step 3: `Q` vanishes on even words.
  have hQeven : ∀ y : Cube (4*q), weight y % 2 = 0 → Q y = 0 := by
    intro y hy
    rcases hcover y hy with hyT | haT | ⟨z, hzT, hzd⟩
    · simp only [Q]
      rw [hvT y hyT, zero_mul]
    · have h := hvT _ haT
      simp_rw [signVec_antipode, mul_neg, Finset.sum_neg_distrib] at h
      simp only [Q]
      rw [neg_eq_zero.mp h, zero_mul]
    · have hzeven : weight z % 2 = 0 := by
        have hp := hamming_weight_parity z y
        omega
      have hzT' : z ∈ T' := by
        rw [hT']
        exact Finset.mem_filter.mpr ⟨hzT, hzeven⟩
      simp only [Q]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ (⟨z, hzT'⟩ : ↥T'))
      rw [signVec_inner, hzd]
      push_cast
      ring
  -- Step 4: `Q` vanishes everywhere.
  have hterm : ∀ y : Cube (4*q), parityChar y * Q y ^ 2 = - Q y ^ 2 := by
    intro y
    rcases Nat.mod_two_eq_zero_or_one (weight y) with hy | hy
    · rw [hQeven y hy]; simp
    · rw [parityChar_of_odd y hy]; ring
  simp_rw [hterm] at horth
  rw [Finset.sum_neg_distrib, neg_eq_zero] at horth
  have hQall : ∀ y : Cube (4*q), Q y = 0 := by
    intro y
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (Q y))).mp horth y
      (Finset.mem_univ y)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  -- hence `v` annihilates all odd sign vectors
  have hvodd : ∀ y : Cube (4*q), weight y % 2 = 1 → ∑ j, v j * signVec y j = 0 := by
    intro y hy
    have h := hQall y
    simp only [Q] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exfalso
      obtain ⟨b, _, hb⟩ := Finset.prod_eq_zero_iff.mp h
      have hbmem : b.1 ∈ T.filter (fun b => weight b % 2 = 0) := b.2
      have hbeven : weight b.1 % 2 = 0 := (Finset.mem_filter.mp hbmem).2
      rw [signVec_inner] at hb
      have hp := hamming_weight_parity b.1 y
      have hd : (hammingDist b.1 y : ℚ) = 2 * q := by
        push_cast at hb
        linarith
      have hd' : hammingDist b.1 y = 2 * q := by exact_mod_cast hd
      omega
  -- Step 5: contradiction.
  exact hv0 (eq_zero_of_orthogonal_odd q hq v hvodd)

/-- Flipping a common coordinate preserves Hamming distance. -/
lemma hammingDist_flipCoordinate {n : ℕ} (j : Fin n) (x y : Cube n) :
    hammingDist (flipCoordinate j x) (flipCoordinate j y) = hammingDist x y := by
  rw [hamming_eq_sum, hamming_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = j
  · subst hi
    cases hx : x i <;> cases hy : y i <;> simp [flipCoordinate, hx, hy]
  · simp [flipCoordinate, hi]

/-- The image of a distance equalizer under a coordinate flip is a distance equalizer. -/
lemma isDistanceEqualizer_image_flip {n : ℕ} (j : Fin n) (S : Finset (Cube n))
    (hS : IsDistanceEqualizer S) : IsDistanceEqualizer (S.image (flipCoordinate j)) := by
  classical
  have hinv := flipCoordinate_involutive j
  intro x hx y hy hxy
  have hx' : flipCoordinate j x ∉ S := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨_, h, hinv x⟩)
  have hy' : flipCoordinate j y ∉ S := by
    intro h
    exact hy (Finset.mem_image.mpr ⟨_, h, hinv y⟩)
  obtain ⟨z, hz, hd⟩ := hS _ hx' _ hy' (fun h => hxy (hinv.injective h))
  refine ⟨flipCoordinate j z, Finset.mem_image_of_mem _ hz, ?_⟩
  rw [cube_dist_eq_hamming, cube_dist_eq_hamming] at hd ⊢
  rw [← hammingDist_flipCoordinate j (flipCoordinate j z) x,
    ← hammingDist_flipCoordinate j (flipCoordinate j z) y, hinv z]
  exact hd

/-- The lower bound for equalizers containing the odd parity class. -/
lemma equalizer_card_lower_bound_of_odd (q : ℕ) (hq : 0 < q) (S : Finset (Cube (4*q)))
    (hS : IsDistanceEqualizer S) (hodd : ∀ x, weight x % 2 = 1 → x ∈ S) :
    2^(4*q-1) + 2*q - 1 ≤ S.card := by
  classical
  have hsub : oddWords (4*q) ⊆ S := by
    intro x hx
    exact hodd x ((mem_oddWords x).mp hx)
  have hunion : oddWords (4*q) ∪ (S \ oddWords (4*q)) = S := Finset.union_sdiff_of_subset hsub
  have hcover := (odd_union_equalizer_iff_antipodal_cover q hq (S \ oddWords (4*q))).mp
    (by rw [hunion]; exact hS)
  have hT := antipodal_cover_card_lower_bound q hq _ hcover
  have hcard : S.card = (oddWords (4*q)).card + (S \ oddWords (4*q)).card := by
    conv_lhs => rw [← hunion]
    exact Finset.card_union_of_disjoint Finset.disjoint_sdiff
  rw [card_oddWords (4*q) (by omega)] at hcard
  omega

/-- Every distance equalizer of Q_{4q} has at least 2^(4q-1) + 2q - 1 vertices. -/
theorem equalizer_card_lower_bound (q : ℕ) (hq : 0 < q) (S : Finset (Cube (4*q)))
    (hS : IsDistanceEqualizer S) : 2^(4*q-1) + 2*q - 1 ≤ S.card := by
  classical
  rcases equalizer_contains_parity_class S hS with hodd | heven
  · exact equalizer_card_lower_bound_of_odd q hq S hS hodd
  · let j : Fin (4*q) := ⟨0, by omega⟩
    have hinv := flipCoordinate_involutive j
    have hS' := isDistanceEqualizer_image_flip j S hS
    have hodd' : ∀ x, weight x % 2 = 1 → x ∈ S.image (flipCoordinate j) := by
      intro x hx
      have hp := weight_flip_parity x j
      exact Finset.mem_image.mpr ⟨flipCoordinate j x, heven _ (by omega), hinv x⟩
    have h := equalizer_card_lower_bound_of_odd q hq _ hS' hodd'
    rwa [Finset.card_image_of_injective _ hinv.injective] at h

/-- The equidistant dimension of Q_{4q} is determined up to one. -/
theorem equidistant_dimension_within_one (q : ℕ) (hq : 0 < q) :
    (∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧ S.card = 2^(4*q-1) + 2*q) ∧
    (∀ S : Finset (Cube (4*q)), IsDistanceEqualizer S → 2^(4*q-1) + 2*q - 1 ≤ S.card) :=
  ⟨⟨prefixEqualizer q, prefixEqualizer_isDistanceEqualizer q hq, prefixEqualizer_card q hq⟩,
    fun S hS => equalizer_card_lower_bound q hq S hS⟩

end ShellObservability.Hypercube
