module

public import ShellObservability.HypercubeCounterexample

@[expose] public section

/-! Structural reduction of distance equalization to antipodal domination.
This is the predicate-level form of the closed-domination problem on the
antipodal quotient of the even orthogonality graph. -/

namespace ShellObservability.Hypercube

def antipode {n : ℕ} (x : Cube n) : Cube n := fun i => !x i

lemma antipode_ne_coordinate {n : ℕ} (x : Cube n) (i : Fin n) :
    x i ≠ antipode x i := by
  cases hx : x i <;> simp [antipode,hx]

lemma antipode_ne {n : ℕ} (hn : 0 < n) (x : Cube n) : x ≠ antipode x := by
  intro h
  exact antipode_ne_coordinate x ⟨0,hn⟩ (congrFun h ⟨0,hn⟩)

lemma antipode_weight {n : ℕ} (x : Cube n) : weight (antipode x) + weight x = n := by
  rw [weight, weight, ← Finset.sum_add_distrib]
  have hi : ∀ i, (if antipode x i then 1 else 0) + (if x i then 1 else 0) = 1 := by
    intro i
    cases hx : x i <;> simp [antipode,hx]
  simp_rw [hi]
  simp

/-- Opposite parity pairs have no equidistant vertex, so every equalizer
necessarily contains an entire parity class. -/
theorem equalizer_contains_parity_class {n : ℕ} (S : Finset (Cube n))
    (hS : IsDistanceEqualizer S) :
    (∀ x, weight x % 2 = 1 → x ∈ S) ∨ (∀ x, weight x % 2 = 0 → x ∈ S) := by
  classical
  by_cases ho : ∀ x, weight x % 2 = 1 → x ∈ S
  · exact Or.inl ho
  · right
    push Not at ho
    obtain ⟨x,hx,hxs⟩ := ho
    intro y hy
    by_contra hys
    have hxy : x ≠ y := by intro h; subst y; omega
    obtain ⟨z,_,hz⟩ := hS x hxs y hys hxy
    rw [cube_dist_eq_hamming, cube_dist_eq_hamming] at hz
    have hp := hamming_weight_parity z x
    have hp' := hamming_weight_parity z y
    omega

/-- An odd parity class supplies every nonantipodal bisector. The remaining
condition is precisely closed domination after identifying antipodes. -/
theorem odd_union_equalizer_iff_antipodal_cover (q : ℕ) (hq : 0 < q)
    (T : Finset (Cube (4*q))) :
    IsDistanceEqualizer (oddWords (4*q) ∪ T) ↔
      ∀ x, weight x % 2 = 0 →
        x ∈ T ∨ antipode x ∈ T ∨ ∃ z ∈ T, hammingDist z x = 2*q := by
  classical
  constructor
  · intro heq x hx
    by_cases hxt : x ∈ T
    · exact Or.inl hxt
    by_cases hat : antipode x ∈ T
    · exact Or.inr (Or.inl hat)
    right; right
    have haw := antipode_weight x
    have hae : weight (antipode x) % 2 = 0 := by omega
    have hxo : x ∉ oddWords (4*q) := by simp [oddWords,hx]
    have hao : antipode x ∉ oddWords (4*q) := by simp [oddWords,hae]
    obtain ⟨z,hz,hd⟩ := heq x (by simp [hxo,hxt]) (antipode x)
      (by simp [hao,hat]) (antipode_ne (by omega) x)
    rw [cube_dist_eq_hamming, cube_dist_eq_hamming] at hd
    have hs := hamming_antipodal_sum x (antipode x) z (antipode_ne_coordinate x)
    have hmid : hammingDist z x = 2*q := by omega
    have hp := hamming_weight_parity z x
    have hze : weight z % 2 = 0 := by omega
    have hzt : z ∈ T := by simpa [oddWords,hze] using hz
    exact ⟨z,hzt,hmid⟩
  · intro hcover x hx y hy _
    have hxo : x ∉ oddWords (4*q) := fun h => hx (Finset.mem_union_left _ h)
    have hyo : y ∉ oddWords (4*q) := fun h => hy (Finset.mem_union_left _ h)
    have hxe : weight x % 2 = 0 := by
      have hne : weight x % 2 ≠ 1 := by simpa [oddWords] using hxo
      omega
    have hye : weight y % 2 = 0 := by
      have hne : weight y % 2 ≠ 1 := by simpa [oddWords] using hyo
      omega
    by_cases hc : ∃ i, x i = y i
    · obtain ⟨z,hz,hd⟩ := exists_odd_graph_bisector x y hxe hye hc
      exact ⟨z,Finset.mem_union_left _ (by simpa [oddWords] using hz),hd⟩
    · have ha : ∀ i, x i ≠ y i := by simpa only [not_exists] using hc
      have hay : antipode x = y := by
        funext i
        have hi := ha i
        cases hx' : x i <;> cases hy' : y i <;> simp_all [antipode]
      obtain hxt | hat | ⟨z,hzt,hmid⟩ := hcover x hxe
      · exact False.elim (hx (Finset.mem_union_right _ hxt))
      · exact False.elim (hy (Finset.mem_union_right _ (hay ▸ hat)))
      · have hs := hamming_antipodal_sum x y z ha
        refine ⟨z,Finset.mem_union_right _ hzt,?_⟩
        rw [cube_dist_eq_hamming,cube_dist_eq_hamming]
        omega

end ShellObservability.Hypercube
