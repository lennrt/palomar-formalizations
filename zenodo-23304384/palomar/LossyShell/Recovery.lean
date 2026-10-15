module

public import LossyShell.Moments
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.LinearCombination

/-!
# Recovering the two legs from the first two moments

* The means determine the folded population `a + b` (`fold_eq_of_legMean_eq`).
* The covariance form of a vector `d` determines `d` up to sign when `0 < p < 1`
  (`eq_or_eq_neg_of_Qform`). The proof locates the deepest nonzero entry `m` from the covariance
  diagonal, determines its magnitude from entry `(m, m)`, and then solves for shallower entries
  from column `m`. The pivots `1 - p ^ (k + 1)` are nonzero because `0 < p < 1`.
  Choosing the sign of the deepest entry fixes the signs of every recovered entry.
* Polarization turns the covariance of the report into the covariance form of `a - b`.
-/

@[expose] public section

namespace LossyShell

open Finset

variable {n : ℕ} {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ### A triangular uniqueness lemma -/

/-- If `B` vanishes strictly below the diagonal and has a nonzero diagonal, and every equation
`∑ i, g i * B i k = 0` holds at the indices where `g k ≠ 0`, then `g = 0`. -/
lemma triangular_eq_zero (B : Fin n → Fin n → K) (hdiag : ∀ k, B k k ≠ 0)
    (hlow : ∀ i k, i < k → B i k = 0) (g : Fin n → K)
    (h : ∀ k, g k ≠ 0 → ∑ i, g i * B i k = 0) : g = 0 := by
  by_contra hg
  have hne : (univ.filter fun k => g k ≠ 0).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hg
    exact ⟨k, by simpa using hk⟩
  set k := (univ.filter fun k => g k ≠ 0).max' hne with hkdef
  have hk : g k ≠ 0 := by
    have := max'_mem _ hne
    simpa using this
  have habove : ∀ j, k < j → g j = 0 := by
    intro j hj
    by_contra hj0
    have : j ≤ k := le_max' _ j (by simpa using hj0)
    exact absurd hj (not_lt.mpr this)
  have hsum := h k hk
  rw [sum_eq_single k] at hsum
  · exact mul_ne_zero hk (hdiag k) hsum
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [hlow i k hlt, mul_zero]
    · rw [habove i hgt, zero_mul]
  · simp

omit [IsStrictOrderedRing K] in
/-- Every nonzero vector has a deepest nonzero entry. -/
lemma exists_last_ne_zero {d : Fin n → K} (hd : d ≠ 0) :
    ∃ m, d m ≠ 0 ∧ ∀ j, m < j → d j = 0 := by
  have hne : (univ.filter fun k => d k ≠ 0).Nonempty := by
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hd
    exact ⟨k, by simpa using hk⟩
  refine ⟨(univ.filter fun k => d k ≠ 0).max' hne, ?_, ?_⟩
  · have := max'_mem _ hne
    simpa using this
  · intro j hj
    by_contra hj0
    have : j ≤ (univ.filter fun k => d k ≠ 0).max' hne := le_max' _ j (by simpa using hj0)
    exact absurd hj (not_lt.mpr this)

/-! ### The means determine the fold -/

lemma landProb_self_ne_zero {p : K} (hp : 0 < p) (i : Fin n) : landProb p i i.val ≠ 0 := by
  rw [landProb_self]
  exact pow_ne_zero _ hp.ne'

/-- Equal mean vectors force equal folded populations. -/
lemma fold_eq_of_legMean_eq {p : K} (hp : 0 < p) (c c' : Fin n → K)
    (h : ∀ k : Fin n, ∑ i, c i * landProb p i k.val = ∑ i, c' i * landProb p i k.val) :
    c = c' := by
  have := triangular_eq_zero (fun i k => landProb p i k.val)
    (fun k => landProb_self_ne_zero hp k)
    (fun i k hik => landProb_eq_zero_of_lt p (Fin.lt_def.mp hik)) (c - c') (by
      intro k _
      simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
      rw [h k, sub_self])
  exact sub_eq_zero.mp this

/-! ### The covariance form near the deepest entry -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Beyond the deepest nonzero entry, the diagonal of the covariance form vanishes. -/
lemma Qform_diag_beyond (p : K) {d : Fin n → K} {m : Fin n} (hm : ∀ j, m < j → d j = 0)
    {k : Fin n} (hk : m < k) : Qform p d d k.val k.val = 0 := by
  unfold Qform
  apply sum_eq_zero; intro i _
  apply sum_eq_zero; intro j _
  by_cases hi : m < i
  · rw [hm i hi]; ring
  by_cases hj : m < j
  · rw [hm j hj]; ring
  have hik : i.val < k.val := by
    have := not_lt.mp hi; exact lt_of_le_of_lt (Fin.le_def.mp this) (Fin.lt_def.mp hk)
  have hjk : j.val < k.val := by
    have := not_lt.mp hj; exact lt_of_le_of_lt (Fin.le_def.mp this) (Fin.lt_def.mp hk)
  rw [pairProb_eq_zero_of_lt p i k.val hjk, landProb_eq_zero_of_lt p hik]
  ring

/-- At the deepest nonzero entry `m`, the diagonal is `d m ^ 2 * p^(m+1) * (1 - p^(m+1))`. -/
lemma Qform_diag_top (p : K) {d : Fin n → K} {m : Fin n} (hm : ∀ j, m < j → d j = 0) :
    Qform p d d m.val m.val = d m ^ 2 * (p ^ (m.val + 1) * (1 - p ^ (m.val + 1))) := by
  unfold Qform
  rw [sum_eq_single m]
  · rw [sum_eq_single m]
    · rw [pairProb_same, ite_eq_left rfl, landProb_self]; ring
    · intro j _ hjm
      rcases lt_or_gt_of_ne hjm with hlt | hgt
      · rw [pairProb_eq_zero_of_lt p m m.val (Fin.lt_def.mp hlt),
          landProb_eq_zero_of_lt p (Fin.lt_def.mp hlt)]; ring
      · rw [hm j hgt]; ring
    · simp
  · intro i _ him
    rcases lt_or_gt_of_ne him with hlt | hgt
    · apply sum_eq_zero; intro j _
      by_cases hj : m < j
      · rw [hm j hj]; ring
      rcases eq_or_lt_of_le (not_lt.mp hj) with hjm | hjm
      · subst hjm
        rw [pairProb_diag p (ne_of_lt hlt), landProb_eq_zero_of_lt p (Fin.lt_def.mp hlt)]; ring
      · rw [pairProb_eq_zero_of_lt p i m.val (Fin.lt_def.mp hjm),
          landProb_eq_zero_of_lt p (Fin.lt_def.mp hlt)]; ring
    · apply sum_eq_zero; intro j _
      rw [hm i hgt]; ring
  · simp

/-- Column `m` of the covariance form, above the deepest nonzero entry `m`. -/
lemma Qform_col_top (p : K) {d : Fin n → K} {m : Fin n} (hm : ∀ j, m < j → d j = 0)
    {k : Fin n} (hk : k < m) :
    Qform p d d k.val m.val =
      d m * p ^ (m.val + 1) * (d k - ∑ i, d i * landProb p i k.val) := by
  unfold Qform
  -- only the column `j = m` contributes
  have hcol : ∀ i : Fin n,
      ∑ j, d i * d j * (pairProb p i j k.val m.val - landProb p i k.val * landProb p j m.val) =
        d i * d m * (pairProb p i m k.val m.val - landProb p i k.val * p ^ (m.val + 1)) := by
    intro i
    rw [sum_eq_single m]
    · rw [landProb_self]
    · intro j _ hjm
      rcases lt_or_gt_of_ne hjm with hlt | hgt
      · rw [pairProb_eq_zero_of_lt p i k.val (Fin.lt_def.mp hlt),
          landProb_eq_zero_of_lt p (Fin.lt_def.mp hlt)]; ring
      · rw [hm j hgt]; ring
    · simp
  simp_rw [hcol]
  -- the pair term picks out `i = k`
  have hpair : ∀ i : Fin n, d i * d m * pairProb p i m k.val m.val =
      if i = k then d k * d m * p ^ (m.val + 1) else 0 := by
    intro i
    rcases lt_trichotomy i m with him | him | him
    · rw [pairProb_top p him]
      by_cases hik : i = k
      · subst hik; simp
      · have : ¬ (k.val = i.val) := fun h => hik (Fin.ext h.symm)
        simp [this, hik]
    · have hik : ¬ (i = k) := by
        rintro rfl
        exact absurd hk (by rw [him]; exact lt_irrefl _)
      rw [ite_eq_right hik, him, pairProb_same, ite_eq_right (Nat.ne_of_lt (Fin.lt_def.mp hk))]
      ring
    · have hik : ¬ (i = k) := by
        rintro rfl
        exact absurd (lt_trans hk him) (lt_irrefl _)
      rw [hm i him, ite_eq_right hik]
      ring
  have hsplit : ∀ i : Fin n,
      d i * d m * (pairProb p i m k.val m.val - landProb p i k.val * p ^ (m.val + 1)) =
        d i * d m * pairProb p i m k.val m.val -
          d m * p ^ (m.val + 1) * (d i * landProb p i k.val) := by
    intro i; ring
  simp_rw [hsplit, sum_sub_distrib, hpair, ← mul_sum]
  rw [sum_ite_eq' univ k]
  simp only [mem_univ, ite_true]
  ring

/-! ### The covariance form determines a vector up to sign -/

lemma diag_factor_pos {p : K} (hp0 : 0 < p) (hp1 : p < 1) (m : ℕ) :
    0 < p ^ (m + 1) * (1 - p ^ (m + 1)) := by
  have h1 : p ^ (m + 1) < 1 := pow_lt_one₀ hp0.le hp1 (Nat.succ_ne_zero m)
  have h2 : 0 < p ^ (m + 1) := pow_pos hp0 _
  nlinarith

lemma Qform_diag_top_ne_zero {p : K} (hp0 : 0 < p) (hp1 : p < 1) {d : Fin n → K} {m : Fin n}
    (hdm : d m ≠ 0) (hm : ∀ j, m < j → d j = 0) : Qform p d d m.val m.val ≠ 0 := by
  rw [Qform_diag_top p hm]
  have := diag_factor_pos hp0 hp1 m.val
  have : 0 < d m ^ 2 := by positivity
  positivity

/-- If every diagonal entry of the covariance form vanishes, the vector is zero. -/
lemma eq_zero_of_Qform_diag {p : K} (hp0 : 0 < p) (hp1 : p < 1) {d : Fin n → K}
    (h : ∀ k : Fin n, Qform p d d k.val k.val = 0) : d = 0 := by
  by_contra hd
  obtain ⟨m, hdm, hm⟩ := exists_last_ne_zero hd
  exact Qform_diag_top_ne_zero hp0 hp1 hdm hm (h m)

/-- Two vectors with the same deepest entry and the same column there agree. -/
lemma eq_of_Qform_col {p : K} (hp0 : 0 < p) (hp1 : p < 1) {d e : Fin n → K} {m : Fin n}
    (hdm : d m ≠ 0) (hme : e m = d m) (hd : ∀ j, m < j → d j = 0) (he : ∀ j, m < j → e j = 0)
    (h : ∀ k : Fin n, k < m → Qform p d d k.val m.val = Qform p e e k.val m.val) : d = e := by
  have hcoef : d m * p ^ (m.val + 1) ≠ 0 := mul_ne_zero hdm (pow_ne_zero _ hp0.ne')
  let B : Fin n → Fin n → K := fun i k => (if i = k then 1 else 0) - landProb p i k.val
  have hdiag : ∀ k, B k k ≠ 0 := by
    intro k
    show (if k = k then (1 : K) else 0) - landProb p k k.val ≠ 0
    rw [ite_eq_left rfl, landProb_self]
    have : p ^ (k.val + 1) < 1 := pow_lt_one₀ hp0.le hp1 (Nat.succ_ne_zero _)
    exact sub_ne_zero.mpr (ne_of_gt this)
  have hlow : ∀ i k, i < k → B i k = 0 := by
    intro i k hik
    show (if i = k then (1 : K) else 0) - landProb p i k.val = 0
    rw [ite_eq_right (ne_of_lt hik), landProb_eq_zero_of_lt p (Fin.lt_def.mp hik), sub_zero]
  have hrow : ∀ (g : Fin n → K) (k : Fin n),
      ∑ i, g i * B i k = g k - ∑ i, g i * landProb p i k.val := by
    intro g k
    show ∑ i, g i * ((if i = k then (1 : K) else 0) - landProb p i k.val) = _
    simp only [mul_sub, sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [sum_ite_eq' univ k]
    simp
  have := triangular_eq_zero B hdiag hlow (d - e) (by
    intro k hk
    rw [hrow]
    have hkm : k < m := by
      by_contra hkm
      rcases eq_or_lt_of_le (not_lt.mp hkm) with hkm' | hkm'
      · subst hkm'; simp [hme] at hk
      · simp [hd k hkm', he k hkm'] at hk
    have hk' := h k hkm
    rw [Qform_col_top p hd hkm, Qform_col_top p he hkm, hme] at hk'
    have := mul_left_cancel₀ hcoef hk'
    simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
    linear_combination this)
  exact sub_eq_zero.mp this

/-- **Sparse covariance recovery.** The covariance diagonal locates the deepest nonzero
entry. Its column above the diagonal then determines the vector up to sign. If the diagonal
vanishes, the vector is zero and no column is needed. This includes the empty vector. -/
lemma eq_or_eq_neg_of_Qform_sparse {p : K} (hp0 : 0 < p) (hp1 : p < 1) {d e : Fin n → K}
    (hdiag : ∀ k : Fin n, Qform p d d k.val k.val = Qform p e e k.val k.val)
    (hcol : ∀ m : Fin n, Qform p d d m.val m.val ≠ 0 →
      (∀ j : Fin n, m < j → Qform p d d j.val j.val = 0) →
      ∀ k : Fin n, k < m → Qform p d d k.val m.val = Qform p e e k.val m.val) :
    d = e ∨ d = -e := by
  by_cases hd : d = 0
  · left
    subst hd
    have : e = 0 := eq_zero_of_Qform_diag hp0 hp1 (fun k => by
      rw [← hdiag k]; unfold Qform; simp)
    rw [this]
  by_cases he : e = 0
  · exfalso
    subst he
    exact hd (eq_zero_of_Qform_diag hp0 hp1 (fun k => by rw [hdiag k]; unfold Qform; simp))
  obtain ⟨md, hdm, hd'⟩ := exists_last_ne_zero hd
  obtain ⟨me, hem, he'⟩ := exists_last_ne_zero he
  have hmm : md = me := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 := Qform_diag_beyond p hd' hlt
      rw [hdiag me] at h1
      exact Qform_diag_top_ne_zero hp0 hp1 hem he' h1
    · have h1 := Qform_diag_beyond p he' hgt
      rw [← hdiag md] at h1
      exact Qform_diag_top_ne_zero hp0 hp1 hdm hd' h1
  subst hmm
  have hsq : d md ^ 2 = e md ^ 2 := by
    have h1 := hdiag md
    rw [Qform_diag_top p hd', Qform_diag_top p he'] at h1
    exact mul_right_cancel₀ (diag_factor_pos hp0 hp1 md.val).ne' h1
  have hselected := hcol md (Qform_diag_top_ne_zero hp0 hp1 hdm hd')
    (fun j hj => Qform_diag_beyond p hd' hj)
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hpos | hneg
  · left
    exact eq_of_Qform_col hp0 hp1 hdm hpos.symm hd' he' (fun k hk => hselected k hk)
  · right
    have hneg' : (-e) md = d md := by simp [hneg]
    have := eq_of_Qform_col hp0 hp1 hdm hneg' hd' (fun j hj => by simp [he' j hj])
      (fun k hk => by rw [Qform_neg]; exact hselected k hk)
    exact this


/-- **The covariance form determines a vector up to sign** when `0 < p < 1`.
The sparse theorem shows that the full array is more information than is needed. -/
lemma eq_or_eq_neg_of_Qform {p : K} (hp0 : 0 < p) (hp1 : p < 1) {d e : Fin n → K}
    (h : ∀ k l : Fin n, Qform p d d k.val l.val = Qform p e e k.val l.val) : d = e ∨ d = -e := by
  exact eq_or_eq_neg_of_Qform_sparse hp0 hp1 (fun k => h k k)
    (fun m _ _ k _ => h k m)

end LossyShell
