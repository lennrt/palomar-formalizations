/-
Paper: Periodic Signings of C_n(1,2): An Exact Band Edge and Short-Period Classification
Formalization: Lennart Rudolph, with the automated assistants Sol (OpenAI
Codex) and Fable (Anthropic Claude)
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892995
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import ArithmeticAndMonotonicity
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# The period-eight signing of `C_n(1,2)` and the refutation of Suvagiya's Conjecture 3

This module carries the paper's finite, purely algebraic refutation certificate.
The signed adjacency matrix of the period-`8` flux word is exhibited as a `±1`
signing of `C_n(1,2)`; an exact rational sum-of-squares window certificate bounds
its Rayleigh quotient by `1397/500`; and `1397/500` is shown to be strictly below
the conjectured minimum `ρ₋(n)` for every `n ≥ 32`.
-/

namespace PalomarSignedCirculantSource

noncomputable section

set_option maxHeartbeats 2000000

/-- The period-8 triangle-flux word (+1,−1,+1,−1,−1,+1,−1,+1): −1 exactly at
residues 1, 3, 4, 6. -/
def fluxWord (i : ZMod 8) : ℤ :=
  if i.val = 1 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 6 then -1 else 1

/-- The step-2 sign at vertex `i` of `C_n(1,2)`, read through the reduction
`ZMod n → ZMod 8`. -/
def stepTwoSign (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) : ℤ :=
  fluxWord (ZMod.castHom hdvd (ZMod 8) i)

/-- The signed adjacency matrix of `C_n(1,2)`: every step-1 edge positive,
the step-2 edge starting at `i` signed by `stepTwoSign`. -/
def signedAdjacency (n : ℕ) (hdvd : 8 ∣ n) : Matrix (ZMod n) (ZMod n) ℝ :=
  fun i j =>
    (if j = i + 1 ∨ i = j + 1 then 1 else 0) +
    (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) else 0) +
    (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) else 0)

/-- `A` is a ±1 signing of the circulant graph `C_n(1,2)`. -/
def IsCirculantSigning (n : ℕ) (A : Matrix (ZMod n) (ZMod n) ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧
  (∀ i j, (SimpleGraph.circulantGraph {(1 : ZMod n), 2}).Adj i j →
    A i j = 1 ∨ A i j = -1) ∧
  (∀ i j, ¬ (SimpleGraph.circulantGraph {(1 : ZMod n), 2}).Adj i j → A i j = 0)

/-- Suvagiya's twisted-class spectral radius `ρ₋(n)`. -/
noncomputable def rhoMinus (n : ℕ) : ℝ :=
  2 * Real.sqrt (Real.cos (Real.pi / n) ^ 2 + Real.cos (2 * Real.pi / n) ^ 2)

/-! ## Elementary arithmetic in `ZMod n` for `8 ∣ n` -/

private lemma one_ne_zero_aux (n : ℕ) (hdvd : 8 ∣ n) : (1 : ZMod n) ≠ 0 := by
  intro h
  have h8 := congrArg (ZMod.castHom hdvd (ZMod 8)) h
  rw [map_one, map_zero] at h8
  exact absurd h8 (by decide)

private lemma two_ne_zero_aux (n : ℕ) (hdvd : 8 ∣ n) : (2 : ZMod n) ≠ 0 := by
  intro h
  have h8 := congrArg (ZMod.castHom hdvd (ZMod 8)) h
  rw [map_zero, map_ofNat] at h8
  exact absurd h8 (by decide)

private lemma three_ne_zero_aux (n : ℕ) (hdvd : 8 ∣ n) : (3 : ZMod n) ≠ 0 := by
  intro h
  have h8 := congrArg (ZMod.castHom hdvd (ZMod 8)) h
  rw [map_zero, map_ofNat] at h8
  exact absurd h8 (by decide)

private lemma four_ne_zero_aux (n : ℕ) (hdvd : 8 ∣ n) : (4 : ZMod n) ≠ 0 := by
  intro h
  have h8 := congrArg (ZMod.castHom hdvd (ZMod 8)) h
  rw [map_zero, map_ofNat] at h8
  exact absurd h8 (by decide)

/-! ## The signing property -/

private lemma fluxWord_eq_one_or_neg_one (m : ZMod 8) : fluxWord m = 1 ∨ fluxWord m = -1 := by
  unfold fluxWord
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

private lemma stepTwoSign_eq_one_or_neg_one (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) :
    stepTwoSign n hdvd i = 1 ∨ stepTwoSign n hdvd i = -1 :=
  fluxWord_eq_one_or_neg_one _

private lemma signedAdjacency_apply (n : ℕ) (hdvd : 8 ∣ n) (i j : ZMod n) :
    signedAdjacency n hdvd i j =
      (if j - i = 1 ∨ i - j = 1 then (1 : ℝ) else 0) +
      (if j - i = 2 then (stepTwoSign n hdvd i : ℝ) else 0) +
      (if i - j = 2 then (stepTwoSign n hdvd j : ℝ) else 0) := by
  simp only [signedAdjacency, sub_eq_iff_eq_add']

theorem signedAdjacency_isCirculantSigning_core (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) :
    IsCirculantSigning n (signedAdjacency n hdvd) := by
  have h1 : (1 : ZMod n) ≠ 0 := one_ne_zero_aux n hdvd
  have h2 : (2 : ZMod n) ≠ 0 := two_ne_zero_aux n hdvd
  have h3 : (3 : ZMod n) ≠ 0 := three_ne_zero_aux n hdvd
  have h4 : (4 : ZMod n) ≠ 0 := four_ne_zero_aux n hdvd
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [signedAdjacency_apply, signedAdjacency_apply]
    by_cases h : j - i = 1 ∨ i - j = 1
    · rw [if_pos h, if_pos (Or.symm h)]; ring
    · rw [if_neg h, if_neg (fun hc => h (Or.symm hc))]; ring
  · intro i j hadj
    rw [SimpleGraph.circulantGraph_adj] at hadj
    obtain ⟨hne, hmem⟩ := hadj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rw [signedAdjacency_apply]
    rcases hmem with (hd | hd) | (hd | hd)
    · have e1 : ¬ (j - i = 2) := fun h => h3 (by linear_combination -hd - h)
      have e2 : ¬ (i - j = 2) := fun h => h1 (by linear_combination hd - h)
      rw [if_pos (Or.inr hd), if_neg e1, if_neg e2]
      left; norm_num
    · have e0 : ¬ (j - i = 1 ∨ i - j = 1) := by
        rintro (h | h)
        · exact h3 (by linear_combination -hd - h)
        · exact h1 (by linear_combination h - hd)
      have e1 : ¬ (j - i = 2) := fun h => h4 (by linear_combination -hd - h)
      rw [if_neg e0, if_neg e1, if_pos hd]
      rcases stepTwoSign_eq_one_or_neg_one n hdvd j with hs | hs <;> rw [hs] <;> norm_num
    · have e1 : ¬ (j - i = 2) := fun h => h1 (by linear_combination hd - h)
      have e2 : ¬ (i - j = 2) := fun h => h3 (by linear_combination -hd - h)
      rw [if_pos (Or.inl hd), if_neg e1, if_neg e2]
      left; norm_num
    · have e0 : ¬ (j - i = 1 ∨ i - j = 1) := by
        rintro (h | h)
        · exact h1 (by linear_combination h - hd)
        · exact h3 (by linear_combination -hd - h)
      have e2 : ¬ (i - j = 2) := fun h => h4 (by linear_combination -hd - h)
      rw [if_neg e0, if_pos hd, if_neg e2]
      rcases stepTwoSign_eq_one_or_neg_one n hdvd i with hs | hs <;> rw [hs] <;> norm_num
  · intro i j hnadj
    rw [signedAdjacency_apply]
    by_cases hij : i = j
    · subst hij
      rw [sub_self,
        if_neg (show ¬ ((0 : ZMod n) = 1 ∨ (0 : ZMod n) = 1) by
          rintro (h | h) <;> exact h1 h.symm),
        if_neg (show ¬ ((0 : ZMod n) = 2) from fun h => h2 h.symm)]
      norm_num
    · rw [SimpleGraph.circulantGraph_adj, not_and] at hnadj
      have hmem := hnadj hij
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hmem
      obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hmem
      rw [if_neg (by rintro (h | h); exact hb1 h; exact ha1 h), if_neg hb2, if_neg ha2]
      norm_num

/-! ## The quadratic form of the signed adjacency matrix -/

private lemma entry_split (n : ℕ) (hdvd : 8 ∣ n) (i j : ZMod n) :
    signedAdjacency n hdvd i j =
      (if j = i + 1 then (1 : ℝ) else 0) + (if i = j + 1 then (1 : ℝ) else 0) +
      (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) else 0) +
      (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) else 0) := by
  have h2 : (2 : ZMod n) ≠ 0 := two_ne_zero_aux n hdvd
  unfold signedAdjacency
  by_cases hp : j = i + 1
  · have hq : ¬ (i = j + 1) := by
      intro h
      rw [hp] at h
      exact h2 (by linear_combination -h)
    rw [if_pos (Or.inl hp), if_pos hp, if_neg hq]
    ring
  · by_cases hq : i = j + 1
    · rw [if_pos (Or.inr hq), if_neg hp, if_pos hq]
      ring
    · rw [if_neg (not_or.mpr ⟨hp, hq⟩), if_neg hp, if_neg hq]
      ring

private lemma sum_shift (n : ℕ) [NeZero n] (c : ZMod n) (f : ZMod n → ℝ) :
    ∑ i : ZMod n, f (i + c) = ∑ i : ZMod n, f i :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

private lemma sum_ite_right (n : ℕ) [NeZero n] (c : ZMod n) (f : ZMod n → ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ j : ZMod n, (if j = i + c then f i j else 0) = ∑ i : ZMod n, f i (i + c) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp

private lemma sum_ite_left (n : ℕ) [NeZero n] (c : ZMod n) (f : ZMod n → ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ j : ZMod n, (if i = j + c then f i j else 0) =
      ∑ j : ZMod n, f (j + c) j := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp

theorem quadratic_form_eq (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) (v : ZMod n → ℝ) :
    ∑ i : ZMod n, ∑ j : ZMod n, v i * signedAdjacency n hdvd i j * v j =
      2 * ∑ i : ZMod n, v i * v (i + 1) +
        2 * ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2) := by
  have hpt : ∀ i j : ZMod n, v i * signedAdjacency n hdvd i j * v j =
      (if j = i + 1 then v i * v j else 0) + (if i = j + 1 then v i * v j else 0) +
      (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) * v i * v j else 0) +
      (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) * v i * v j else 0) := by
    intro i j
    rw [entry_split]
    split_ifs <;> ring
  calc ∑ i : ZMod n, ∑ j : ZMod n, v i * signedAdjacency n hdvd i j * v j
      = ∑ i : ZMod n, ∑ j : ZMod n,
          ((if j = i + 1 then v i * v j else 0) + (if i = j + 1 then v i * v j else 0) +
           (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) * v i * v j else 0) +
           (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) * v i * v j else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hpt i j))
    _ = (∑ i : ZMod n, ∑ j : ZMod n, (if j = i + 1 then v i * v j else 0)) +
        (∑ i : ZMod n, ∑ j : ZMod n, (if i = j + 1 then v i * v j else 0)) +
        (∑ i : ZMod n, ∑ j : ZMod n,
          (if j = i + 2 then (stepTwoSign n hdvd i : ℝ) * v i * v j else 0)) +
        (∑ i : ZMod n, ∑ j : ZMod n,
          (if i = j + 2 then (stepTwoSign n hdvd j : ℝ) * v i * v j else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ = (∑ i : ZMod n, v i * v (i + 1)) + (∑ j : ZMod n, v (j + 1) * v j) +
        (∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2)) +
        (∑ j : ZMod n, (stepTwoSign n hdvd j : ℝ) * v (j + 2) * v j) := by
        rw [sum_ite_right n 1 (fun i j => v i * v j), sum_ite_left n 1 (fun i j => v i * v j),
          sum_ite_right n 2 (fun i j => (stepTwoSign n hdvd i : ℝ) * v i * v j),
          sum_ite_left n 2 (fun i j => (stepTwoSign n hdvd j : ℝ) * v i * v j)]
    _ = 2 * ∑ i : ZMod n, v i * v (i + 1) +
          2 * ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2) := by
        have e1 : ∑ j : ZMod n, v (j + 1) * v j = ∑ i : ZMod n, v i * v (i + 1) :=
          Finset.sum_congr rfl (fun j _ => mul_comm _ _)
        have e2 : ∑ j : ZMod n, (stepTwoSign n hdvd j : ℝ) * v (j + 2) * v j =
            ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2) :=
          Finset.sum_congr rfl (fun j _ => by ring)
        rw [e1, e2]
        ring

/-! ## The exact rational sum-of-squares window certificates -/

def upperD1 : ZMod 8 → ℚ
  | 0 => (2039163401169 / 1000000000000 : ℚ)
  | 1 => (4250429950259 / 3000000000000 : ℚ)
  | 2 => (1709084882213 / 3000000000000 : ℚ)
  | 3 => (6204384586663 / 3000000000000 : ℚ)
  | 4 => (215447098759 / 300000000000 : ℚ)
  | 5 => (337079313107 / 187500000000 : ℚ)
  | 6 => (1387757536539 / 1000000000000 : ℚ)
  | 7 => (4161282092509 / 3000000000000 : ℚ)

def upperP : ZMod 8 → ℚ
  | 0 => (-1156563300869 / 2039163401169 : ℚ)
  | 1 => (-4701609189309 / 4250429950259 : ℚ)
  | 2 => (318682039875 / 1709084882213 : ℚ)
  | 3 => (-2440508874144 / 6204384586663 : ℚ)
  | 4 => (-3639771091269 / 4308941975180 : ℚ)
  | 5 => (-931082713965 / 10786538019424 : ℚ)
  | 6 => (-2172647539045 / 2775515073078 : ℚ)
  | 7 => (-1302915676431 / 8322564185018 : ℚ)

def upperQ : ZMod 8 → ℚ
  | 0 => (-1000000000000 / 2039163401169 : ℚ)
  | 1 => (3000000000000 / 4250429950259 : ℚ)
  | 2 => (-3000000000000 / 1709084882213 : ℚ)
  | 3 => (3000000000000 / 6204384586663 : ℚ)
  | 4 => (300000000000 / 215447098759 : ℚ)
  | 5 => (-187500000000 / 337079313107 : ℚ)
  | 6 => (1000000000000 / 1387757536539 : ℚ)
  | 7 => (-3000000000000 / 4161282092509 : ℚ)

def upperD2 : ZMod 8 → ℚ
  | 0 => (67515686424974072507 / 509790850292250000000000 : ℚ)
  | 1 => (2844671912021346781033 / 12751289850777000000000000 : ℚ)
  | 2 => (265910866318523480653 / 2563627323319500000000000 : ℚ)
  | 3 => (2160282990154777299859 / 18613153759989000000000000 : ℚ)
  | 4 => (4429142011219169196839 / 25853651851080000000000000 : ℚ)
  | 5 => (2161302732966896292189 / 21573076038848000000000000 : ℚ)
  | 6 => (894957609578243467099 / 5551030146156000000000000 : ℚ)
  | 7 => (1694983608277318479849 / 16645128370036000000000000 : ℚ)

def upperR : ZMod 8 → ℚ
  | 0 => (56426441588410967407 / 270062745699896290028 : ℚ)
  | 1 => (-997969744332904577625 / 2844671912021346781033 : ℚ)
  | 2 => (-85852653910259399664 / 265910866318523480653 : ℚ)
  | 3 => (-714617463048986854653 / 4320565980309554599718 : ℚ)
  | 4 => (-3043914897697930611300 / 4429142011219169196839 : ℚ)
  | 5 => (103815938882008410080 / 2161302732966896292189 : ℚ)
  | 6 => (-314368438047077591794 / 894957609578243467099 : ℚ)
  | 7 => (184888139073832361284 / 1694983608277318479849 : ℚ)

def upperD3 : ZMod 8 → ℚ
  | 0 => (19241878259234664835033505557 / 162037647419937774016800000000000 : ℚ)
  | 1 => (41695506177754748003665489999 / 341360629442561613723960000000000 : ℚ)
  | 2 => (317131283479561440357615014401 / 797732598955570441959000000000000 : ℚ)
  | 3 => (621884896911472816986428358301 / 5184679176371465519661600000000000 : ℚ)
  | 4 => (944112408937380838760038657427 / 4429142011219169196839000000000000 : ℚ)
  | 5 => (142000052555725273098990549001 / 1080651366483448146094500000000000 : ℚ)
  | 6 => (354903056018592583363622811317 / 2684872828734730401297000000000000 : ℚ)
  | 7 => (42506042081877903387705259273 / 282497268046219746641500000000000 : ℚ)

def lowerD1 : ZMod 8 → ℚ
  | 0 => (215447098759 / 300000000000 : ℚ)
  | 1 => (337079313107 / 187500000000 : ℚ)
  | 2 => (1387757536539 / 1000000000000 : ℚ)
  | 3 => (4161282092509 / 3000000000000 : ℚ)
  | 4 => (2039163401169 / 1000000000000 : ℚ)
  | 5 => (4250429950259 / 3000000000000 : ℚ)
  | 6 => (1709084882213 / 3000000000000 : ℚ)
  | 7 => (6204384586663 / 3000000000000 : ℚ)

def lowerP : ZMod 8 → ℚ
  | 0 => (3639771091269 / 4308941975180 : ℚ)
  | 1 => (931082713965 / 10786538019424 : ℚ)
  | 2 => (2172647539045 / 2775515073078 : ℚ)
  | 3 => (1302915676431 / 8322564185018 : ℚ)
  | 4 => (1156563300869 / 2039163401169 : ℚ)
  | 5 => (4701609189309 / 4250429950259 : ℚ)
  | 6 => (-318682039875 / 1709084882213 : ℚ)
  | 7 => (2440508874144 / 6204384586663 : ℚ)

def lowerQ : ZMod 8 → ℚ
  | 0 => (300000000000 / 215447098759 : ℚ)
  | 1 => (-187500000000 / 337079313107 : ℚ)
  | 2 => (1000000000000 / 1387757536539 : ℚ)
  | 3 => (-3000000000000 / 4161282092509 : ℚ)
  | 4 => (-1000000000000 / 2039163401169 : ℚ)
  | 5 => (3000000000000 / 4250429950259 : ℚ)
  | 6 => (-3000000000000 / 1709084882213 : ℚ)
  | 7 => (3000000000000 / 6204384586663 : ℚ)

def lowerD2 : ZMod 8 → ℚ
  | 0 => (4429142011219169196839 / 25853651851080000000000000 : ℚ)
  | 1 => (2161302732966896292189 / 21573076038848000000000000 : ℚ)
  | 2 => (894957609578243467099 / 5551030146156000000000000 : ℚ)
  | 3 => (1694983608277318479849 / 16645128370036000000000000 : ℚ)
  | 4 => (67515686424974072507 / 509790850292250000000000 : ℚ)
  | 5 => (2844671912021346781033 / 12751289850777000000000000 : ℚ)
  | 6 => (265910866318523480653 / 2563627323319500000000000 : ℚ)
  | 7 => (2160282990154777299859 / 18613153759989000000000000 : ℚ)

def lowerR : ZMod 8 → ℚ
  | 0 => (3043914897697930611300 / 4429142011219169196839 : ℚ)
  | 1 => (-103815938882008410080 / 2161302732966896292189 : ℚ)
  | 2 => (314368438047077591794 / 894957609578243467099 : ℚ)
  | 3 => (-184888139073832361284 / 1694983608277318479849 : ℚ)
  | 4 => (-56426441588410967407 / 270062745699896290028 : ℚ)
  | 5 => (997969744332904577625 / 2844671912021346781033 : ℚ)
  | 6 => (85852653910259399664 / 265910866318523480653 : ℚ)
  | 7 => (714617463048986854653 / 4320565980309554599718 : ℚ)

def lowerD3 : ZMod 8 → ℚ
  | 0 => (944112408937380838760038657427 / 4429142011219169196839000000000000 : ℚ)
  | 1 => (142000052555725273098990549001 / 1080651366483448146094500000000000 : ℚ)
  | 2 => (354903056018592583363622811317 / 2684872828734730401297000000000000 : ℚ)
  | 3 => (42506042081877903387705259273 / 282497268046219746641500000000000 : ℚ)
  | 4 => (19241878259234664835033505557 / 162037647419937774016800000000000 : ℚ)
  | 5 => (41695506177754748003665489999 / 341360629442561613723960000000000 : ℚ)
  | 6 => (317131283479561440357615014401 / 797732598955570441959000000000000 : ℚ)
  | 7 => (621884896911472816986428358301 / 5184679176371465519661600000000000 : ℚ)

private def uA (m : ZMod 8) : ℚ := upperD1 m
private def uB (m : ZMod 8) : ℚ := upperD1 m * upperP m ^ 2 + upperD2 m
private def uC (m : ZMod 8) : ℚ :=
  upperD1 m * upperQ m ^ 2 + upperD2 m * upperR m ^ 2 + upperD3 m
private def uD (m : ZMod 8) : ℚ := 2 * upperD1 m * upperP m
private def uE (m : ZMod 8) : ℚ :=
  2 * (upperD1 m * upperP m * upperQ m + upperD2 m * upperR m)
private def uF (m : ZMod 8) : ℚ := 2 * upperD1 m * upperQ m

private def lA (m : ZMod 8) : ℚ := lowerD1 m
private def lB (m : ZMod 8) : ℚ := lowerD1 m * lowerP m ^ 2 + lowerD2 m
private def lC (m : ZMod 8) : ℚ :=
  lowerD1 m * lowerQ m ^ 2 + lowerD2 m * lowerR m ^ 2 + lowerD3 m
private def lD (m : ZMod 8) : ℚ := 2 * lowerD1 m * lowerP m
private def lE (m : ZMod 8) : ℚ :=
  2 * (lowerD1 m * lowerP m * lowerQ m + lowerD2 m * lowerR m)
private def lF (m : ZMod 8) : ℚ := 2 * lowerD1 m * lowerQ m

private lemma zmod8_cases : ∀ m : ZMod 8,
    m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by decide

private lemma fluxWord_zero : fluxWord 0 = 1 := by decide
private lemma fluxWord_one : fluxWord 1 = -1 := by decide
private lemma fluxWord_two : fluxWord 2 = 1 := by decide
private lemma fluxWord_three : fluxWord 3 = -1 := by decide
private lemma fluxWord_four : fluxWord 4 = -1 := by decide
private lemma fluxWord_five : fluxWord 5 = 1 := by decide
private lemma fluxWord_six : fluxWord 6 = -1 := by decide
private lemma fluxWord_seven : fluxWord 7 = 1 := by decide

private lemma uA_sum (m : ZMod 8) : uA m + uB (m - 1) + uC (m - 2) = 1397 / 500 := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [uA, uB, uC, upperD1, upperP, upperQ, upperD2, upperR, upperD3,
      show ((0:ZMod 8) - 1) = 7 by decide, show ((1:ZMod 8) - 1) = 0 by decide,
      show ((2:ZMod 8) - 1) = 1 by decide, show ((3:ZMod 8) - 1) = 2 by decide,
      show ((4:ZMod 8) - 1) = 3 by decide, show ((5:ZMod 8) - 1) = 4 by decide,
      show ((6:ZMod 8) - 1) = 5 by decide, show ((7:ZMod 8) - 1) = 6 by decide,
      show ((0:ZMod 8) - 2) = 6 by decide, show ((1:ZMod 8) - 2) = 7 by decide,
      show ((2:ZMod 8) - 2) = 0 by decide, show ((3:ZMod 8) - 2) = 1 by decide,
      show ((4:ZMod 8) - 2) = 2 by decide, show ((5:ZMod 8) - 2) = 3 by decide,
      show ((6:ZMod 8) - 2) = 4 by decide, show ((7:ZMod 8) - 2) = 5 by decide]

private lemma uD_sum (m : ZMod 8) : uD m + uE (m - 1) = -2 * 1 := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [uD, uE, upperD1, upperP, upperQ, upperD2, upperR, upperD3,
      show ((0:ZMod 8) - 1) = 7 by decide, show ((1:ZMod 8) - 1) = 0 by decide,
      show ((2:ZMod 8) - 1) = 1 by decide, show ((3:ZMod 8) - 1) = 2 by decide,
      show ((4:ZMod 8) - 1) = 3 by decide, show ((5:ZMod 8) - 1) = 4 by decide,
      show ((6:ZMod 8) - 1) = 5 by decide, show ((7:ZMod 8) - 1) = 6 by decide]

private lemma uF_val (m : ZMod 8) : uF m = -2 * 1 * (fluxWord m : ℚ) := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [uF, upperD1, upperQ, fluxWord_zero, fluxWord_one, fluxWord_two,
      fluxWord_three, fluxWord_four, fluxWord_five, fluxWord_six, fluxWord_seven]

private lemma lA_sum (m : ZMod 8) : lA m + lB (m - 1) + lC (m - 2) = 1397 / 500 := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [lA, lB, lC, lowerD1, lowerP, lowerQ, lowerD2, lowerR, lowerD3,
      show ((0:ZMod 8) - 1) = 7 by decide, show ((1:ZMod 8) - 1) = 0 by decide,
      show ((2:ZMod 8) - 1) = 1 by decide, show ((3:ZMod 8) - 1) = 2 by decide,
      show ((4:ZMod 8) - 1) = 3 by decide, show ((5:ZMod 8) - 1) = 4 by decide,
      show ((6:ZMod 8) - 1) = 5 by decide, show ((7:ZMod 8) - 1) = 6 by decide,
      show ((0:ZMod 8) - 2) = 6 by decide, show ((1:ZMod 8) - 2) = 7 by decide,
      show ((2:ZMod 8) - 2) = 0 by decide, show ((3:ZMod 8) - 2) = 1 by decide,
      show ((4:ZMod 8) - 2) = 2 by decide, show ((5:ZMod 8) - 2) = 3 by decide,
      show ((6:ZMod 8) - 2) = 4 by decide, show ((7:ZMod 8) - 2) = 5 by decide]

private lemma lD_sum (m : ZMod 8) : lD m + lE (m - 1) = -2 * (-1) := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [lD, lE, lowerD1, lowerP, lowerQ, lowerD2, lowerR, lowerD3,
      show ((0:ZMod 8) - 1) = 7 by decide, show ((1:ZMod 8) - 1) = 0 by decide,
      show ((2:ZMod 8) - 1) = 1 by decide, show ((3:ZMod 8) - 1) = 2 by decide,
      show ((4:ZMod 8) - 1) = 3 by decide, show ((5:ZMod 8) - 1) = 4 by decide,
      show ((6:ZMod 8) - 1) = 5 by decide, show ((7:ZMod 8) - 1) = 6 by decide]

private lemma lF_val (m : ZMod 8) : lF m = -2 * (-1) * (fluxWord m : ℚ) := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [lF, lowerD1, lowerQ, fluxWord_zero, fluxWord_one, fluxWord_two,
      fluxWord_three, fluxWord_four, fluxWord_five, fluxWord_six, fluxWord_seven]

private lemma upperD1_nonneg (m : ZMod 8) : 0 ≤ upperD1 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [upperD1]

private lemma upperD2_nonneg (m : ZMod 8) : 0 ≤ upperD2 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [upperD2]

private lemma upperD3_nonneg (m : ZMod 8) : 0 ≤ upperD3 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [upperD3]

private lemma lowerD1_nonneg (m : ZMod 8) : 0 ≤ lowerD1 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lowerD1]

private lemma lowerD2_nonneg (m : ZMod 8) : 0 ≤ lowerD2 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lowerD2]

private lemma lowerD3_nonneg (m : ZMod 8) : 0 ≤ lowerD3 m := by
  rcases zmod8_cases m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lowerD3]

private lemma upper_window_nonneg (m : ZMod 8) (x y z : ℝ) :
    0 ≤ (uA m : ℝ) * x ^ 2 + (uB m : ℝ) * y ^ 2 + (uC m : ℝ) * z ^ 2 +
      (uD m : ℝ) * (x * y) + (uE m : ℝ) * (y * z) + (uF m : ℝ) * (x * z) := by
  have h1 : (0:ℝ) ≤ (upperD1 m : ℝ) := by exact_mod_cast upperD1_nonneg m
  have h2 : (0:ℝ) ≤ (upperD2 m : ℝ) := by exact_mod_cast upperD2_nonneg m
  have h3 : (0:ℝ) ≤ (upperD3 m : ℝ) := by exact_mod_cast upperD3_nonneg m
  have hexp : (uA m : ℝ) * x ^ 2 + (uB m : ℝ) * y ^ 2 + (uC m : ℝ) * z ^ 2 +
      (uD m : ℝ) * (x * y) + (uE m : ℝ) * (y * z) + (uF m : ℝ) * (x * z) =
      (upperD1 m : ℝ) * (x + (upperP m : ℝ) * y + (upperQ m : ℝ) * z) ^ 2 +
        (upperD2 m : ℝ) * (y + (upperR m : ℝ) * z) ^ 2 + (upperD3 m : ℝ) * z ^ 2 := by
    simp only [uA, uB, uC, uD, uE, uF]
    push_cast
    ring
  rw [hexp]
  have t1 := mul_nonneg h1 (sq_nonneg (x + (upperP m : ℝ) * y + (upperQ m : ℝ) * z))
  have t2 := mul_nonneg h2 (sq_nonneg (y + (upperR m : ℝ) * z))
  have t3 := mul_nonneg h3 (sq_nonneg z)
  linarith

private lemma lower_window_nonneg (m : ZMod 8) (x y z : ℝ) :
    0 ≤ (lA m : ℝ) * x ^ 2 + (lB m : ℝ) * y ^ 2 + (lC m : ℝ) * z ^ 2 +
      (lD m : ℝ) * (x * y) + (lE m : ℝ) * (y * z) + (lF m : ℝ) * (x * z) := by
  have h1 : (0:ℝ) ≤ (lowerD1 m : ℝ) := by exact_mod_cast lowerD1_nonneg m
  have h2 : (0:ℝ) ≤ (lowerD2 m : ℝ) := by exact_mod_cast lowerD2_nonneg m
  have h3 : (0:ℝ) ≤ (lowerD3 m : ℝ) := by exact_mod_cast lowerD3_nonneg m
  have hexp : (lA m : ℝ) * x ^ 2 + (lB m : ℝ) * y ^ 2 + (lC m : ℝ) * z ^ 2 +
      (lD m : ℝ) * (x * y) + (lE m : ℝ) * (y * z) + (lF m : ℝ) * (x * z) =
      (lowerD1 m : ℝ) * (x + (lowerP m : ℝ) * y + (lowerQ m : ℝ) * z) ^ 2 +
        (lowerD2 m : ℝ) * (y + (lowerR m : ℝ) * z) ^ 2 + (lowerD3 m : ℝ) * z ^ 2 := by
    simp only [lA, lB, lC, lD, lE, lF]
    push_cast
    ring
  rw [hexp]
  have t1 := mul_nonneg h1 (sq_nonneg (x + (lowerP m : ℝ) * y + (lowerQ m : ℝ) * z))
  have t2 := mul_nonneg h2 (sq_nonneg (y + (lowerR m : ℝ) * z))
  have t3 := mul_nonneg h3 (sq_nonneg z)
  linarith

/-! ## Assembling the window certificates into a Rayleigh bound -/

private def resid (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) : ZMod 8 :=
  ZMod.castHom hdvd (ZMod 8) i

private lemma stepTwoSign_eq_fluxWord_resid (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) :
    stepTwoSign n hdvd i = fluxWord (resid n hdvd i) := rfl

private lemma resid_add_one (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) :
    resid n hdvd (i + 1) = resid n hdvd i + 1 := by
  unfold resid
  rw [map_add, map_one]

private lemma resid_add_two (n : ℕ) (hdvd : 8 ∣ n) (i : ZMod n) :
    resid n hdvd (i + 2) = resid n hdvd i + 2 := by
  unfold resid
  rw [map_add, map_ofNat]

private lemma window_rayleigh (n : ℕ) [NeZero n] (hdvd : 8 ∣ n)
    (A B C D E F : ZMod 8 → ℚ) (σ : ℚ)
    (hAsum : ∀ m : ZMod 8, A m + B (m - 1) + C (m - 2) = 1397 / 500)
    (hDsum : ∀ m : ZMod 8, D m + E (m - 1) = -2 * σ)
    (hFval : ∀ m : ZMod 8, F m = -2 * σ * (fluxWord m : ℚ))
    (hnn : ∀ (m : ZMod 8) (x y z : ℝ),
      0 ≤ (A m : ℝ) * x ^ 2 + (B m : ℝ) * y ^ 2 + (C m : ℝ) * z ^ 2 +
        (D m : ℝ) * (x * y) + (E m : ℝ) * (y * z) + (F m : ℝ) * (x * z))
    (v : ZMod n → ℝ) :
    (σ : ℝ) * (2 * ∑ i : ZMod n, v i * v (i + 1) +
        2 * ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2)) ≤
      1397 / 500 * ∑ i : ZMod n, v i ^ 2 := by
  have hnonneg : (0:ℝ) ≤ ∑ i : ZMod n,
      ((A (resid n hdvd i) : ℝ) * v i ^ 2 + (B (resid n hdvd i) : ℝ) * v (i + 1) ^ 2 +
        (C (resid n hdvd i) : ℝ) * v (i + 2) ^ 2 +
        (D (resid n hdvd i) : ℝ) * (v i * v (i + 1)) +
        (E (resid n hdvd i) : ℝ) * (v (i + 1) * v (i + 2)) +
        (F (resid n hdvd i) : ℝ) * (v i * v (i + 2))) :=
    Finset.sum_nonneg (fun i _ => hnn _ _ _ _)
  have hB : ∑ i : ZMod n, (B (resid n hdvd i) : ℝ) * v (i + 1) ^ 2 =
      ∑ i : ZMod n, (B (resid n hdvd i - 1) : ℝ) * v i ^ 2 := by
    rw [← sum_shift n 1 (fun i => (B (resid n hdvd i - 1) : ℝ) * v i ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [resid_add_one, add_sub_cancel_right]
  have hC : ∑ i : ZMod n, (C (resid n hdvd i) : ℝ) * v (i + 2) ^ 2 =
      ∑ i : ZMod n, (C (resid n hdvd i - 2) : ℝ) * v i ^ 2 := by
    rw [← sum_shift n 2 (fun i => (C (resid n hdvd i - 2) : ℝ) * v i ^ 2)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [resid_add_two, add_sub_cancel_right]
  have hE : ∑ i : ZMod n, (E (resid n hdvd i) : ℝ) * (v (i + 1) * v (i + 2)) =
      ∑ i : ZMod n, (E (resid n hdvd i - 1) : ℝ) * (v i * v (i + 1)) := by
    rw [← sum_shift n 1 (fun i => (E (resid n hdvd i - 1) : ℝ) * (v i * v (i + 1)))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [resid_add_one, add_sub_cancel_right, add_assoc]
    norm_num
  have key : ∑ i : ZMod n,
      ((A (resid n hdvd i) : ℝ) * v i ^ 2 + (B (resid n hdvd i) : ℝ) * v (i + 1) ^ 2 +
        (C (resid n hdvd i) : ℝ) * v (i + 2) ^ 2 +
        (D (resid n hdvd i) : ℝ) * (v i * v (i + 1)) +
        (E (resid n hdvd i) : ℝ) * (v (i + 1) * v (i + 2)) +
        (F (resid n hdvd i) : ℝ) * (v i * v (i + 2))) =
      1397 / 500 * (∑ i : ZMod n, v i ^ 2) -
        (σ : ℝ) * (2 * ∑ i : ZMod n, v i * v (i + 1) +
          2 * ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2)) := by
    calc ∑ i : ZMod n,
        ((A (resid n hdvd i) : ℝ) * v i ^ 2 + (B (resid n hdvd i) : ℝ) * v (i + 1) ^ 2 +
          (C (resid n hdvd i) : ℝ) * v (i + 2) ^ 2 +
          (D (resid n hdvd i) : ℝ) * (v i * v (i + 1)) +
          (E (resid n hdvd i) : ℝ) * (v (i + 1) * v (i + 2)) +
          (F (resid n hdvd i) : ℝ) * (v i * v (i + 2)))
        = (∑ i : ZMod n, (A (resid n hdvd i) : ℝ) * v i ^ 2) +
          (∑ i : ZMod n, (B (resid n hdvd i) : ℝ) * v (i + 1) ^ 2) +
          (∑ i : ZMod n, (C (resid n hdvd i) : ℝ) * v (i + 2) ^ 2) +
          (∑ i : ZMod n, (D (resid n hdvd i) : ℝ) * (v i * v (i + 1))) +
          (∑ i : ZMod n, (E (resid n hdvd i) : ℝ) * (v (i + 1) * v (i + 2))) +
          (∑ i : ZMod n, (F (resid n hdvd i) : ℝ) * (v i * v (i + 2))) := by
          simp only [Finset.sum_add_distrib]
      _ = (∑ i : ZMod n, (A (resid n hdvd i) : ℝ) * v i ^ 2) +
          (∑ i : ZMod n, (B (resid n hdvd i - 1) : ℝ) * v i ^ 2) +
          (∑ i : ZMod n, (C (resid n hdvd i - 2) : ℝ) * v i ^ 2) +
          (∑ i : ZMod n, (D (resid n hdvd i) : ℝ) * (v i * v (i + 1))) +
          (∑ i : ZMod n, (E (resid n hdvd i - 1) : ℝ) * (v i * v (i + 1))) +
          (∑ i : ZMod n, (F (resid n hdvd i) : ℝ) * (v i * v (i + 2))) := by
          rw [hB, hC, hE]
      _ = ∑ i : ZMod n,
          ((A (resid n hdvd i) : ℝ) * v i ^ 2 + (B (resid n hdvd i - 1) : ℝ) * v i ^ 2 +
            (C (resid n hdvd i - 2) : ℝ) * v i ^ 2 +
            (D (resid n hdvd i) : ℝ) * (v i * v (i + 1)) +
            (E (resid n hdvd i - 1) : ℝ) * (v i * v (i + 1)) +
            (F (resid n hdvd i) : ℝ) * (v i * v (i + 2))) := by
          simp only [Finset.sum_add_distrib]
      _ = ∑ i : ZMod n,
          ((1397 / 500 : ℝ) * v i ^ 2 + (-2 * (σ : ℝ)) * (v i * v (i + 1)) +
            (-2 * (σ : ℝ)) * ((stepTwoSign n hdvd i : ℝ) * v i * v (i + 2))) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have ha : (A (resid n hdvd i) : ℝ) + (B (resid n hdvd i - 1) : ℝ) +
              (C (resid n hdvd i - 2) : ℝ) = 1397 / 500 := by
            have h := congrArg (fun q : ℚ => (q : ℝ)) (hAsum (resid n hdvd i))
            simp only at h
            push_cast at h
            linarith
          have hd : (D (resid n hdvd i) : ℝ) + (E (resid n hdvd i - 1) : ℝ) = -2 * (σ : ℝ) := by
            have h := congrArg (fun q : ℚ => (q : ℝ)) (hDsum (resid n hdvd i))
            simp only at h
            push_cast at h
            linarith
          have hf : (F (resid n hdvd i) : ℝ) =
              -2 * (σ : ℝ) * ((fluxWord (resid n hdvd i) : ℤ) : ℝ) := by
            have h := congrArg (fun q : ℚ => (q : ℝ)) (hFval (resid n hdvd i))
            simp only at h
            push_cast at h
            linarith
          rw [stepTwoSign_eq_fluxWord_resid]
          linear_combination (v i ^ 2) * ha + (v i * v (i + 1)) * hd +
            (v i * v (i + 2)) * hf
      _ = (∑ i : ZMod n, (1397 / 500 : ℝ) * v i ^ 2) +
          (∑ i : ZMod n, (-2 * (σ : ℝ)) * (v i * v (i + 1))) +
          (∑ i : ZMod n, (-2 * (σ : ℝ)) * ((stepTwoSign n hdvd i : ℝ) * v i * v (i + 2))) := by
          simp only [Finset.sum_add_distrib]
      _ = 1397 / 500 * (∑ i : ZMod n, v i ^ 2) -
            (σ : ℝ) * (2 * ∑ i : ZMod n, v i * v (i + 1) +
              2 * ∑ i : ZMod n, (stepTwoSign n hdvd i : ℝ) * v i * v (i + 2)) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          ring
  rw [key] at hnonneg
  linarith

theorem rayleigh_band_bound_core (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) (v : ZMod n → ℝ) :
    |∑ i : ZMod n, ∑ j : ZMod n, v i * signedAdjacency n hdvd i j * v j| ≤
      1397 / 500 * ∑ i : ZMod n, v i ^ 2 := by
  have hup := window_rayleigh n hdvd uA uB uC uD uE uF 1 uA_sum uD_sum uF_val
    upper_window_nonneg v
  have hlo := window_rayleigh n hdvd lA lB lC lD lE lF (-1) lA_sum lD_sum lF_val
    lower_window_nonneg v
  rw [quadratic_form_eq]
  rw [abs_le]
  constructor
  · push_cast at hlo
    linarith
  · push_cast at hup
    linarith

theorem eigenvalue_band_bound_core (n : ℕ) [NeZero n] (hdvd : 8 ∣ n) (μ : ℝ) (v : ZMod n → ℝ)
    (hv : v ≠ 0) (hev : (signedAdjacency n hdvd).mulVec v = μ • v) :
    |μ| ≤ 1397 / 500 := by
  have hrow : ∀ i : ZMod n, ∑ j : ZMod n, v i * signedAdjacency n hdvd i j * v j =
      v i * ((signedAdjacency n hdvd).mulVec v i) := by
    intro i
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hquad : ∑ i : ZMod n, ∑ j : ZMod n, v i * signedAdjacency n hdvd i j * v j =
      μ * ∑ i : ZMod n, v i ^ 2 := by
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => hrow i), hev]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by simp [Pi.smul_apply, smul_eq_mul]; ring)
  obtain ⟨i0, hi0⟩ : ∃ i : ZMod n, v i ≠ 0 := by
    by_contra hcon
    exact hv (funext fun i => not_not.mp (fun hne => hcon ⟨i, hne⟩))
  have hpos : (0:ℝ) < ∑ i : ZMod n, v i ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i0, Finset.mem_univ _, by positivity⟩
  have hb := rayleigh_band_bound_core n hdvd v
  rw [hquad, abs_mul, abs_of_pos hpos] at hb
  exact le_of_mul_le_mul_right (by linarith) hpos

/-! ## The conjectured minimum `ρ₋(n)` exceeds the certified band edge -/

theorem separator_lt_twisted_value_core (n : ℕ) (hn : 32 ≤ n) :
    (1397 / 500 : ℝ) < rhoMinus n := by
  have hpi := Real.pi_pos
  have hn' : (32 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0:ℝ) < (n : ℝ) := by linarith
  have ha1 : (0:ℝ) ≤ Real.pi / n := by positivity
  have ha2 : Real.pi / n ≤ Real.pi / 32 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    nlinarith
  have hb1 : (0:ℝ) ≤ 2 * Real.pi / n := by positivity
  have hb2 : 2 * Real.pi / n ≤ Real.pi / 16 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    nlinarith
  have hc1 : Real.cos (Real.pi / 32) ≤ Real.cos (Real.pi / n) :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha1 (by linarith) ha2
  have hc0 : (0:ℝ) ≤ Real.cos (Real.pi / 32) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hd1 : Real.cos (Real.pi / 16) ≤ Real.cos (2 * Real.pi / n) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hb1 (by linarith) hb2
  have hd0 : (0:ℝ) ≤ Real.cos (Real.pi / 16) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  have hsq1 : Real.cos (Real.pi / 32) ^ 2 ≤ Real.cos (Real.pi / n) ^ 2 := by nlinarith
  have hsq2 : Real.cos (Real.pi / 16) ^ 2 ≤ Real.cos (2 * Real.pi / n) ^ 2 := by nlinarith
  have hrad : (0:ℝ) ≤ Real.cos (Real.pi / n) ^ 2 + Real.cos (2 * Real.pi / n) ^ 2 := by
    positivity
  have hrho2 : rhoMinus n ^ 2 =
      4 * (Real.cos (Real.pi / n) ^ 2 + Real.cos (2 * Real.pi / n) ^ 2) := by
    unfold rhoMinus
    rw [mul_pow, Real.sq_sqrt hrad]
    norm_num
  have h32 : 4 * Real.cos (Real.pi / 32) ^ 2 = 2 + 2 * Real.cos (Real.pi / 16) := by
    rw [Real.cos_sq, show (2 : ℝ) * (Real.pi / 32) = Real.pi / 16 by ring]
    ring
  have h16 : 4 * Real.cos (Real.pi / 16) ^ 2 = 2 + 2 * Real.cos (Real.pi / 8) := by
    rw [Real.cos_sq, show (2 : ℝ) * (Real.pi / 16) = Real.pi / 8 by ring]
    ring
  have hcos8 : 2 * Real.cos (Real.pi / 8) = Real.sqrt (2 + Real.sqrt 2) := by
    rw [Real.cos_pi_div_eight]; ring
  have hcos16 : 2 * Real.cos (Real.pi / 16) =
      Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    rw [Real.cos_pi_div_sixteen]; ring
  have hbase : (4:ℝ) * (Real.cos (Real.pi / 32) ^ 2 + Real.cos (Real.pi / 16) ^ 2) =
      4 + Real.sqrt (2 + Real.sqrt 2) + Real.sqrt (2 + Real.sqrt (2 + Real.sqrt 2)) := by
    have hexp : (4:ℝ) * (Real.cos (Real.pi / 32) ^ 2 + Real.cos (Real.pi / 16) ^ 2) =
        4 * Real.cos (Real.pi / 32) ^ 2 + 4 * Real.cos (Real.pi / 16) ^ 2 := by ring
    rw [hexp, h32, h16]
    linarith [hcos8, hcos16]
  have hsep := SignedCirculantArithmetic.finite_separator_squared_lt_aux
  have htarget := SignedCirculantArithmetic.target_squared_lower
  have hlt : (1397 / 500 : ℝ) ^ 2 < rhoMinus n ^ 2 := by
    rw [hrho2]
    linarith
  have hrhononneg : (0:ℝ) ≤ rhoMinus n := by
    unfold rhoMinus
    positivity
  nlinarith [hlt, hrhononneg]

/-! ## The refutation -/

theorem periodic_signing_beats_twisted_class_core (n : ℕ) [NeZero n] (hdvd : 8 ∣ n)
    (hn : 32 ≤ n) :
    ∃ A : Matrix (ZMod n) (ZMod n) ℝ, IsCirculantSigning n A ∧
      ∀ (μ : ℝ) (v : ZMod n → ℝ), v ≠ 0 → A.mulVec v = μ • v → |μ| < rhoMinus n := by
  refine ⟨signedAdjacency n hdvd, signedAdjacency_isCirculantSigning_core n hdvd, ?_⟩
  intro μ v hv hev
  exact lt_of_le_of_lt (eigenvalue_band_bound_core n hdvd μ v hv hev)
    (separator_lt_twisted_value_core n hn)

end

end PalomarSignedCirculantSource
