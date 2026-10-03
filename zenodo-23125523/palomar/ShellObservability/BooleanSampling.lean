module

public import Mathlib

@[expose] public section

/-!
Triangular interpolation on a lower Hamming ball, in characteristic zero.
Vertices of a Boolean cube are finite subsets. `evaluate a s` evaluates the
multilinear coefficient array `a` at the indicator vector of `s`.
The polynomial-interpolation fact is classical. The separate theorem that
distance-moment fields have exactly this range is not asserted here.
-/

namespace ShellObservability.BooleanSampling

open Finset

variable {ι : Type*} [DecidableEq ι]

def evaluate (a : Finset ι → ℚ) (s : Finset ι) : ℚ :=
  ∑ t ∈ s.powerset, a t

def DegreeAtMost (a : Finset ι → ℚ) (k : ℕ) : Prop :=
  ∀ s, k < s.card → a s = 0

/-- All coefficients are determined by values on subsets of size at most k. -/
theorem coefficients_zero_of_lower_ball (a : Finset ι → ℚ) (k : ℕ)
    (hdegree : DegreeAtMost a k)
    (hball : ∀ s, s.card ≤ k → evaluate a s = 0) :
    ∀ s, a s = 0 := by
  intro s
  refine Finset.strongInductionOn s ?_
  intro s ih
  by_cases hs : s.card ≤ k
  · have heval := hball s hs
    have hsum : evaluate a s = a s := by
      unfold evaluate
      apply Finset.sum_eq_single s
      · intro t ht hne
        exact ih t (Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp ht, hne⟩)
      · intro hnot
        exact (hnot (mem_powerset.mpr (Subset.refl s))).elim
    exact hsum.symm.trans heval
  · exact hdegree s (by omega)

theorem coefficients_eq_of_lower_ball (a b : Finset ι → ℚ) (k : ℕ)
    (ha : DegreeAtMost a k) (hb : DegreeAtMost b k)
    (hball : ∀ s, s.card ≤ k → evaluate a s = evaluate b s) : a = b := by
  have hc : ∀ s, a s - b s = 0 :=
    coefficients_zero_of_lower_ball (fun s => a s - b s) k
      (by intro s hs; simp [ha s hs, hb s hs])
      (by
        intro s hs
        simpa [evaluate, Finset.sum_sub_distrib] using sub_eq_zero.mpr (hball s hs))
  funext s
  exact sub_eq_zero.mp (hc s)

/-- Every value on the entire cube is fixed by the lower-ball samples. -/
theorem field_eq_of_lower_ball (a b : Finset ι → ℚ) (k : ℕ)
    (ha : DegreeAtMost a k) (hb : DegreeAtMost b k)
    (hball : ∀ s, s.card ≤ k → evaluate a s = evaluate b s) :
    evaluate a = evaluate b := by
  rw [coefficients_eq_of_lower_ball a b k ha hb hball]

end ShellObservability.BooleanSampling
