module
public import ShellObservability.HypercubeGeometry

/-! New geometric certificates. These declarations are not part of the frozen
Comparator entry. The polynomial application below exposes its finite moment
certificate; it does not assume or claim a formalization of ABCO's theorem. -/
@[expose] public section

namespace ShellObservability.Hypercube

/-- The word with ones at two specified coordinates. -/
def pairWord {n : ℕ} (i j : Fin n) : Cube n :=
  Function.update (Function.update (fun _ => false) i true) j true

lemma distance_zero (x : Cube n) : hammingDist x (fun _ => false) = weight x := by
  simp only [hamming_eq_sum, weight]
  apply Finset.sum_congr rfl
  intro i _
  cases x i <;> rfl

lemma distance_pairWord (x : Cube n) (i j : Fin n) (hij : i ≠ j) :
    hammingDist x (pairWord i j) +
      2 * (if x i then 1 else 0) + 2 * (if x j then 1 else 0) = weight x + 2 := by
  have h₁ := hamming_update_balance (fun _ : Fin n => false) x i true
  have h₂ := hamming_update_balance
    (Function.update (fun _ : Fin n => false) i true) x j true
  rw [hammingDist_comm (fun _ => false) x, distance_zero] at h₁
  rw [Function.update_of_ne (Ne.symm hij)] at h₂
  rw [hammingDist_comm (Function.update (fun _ : Fin n => false) i true) x] at h₁ h₂
  rw [hammingDist_comm] at h₂
  change hammingDist x (pairWord i j) + (if false ≠ x j then 1 else 0) =
    hammingDist x (Function.update (fun _ => false) i true) +
      (if true ≠ x j then 1 else 0) at h₂
  cases hi : x i <;> cases hj : x j <;> simp [hi,hj] at h₁ h₂ ⊢ <;> omega

/-- A translated binary tetrahedron has no common equidistant cube vertex.
In dimensions divisible by four its even antipodal classes give the minimal
four-set obstruction to common middle neighbors. -/
theorem four_word_no_common_distance (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ ∃ x : Cube n,
      hammingDist x (fun _ => false) = hammingDist x (pairWord i j) ∧
      hammingDist x (fun _ => false) = hammingDist x (pairWord i k) ∧
      hammingDist x (fun _ => false) = hammingDist x (pairWord j k) := by
  rintro ⟨x,h₁,h₂,h₃⟩
  rw [distance_zero] at h₁ h₂ h₃
  have e₁ := distance_pairWord x i j hij
  have e₂ := distance_pairWord x i k hik
  have e₃ := distance_pairWord x j k hjk
  rw [← h₁] at e₁
  rw [← h₂] at e₂
  rw [← h₃] at e₃
  cases hi : x i <;> cases hj : x j <;> cases hk : x k <;>
    simp [hi,hj,hk] at e₁ e₂ e₃

/-- The obstruction uses actual shortest-path distances, not an assumed metric. -/
theorem four_word_no_common_graph_distance (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ¬ ∃ x : Cube n,
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord i j) ∧
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord i k) ∧
      (cubeGraph n).dist x (fun _ => false) = (cubeGraph n).dist x (pairWord j k) := by
  simpa only [cube_dist_eq_hamming] using four_word_no_common_distance i j k hij hik hjk

end ShellObservability.Hypercube

namespace ShellObservability.CubeSupport
open Finset

/-- A nonzero weighted sum in every fiber forces at least one support point
per fiber. This is the counting step in the maximal-monomial support proof. -/
theorem support_card_ge_of_fiber_moments
    {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (f w : X → ℝ) (π : X → Y)
    (hmoment : ∀ y, (∑ x ∈ univ.filter (fun x => π x = y), w x * f x) ≠ 0) :
    Fintype.card Y ≤ (univ.filter (fun x => f x ≠ 0)).card := by
  classical
  have hex : ∀ y, ∃ x, π x = y ∧ f x ≠ 0 := by
    intro y
    by_contra h
    push Not at h
    apply hmoment y
    apply sum_eq_zero
    intro x hx
    rw [h x (mem_filter.mp hx).2, mul_zero]
  let g : Y → {x : X // x ∈ univ.filter (fun x => f x ≠ 0)} :=
    fun y => ⟨(hex y).choose, by simp [(hex y).choose_spec.2]⟩
  have hg : Function.Injective g := by
    intro y z h
    have he : (hex y).choose = (hex z).choose := congrArg Subtype.val h
    exact (hex y).choose_spec.1.symm.trans
      ((congrArg π he).trans (hex z).choose_spec.1)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective g hg

/-- Explicit cube support bound from the alternating-fiber certificate.
A maximal nonzero monomial of degree d provides precisely this certificate. -/
theorem cube_support_lower_bound_of_moments
    (n d : ℕ) (f w : (Fin n → Bool) → ℝ)
    (π : (Fin n → Bool) → (Fin (n-d) → Bool))
    (hmoment : ∀ y, (∑ x ∈ univ.filter (fun x => π x = y), w x * f x) ≠ 0) :
    2^(n-d) ≤ (univ.filter (fun x => f x ≠ 0)).card := by
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] using
    support_card_ge_of_fiber_moments f w π hmoment

/-- Conditional finite certificate for the isolate-support inequality.
For a k-vertex folded dominating set the balanced product has degree 2k and
support exactly four times the number r of isolated selected classes. The
classical polynomial argument supplies the displayed moment certificate. -/
theorem isolate_support_bound_of_moments
    (n k r : ℕ) (f w : (Fin n → Bool) → ℝ)
    (π : (Fin n → Bool) → (Fin (n-2*k) → Bool))
    (hmoment : ∀ y, (∑ x ∈ univ.filter (fun x => π x = y), w x * f x) ≠ 0)
    (hsupport : (univ.filter (fun x => f x ≠ 0)).card = 4*r) :
    2^(n-2*k) ≤ 4*r := by
  rw [← hsupport]
  exact cube_support_lower_bound_of_moments n (2*k) f w π hmoment

end ShellObservability.CubeSupport
