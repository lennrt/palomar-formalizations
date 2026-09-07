import ShellTomography.Foundations
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Combinatorics.SimpleGraph.Prod

/-! Polynomial responses and the exact full-factor Cartesian-product kernel. -/

noncomputable section

namespace ShellTomography

open Polynomial

universe u v w
variable {G : Type u} {H : Type v} {S : Type w}
variable [Fintype G] [Fintype H] [Fintype S]
variable [DecidableEq G] [DecidableEq H] [DecidableEq S]

/-- Polynomial response associated to a natural-valued distance table. -/
def response (d : S → G → ℕ) (z : SignedConfiguration G) (s : S) : Polynomial ℤ :=
  ∑ v, Polynomial.monomial (d s v) (z v)

/-- Coefficients of the response are exactly shell sums. -/
theorem coeff_response (d : S → G → ℕ) (z : SignedConfiguration G) (s : S) (r : ℕ) :
    (response d z s).coeff r = shellZ d z s r := by
  classical
  unfold response shellZ
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro v hv
  simp [Polynomial.coeff_monomial]

/-- Vanishing polynomial response is equivalent to vanishing at every distance shell. -/
theorem response_eq_zero_iff (d : S → G → ℕ) (z : SignedConfiguration G) (s : S) :
    response d z s = 0 ↔ ∀ r, shellZ d z s r = 0 := by
  constructor
  · intro h r
    have := congrArg (fun p : Polynomial ℤ => p.coeff r) h
    simpa [coeff_response] using this
  · intro h
    ext r
    simpa [coeff_response] using h r

/-- Matrix of exponential-distance polynomials. -/
def mixing (d : G → G → ℕ) : Matrix G G (Polynomial ℤ) :=
  fun g u => Polynomial.monomial (d g u) 1

/-- A zero-diagonal-positive distance table has identity constant coefficient. -/
def MetricLike (d : G → G → ℕ) : Prop := ∀ g u, d g u = 0 ↔ g = u

/-- Constant coefficient of the mixing matrix is the identity. -/
theorem mixing_coeff_zero (d : G → G → ℕ) (hd : MetricLike d) (g u : G) :
    (mixing d g u).coeff 0 = if g = u then 1 else 0 := by
  unfold mixing
  simp [Polynomial.coeff_monomial, hd g u]

/-- The exponential-distance determinant has constant term one. -/
theorem mixing_det_constant (d : G → G → ℕ) (hd : MetricLike d) :
    Polynomial.constantCoeff (mixing d).det = 1 := by
  rw [RingHom.map_det]
  have h : (mixing d).map Polynomial.constantCoeff = (1 : Matrix G G ℤ) := by
    ext g u
    simpa [Matrix.map_apply, Matrix.one_apply] using mixing_coeff_zero d hd g u
  change ((mixing d).map Polynomial.constantCoeff).det = 1
  rw [h, Matrix.det_one]

/-- Invertibility over the fraction field gives injection already over integer polynomials. -/
theorem mixing_mulVec_injective (d : G → G → ℕ) (hd : MetricLike d) :
    Function.Injective ((mixing d).mulVec : (G → Polynomial ℤ) → (G → Polynomial ℤ)) := by
  classical
  have hdet : (mixing d).det ≠ 0 := by
    intro h
    have hc := mixing_det_constant d hd
    rw [h, map_zero] at hc
    exact zero_ne_one hc
  intro F F' h
  have hz : (mixing d).mulVec (F - F') = 0 := by
    rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet hz)

/-- Additive distance on a Cartesian product. -/
def productDistance (dG : G → G → ℕ) (dH : H → H → ℕ) :
    (G × H) → (G × H) → ℕ := fun x y => dG x.1 y.1 + dH x.2 y.2

/-- Slice an integer configuration by the first factor. -/
def slice (z : SignedConfiguration (G × H)) (u : G) : SignedConfiguration H := fun v => z (u,v)

/-- Product response decomposes by the first-factor mixing matrix. -/
theorem response_product_decompose
    (dG : G → G → ℕ) (dH : S → H → ℕ)
    (z : SignedConfiguration (G × H)) (g : G) (t : S) :
    response (fun (st : G × S) (uv : G × H) => dG st.1 uv.1 + dH st.2 uv.2) z (g,t) =
      ∑ u, Polynomial.monomial (dG g u) 1 * response dH (slice z u) t := by
  classical
  unfold response slice
  rw [Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum, Polynomial.monomial_mul_monomial, one_mul]

/-- Exact slice characterization of the full-factor product kernel. -/
theorem product_kernel_iff
    (dG : G → G → ℕ) (dH : S → H → ℕ)
    (hdG : MetricLike dG) (z : SignedConfiguration (G × H)) :
    Invisible (fun (st : G × S) (uv : G × H) => dG st.1 uv.1 + dH st.2 uv.2) z ↔
      ∀ u, Invisible dH (slice z u) := by
  constructor
  · intro hz u t r
    let F : G → Polynomial ℤ := fun u => response dH (slice z u) t
    have hKF : (mixing dG).mulVec F = 0 := by
      funext g
      have hg : response (fun (st : G × S) (uv : G × H) => dG st.1 uv.1 + dH st.2 uv.2) z (g,t) = 0 :=
        (response_eq_zero_iff _ z (g,t)).mpr (hz (g,t))
      rw [response_product_decompose] at hg
      exact hg
    have hF : F = 0 := mixing_mulVec_injective dG hdG (by simpa using hKF)
    exact (response_eq_zero_iff dH (slice z u) t).mp (congrFun hF u) r
  · intro hz st r
    apply (response_eq_zero_iff _ z st).mp ?_ r
    rw [response_product_decompose]
    apply Finset.sum_eq_zero
    intro u hu
    rw [(response_eq_zero_iff dH (slice z u) st.2).mpr (hz u st.2), mul_zero]

/-- A nonnegative slice cannot have more mass than the full configuration. -/
theorem slice_mass_le (x : Configuration (G × H)) (u : G) :
    mass (fun v => x (u,v)) ≤ mass x := by
  unfold mass
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun i => ∑ v, x (i,v)) (fun i _ => Nat.zero_le _) (Finset.mem_univ u)

/-- Full-factor sensing preserves bounded recovery in both directions, for every mass bound. -/
theorem product_resolves_iff [Nonempty G]
    (dG : G → G → ℕ) (dH : S → H → ℕ) (hdG : MetricLike dG) (h : ℕ) :
    ResolvesUpTo (fun (st : G × S) (uv : G × H) => dG st.1 uv.1 + dH st.2 uv.2) h ↔
      ResolvesUpTo dH h := by
  classical
  constructor
  · intro hp x y hx hy hobs
    let g₀ : G := Classical.arbitrary G
    let X : Configuration (G × H) := fun v => if v.1 = g₀ then x v.2 else 0
    let Y : Configuration (G × H) := fun v => if v.1 = g₀ then y v.2 else 0
    have hX : mass X = mass x := by
      simp [mass, X, Fintype.sum_prod_type]
    have hY : mass Y = mass y := by
      simp [mass, Y, Fintype.sum_prod_type]
    have hi : Invisible (fun (st : G × S) (uv : G × H) => dG st.1 uv.1 + dH st.2 uv.2)
        (difference X Y) := by
      apply (product_kernel_iff dG dH hdG _).mpr
      intro u
      by_cases hu : u = g₀
      · intro t r
        simpa [shellZ, slice, difference, X, Y, hu] using
          (invisible_difference_iff dH x y).mpr hobs t r
      · intro t r
        simp [shellZ, slice, difference, X, Y, hu]
    have he := hp X Y (hX ▸ hx) (hY ▸ hy) ((invisible_difference_iff _ X Y).mp hi)
    funext v
    simpa [X, Y] using congrFun he (g₀,v)
  · intro hf x y hx hy hobs
    have hi := (product_kernel_iff dG dH hdG (difference x y)).mp
      ((invisible_difference_iff _ x y).mpr hobs)
    funext v
    have he := hf (fun w => x (v.1,w)) (fun w => y (v.1,w))
      ((slice_mass_le x v.1).trans hx) ((slice_mass_le y v.1).trans hy)
      ((invisible_difference_iff dH _ _).mp (hi v.1))
    exact congrFun he v.2

/-- Cartesian-product graph distance is additive; connectivity excludes the
zero-distance convention for disconnected vertices. -/
theorem boxProd_dist (A : SimpleGraph G) (B : SimpleGraph H)
    (hA : A.Connected) (hB : B.Connected) (x y : G × H) :
    (A.boxProd B).dist x y = A.dist x.1 y.1 + B.dist x.2 y.2 := by
  have h := SimpleGraph.edist_boxProd (G := A) (H := B) x y
  rw [← ((hA.boxProd hB) x y).coe_dist_eq_edist,
    ← (hA x.1 y.1).coe_dist_eq_edist, ← (hB x.2 y.2).coe_dist_eq_edist] at h
  exact_mod_cast h

/-- Paper's exact kernel theorem for genuine connected simple graphs and an
arbitrary labelled placement in the second factor. -/
theorem graph_product_kernel_iff
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (z : SignedConfiguration (G × H)) :
    Invisible (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) z ↔
      ∀ u, Invisible (fun s v => B.dist (sensor s) v) (slice z u) := by
  simpa only [boxProd_dist A B hA hB] using
    product_kernel_iff A.dist (fun s v => B.dist (sensor s) v)
      (fun _ _ => hA.dist_eq_zero_iff) z

/-- Every bounded population-recovery threshold is preserved exactly under a full-factor lift. -/
theorem graph_product_resolves_iff
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (h : ℕ) :
    ResolvesUpTo (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) h ↔
      ResolvesUpTo (fun s v => B.dist (sensor s) v) h := by
  haveI := hA.nonempty
  simpa only [boxProd_dist A B hA hB] using
    product_resolves_iff A.dist (fun s v => B.dist (sensor s) v)
      (fun _ _ => hA.dist_eq_zero_iff) h

end ShellTomography
