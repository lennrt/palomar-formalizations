import ShellTomography.UniformRecovery

namespace ShellTomography.Verified

/-- Bounded recovery is equivalent to exclusion of small nonzero integer trades. -/
theorem trade_criterion {V S : Type*} [Fintype V] (δ : S → V → ℕ) (s₀ : S) (h : ℕ) :
    ResolvesUpTo δ h ↔ ¬ ∃ z : SignedConfiguration V,
      z ≠ 0 ∧ Invisible δ z ∧ mass (positive z) ≤ h := by simpa only [not_exists, not_and, not_le] using resolvesUpTo_iff_no_small_trade δ s₀ h

/-- The full-factor Cartesian-product kernel is exactly the direct sum of factor kernels. -/
theorem product_kernel {G H S : Type*} [Fintype G] [Fintype H] [Fintype S]
    [DecidableEq G] [DecidableEq H] [DecidableEq S]
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (z : SignedConfiguration (G × H)) :
    Invisible (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) z ↔
      ∀ u, Invisible (fun s v => B.dist (sensor s) v) (fun v => z (u,v)) := graph_product_kernel_iff A B hA hB sensor z

/-- Every population mass bound is preserved under full-factor graph sensing. -/
theorem product_recovery {G H S : Type*} [Fintype G] [Fintype H] [Fintype S]
    [DecidableEq G] [DecidableEq H] [DecidableEq S]
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (h : ℕ) :
    ResolvesUpTo (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) h ↔
      ResolvesUpTo (fun s v => B.dist (sensor s) v) h := graph_product_resolves_iff A B hA hB sensor h

/-- Every placement of fewer than n-2 sensors misses an explicit two-target collision. -/
theorem grid_lower_bound {n : ℕ} (S : Finset (Grid n)) (hS : S.card < n-2) :
    ¬ ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) 2 := grid_two_target_lower_bound S hS

/-- For every n at least 6, every invisible integer array has unique explicit four-parameter coordinates. -/
theorem grid_kernel_uniform {n : ℕ} (hn : 6 ≤ n) (z : SignedConfiguration (Grid n)) :
    Invisible (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) z ↔
      ∃! p : Params4, z = alternatingKernelVector n p := by simpa only [grid_dist_eq_manhattan] using Uniform.grid_kernel_uniform hn z

/-- For every n at least 6, the exact threshold is n-2 for odd orders and n-3 for even orders. -/
theorem grid_capacity_uniform {n : ℕ} (hn : 6 ≤ n) (h : ℕ) :
    ResolvesUpTo (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) h ↔
      h < (if Odd n then n-2 else n-3) := by simpa only [grid_dist_eq_manhattan, Uniform.ambiguityThreshold] using Uniform.grid_capacity_uniform hn h

/-- Exactly n-2 sensors are necessary and sufficient throughout the nontrivial recovery range. -/
theorem grid_sensor_optimality {n : ℕ} (hn : 6 ≤ n) (h : ℕ) (hh : 2 ≤ h)
    (ht : h < (if Odd n then n-2 else n-3)) :
    (∃ S : Finset (Grid n), S.card=n-2 ∧
      ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h) ∧
    (∀ S : Finset (Grid n), ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h →
      n-2 ≤ S.card) := Uniform.grid_sensor_optimality hn h hh ht

/-- Every full observation fibre, at every population size, is an explicit four-variable integral affine slice. -/
theorem grid_fibre_uniform {n : ℕ} (hn : 6 ≤ n) (x y : Configuration (Grid n)) :
    SameObservation (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) x y ↔
      ∃! p : Params4, ∀ v, (y v : ℤ)=(x v : ℤ)+alternatingKernelVector n p v := by simpa only [grid_dist_eq_manhattan] using Uniform.grid_fibre_uniform hn x y

end ShellTomography.Verified
