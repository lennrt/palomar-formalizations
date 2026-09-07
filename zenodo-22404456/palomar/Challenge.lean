import Mathlib.Tactic
import Mathlib.Data.Multiset.Replicate
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Distance-shell tomography: selected paper theorems

Lennart Rudolph. Companion paper and reproducible artifacts:
https://doi.org/10.5281/zenodo.22404456 (published version 1.0.0).

The statements use literal multiplicity-preserving distance bags on known graphs.
Sensors remain labelled; configurations may be empty and may occupy a vertex more
than once. The motivating problem is to reconstruct several indistinguishable
targets from these distance bags. Two adjacent corners locate a single grid vertex,
but resolving even two targets requires at least n-2 sensors. This is a loss of
correspondence across sensors, not a loss of distance precision.

The selection proves an optimal construction for every square grid of order n at
least 6. Alternating side sensors have a four-parameter integer kernel, independent
of grid size. Its smallest nonzero trade has mass n-2 for odd n and n-3 for even n.
Consequently n-2 sensors are optimal throughout the resulting recovery range, and
every complete observation fibre is an explicit four-variable integral affine slice.
These statements concern arbitrary grid orders and populations, not a finite census.

The proof turns shell observations into Laurent-polynomial row responses. A local
tridiagonal inverse propagates the boundary data, and support restrictions leave
exactly four integer parameters. A nonzero ambiguity has at most one zero interior
row; the remaining rows and boundary terms give the sharp trade-mass bound. The
general product theorems transport complete kernels and recovery bounds to Cartesian
products. This provides a method and structural recovery theorem for discrete
tomography, graph identification, and additive-channel reconstruction.

The source paper is Distance-Shell Tomography on Graphs: Integer Trades and Optimal
Grid Sensing. The all-order kernel, sharp threshold, optimality and fibre theorems
are selected below. The paper's coefficient census and separate cycle theorem are
not advertised as Lean results. The Solution proves every selected statement.

This standalone Challenge imports only Mathlib and supplies the definitions directly.
Its theorem placeholders are the expected Comparator specification holes.
-/

universe u v w
namespace ShellTomography

variable {V : Type u} {S : Type v} {R : Type w}
variable [Fintype V] [DecidableEq R]

/-- Nonnegative integer occupancy at each vertex; repetitions and the empty population are allowed. -/
abbrev Configuration (V : Type u) := V → ℕ
/-- An integer occupancy change at each vertex. -/
abbrev SignedConfiguration (V : Type u) := V → ℤ

/-- Total population, counting multiplicities. -/
def mass (x : Configuration V) : ℕ := ∑ v, x v

/-- The sensor-labelled multiset containing x(v) copies of the distance or symbol at v. -/
def bag (δ : S → V → R) (x : Configuration V) (s : S) : Multiset R :=
  ∑ v, Multiset.replicate (x v) (δ s v)

/-- Nonnegative occupancy in one measured distance shell. -/
def shellN (δ : S → V → R) (x : Configuration V) (s : S) (r : R) : ℕ :=
  ∑ v, if δ s v = r then x v else 0

/-- Signed occupancy sum in one measured distance shell. -/
def shellZ (δ : S → V → R) (z : SignedConfiguration V) (s : S) (r : R) : ℤ :=
  ∑ v, if δ s v = r then z v else 0

/-- Equality of the complete distance bags at every labelled sensor. -/
def SameObservation (δ : S → V → R) (x y : Configuration V) : Prop :=
  ∀ s, bag δ x s = bag δ y s

/-- Injectivity of observations on all populations of total mass at most h. -/
def ResolvesUpTo (δ : S → V → R) (h : ℕ) : Prop :=
  ∀ x y : Configuration V, mass x ≤ h → mass y ≤ h → SameObservation δ x y → x = y

/-- Every signed shell sum vanishes, for every sensor and every radius. -/
def Invisible (δ : S → V → R) (z : SignedConfiguration V) : Prop :=
  ∀ s r, shellZ δ z s r = 0

/-- Coordinatewise positive part of an integer occupancy change. -/
def positive (z : SignedConfiguration V) : Configuration V := fun v => (z v).toNat

/-- Coordinatewise negative part, recorded with nonnegative multiplicity. -/
def negative (z : SignedConfiguration V) : Configuration V := fun v => (-z v).toNat

/-- The signed coordinatewise difference of two populations. -/
def difference (x y : Configuration V) : SignedConfiguration V :=
  fun v => (x v : ℤ) - (y v : ℤ)

end ShellTomography
namespace ShellTomography
/-- Vertices of the n by n grid, in zero-based coordinates. -/
abbrev Grid (n : ℕ) := Fin n × Fin n
/-- Natural absolute difference, with truncated subtraction in both directions. -/
def natAbsDiff (a b : ℕ) : ℕ := (a-b)+(b-a)
/-- Sum of coordinatewise absolute displacements. -/
def manhattan {n : ℕ} (x y : Grid n) : ℕ :=
  natAbsDiff x.1.val y.1.val + natAbsDiff x.2.val y.2.val
/-- Simple graph joining exactly vertices at Manhattan distance one. -/
def gridGraph (n : ℕ) : SimpleGraph (Grid n) :=
  SimpleGraph.fromRel fun x y => manhattan x y = 1
structure Params4 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  deriving DecidableEq



/-- Coefficient of q^e at q^j. -/
def monoCoeff (e j : ℕ) : ℤ := if e = j then 1 else 0

/-- Coefficient of (1+q²)q^e. -/
def pairCoeff (e j : ℕ) : ℤ := monoCoeff e j + monoCoeff (e+2) j

/-- Sign (-1)^i. -/
def paritySign (i : ℕ) : ℤ := if Even i then 1 else -1

/-- Row coefficient for odd n, expanded from the odd-order row and parameter formulas in Section 5.2. -/
def oddKernelEntry (n i j : ℕ) (p : Params4) : ℤ :=
  let m := n-1
  if i = 0 then
    -p.a * monoCoeff (m-2) j - p.b * monoCoeff (m-1) j
  else if i = 1 then
    -p.c * monoCoeff 1 j - p.d * monoCoeff 2 j
      + p.a * pairCoeff (m-3) j + p.b * pairCoeff (m-2) j
  else if i = m-1 then
    p.a * monoCoeff 1 j + p.b * monoCoeff 2 j
      - p.c * pairCoeff (m-3) j - p.d * pairCoeff (m-2) j
  else if i = m then
    p.c * monoCoeff (m-2) j + p.d * monoCoeff (m-1) j
  else
    paritySign i *
      (p.c * pairCoeff (i-2) j + p.d * pairCoeff (i-1) j
       - p.a * pairCoeff (m-2-i) j - p.b * pairCoeff (m-1-i) j)

/-- Row coefficient for even n, expanded from the even-order row and parameter formulas in Section 5.2. -/
def evenKernelEntry (n i j : ℕ) (p : Params4) : ℤ :=
  let m := n-1
  if i = 0 then
    -p.d * monoCoeff (m-1) j
  else if i = 1 then
    -p.a * monoCoeff 1 j - p.b * monoCoeff 2 j - p.c * monoCoeff 3 j
      + p.d * monoCoeff (m-2) j + p.d * monoCoeff m j
  else if i = m-1 then
    p.a * monoCoeff (m-3) j + p.b * monoCoeff (m-2) j + p.c * monoCoeff (m-1) j
      - p.d * monoCoeff 0 j - p.d * monoCoeff 2 j
  else if i = m then
    p.d * monoCoeff 1 j
  else
    paritySign i *
      (p.a * pairCoeff (i-2) j + p.b * pairCoeff (i-1) j
       + p.c * pairCoeff i j - p.d * pairCoeff (m-1-i) j)

/-- The explicit n²-vector B_n p. -/
def alternatingKernelVector (n : ℕ) (p : Params4) : SignedConfiguration (Grid n) := fun v =>
  if Odd n then oddKernelEntry n v.1.val v.2.val p
  else evenKernelEntry n v.1.val v.2.val p

/-- There are n-2 sensors, indexed by the interior first coordinate minus one. -/
abbrev AltSensor (n : ℕ) := Fin (n-2)

/-- Alternating boundary vertex associated to sensor k. -/
def altSensorVertex {n : ℕ} (hn : 3 ≤ n) (k : AltSensor n) : Grid n :=
  let i : ℕ := k.val + 1
  let fi : Fin n := ⟨i, by have := k.isLt; omega⟩
  if Odd i then (fi, ⟨0,by omega⟩) else (fi, ⟨n-1,by omega⟩)

/-- Actual Manhattan distance table for the alternating sensors. -/
def altDistance {n : ℕ} (hn : 3 ≤ n) : AltSensor n → Grid n → ℕ :=
  fun k v => manhattan (altSensorVertex hn k) v

end ShellTomography

namespace ShellTomography.Verified

/-- Bounded recovery is equivalent to exclusion of small nonzero integer trades. -/
theorem trade_criterion {V S : Type*} [Fintype V] (δ : S → V → ℕ) (s₀ : S) (h : ℕ) :
    ResolvesUpTo δ h ↔ ¬ ∃ z : SignedConfiguration V,
      z ≠ 0 ∧ Invisible δ z ∧ mass (positive z) ≤ h := by
  sorry

/-- The full-factor Cartesian-product kernel is exactly the direct sum of factor kernels. -/
theorem product_kernel {G H S : Type*} [Fintype G] [Fintype H] [Fintype S]
    [DecidableEq G] [DecidableEq H] [DecidableEq S]
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (z : SignedConfiguration (G × H)) :
    Invisible (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) z ↔
      ∀ u, Invisible (fun s v => B.dist (sensor s) v) (fun v => z (u,v)) := by
  sorry

/-- Every population mass bound is preserved under full-factor graph sensing. -/
theorem product_recovery {G H S : Type*} [Fintype G] [Fintype H] [Fintype S]
    [DecidableEq G] [DecidableEq H] [DecidableEq S]
    (A : SimpleGraph G) (B : SimpleGraph H) (hA : A.Connected) (hB : B.Connected)
    (sensor : S → H) (h : ℕ) :
    ResolvesUpTo (fun (st : G × S) (v : G × H) => (A.boxProd B).dist (st.1,sensor st.2) v) h ↔
      ResolvesUpTo (fun s v => B.dist (sensor s) v) h := by
  sorry

/-- Every placement of fewer than n-2 sensors misses an explicit two-target collision. -/
theorem grid_lower_bound {n : ℕ} (S : Finset (Grid n)) (hS : S.card < n-2) :
    ¬ ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) 2 := by
  sorry

/-- For every n at least 6, every invisible integer array has unique explicit four-parameter coordinates. -/
theorem grid_kernel_uniform {n : ℕ} (hn : 6 ≤ n) (z : SignedConfiguration (Grid n)) :
    Invisible (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) z ↔
      ∃! p : Params4, z = alternatingKernelVector n p := by
  sorry

/-- For every n at least 6, the exact threshold is n-2 for odd orders and n-3 for even orders. -/
theorem grid_capacity_uniform {n : ℕ} (hn : 6 ≤ n) (h : ℕ) :
    ResolvesUpTo (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) h ↔
      h < (if Odd n then n-2 else n-3) := by
  sorry

/-- Exactly n-2 sensors are necessary and sufficient throughout the nontrivial recovery range. -/
theorem grid_sensor_optimality {n : ℕ} (hn : 6 ≤ n) (h : ℕ) (hh : 2 ≤ h)
    (ht : h < (if Odd n then n-2 else n-3)) :
    (∃ S : Finset (Grid n), S.card=n-2 ∧
      ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h) ∧
    (∀ S : Finset (Grid n), ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h →
      n-2 ≤ S.card) := by
  sorry

/-- Every full observation fibre, at every population size, is an explicit four-variable integral affine slice. -/
theorem grid_fibre_uniform {n : ℕ} (hn : 6 ≤ n) (x y : Configuration (Grid n)) :
    SameObservation (fun (s : AltSensor n) v => (gridGraph n).dist (altSensorVertex (by omega) s) v) x y ↔
      ∃! p : Params4, ∀ v, (y v : ℤ)=(x v : ℤ)+alternatingKernelVector n p v := by
  sorry

end ShellTomography.Verified
