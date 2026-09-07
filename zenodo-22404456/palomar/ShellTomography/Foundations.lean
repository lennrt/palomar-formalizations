import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Replicate
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic

/-!
Distance-shell tomography: finite configurations, literal distance bags and integer trades.
Paper author: Lennart Rudolph, ORCID 0009-0009-0198-085X.
Companion DOI: 10.5281/zenodo.22404456.
Formalization prepared with OpenAI Codex; theorem scope is recorded separately.
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

theorem count_bag (δ : S → V → R) (x : Configuration V) (s : S) (r : R) :
    Multiset.count r (bag δ x s) = shellN δ x s r := by
  classical
  unfold bag shellN
  generalize (Finset.univ : Finset V) = t
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a t ha ih =>
      simp only [Finset.sum_insert ha, Multiset.count_add, Multiset.count_replicate, ih]

theorem observation_iff_shells (δ : S → V → R) (x y : Configuration V) :
    SameObservation δ x y ↔ ∀ s r, shellN δ x s r = shellN δ y s r := by
  constructor
  · intro h s r
    have e := congrArg (Multiset.count r) (h s)
    simpa only [count_bag] using e
  · intro h s
    apply Multiset.ext.mpr
    intro r
    simpa only [count_bag] using h s r

theorem shell_difference (δ : S → V → R) (x y : Configuration V) (s : S) (r : R) :
    shellZ δ (difference x y) s r = (shellN δ x s r : ℤ) - (shellN δ y s r : ℤ) := by
  classical
  simp only [shellZ, shellN, difference, Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : δ s v = r <;> simp [h]

theorem invisible_difference_iff (δ : S → V → R) (x y : Configuration V) :
    Invisible δ (difference x y) ↔ SameObservation δ x y := by
  rw [observation_iff_shells]
  constructor
  · intro h s r
    have e := h s r
    rw [shell_difference] at e
    omega
  · intro h s r
    rw [shell_difference, h s r, sub_self]

theorem sum_shells [Fintype R] (δ : S → V → R) (z : SignedConfiguration V) (s : S) :
    (∑ r, shellZ δ z s r) = ∑ v, z v := by
  classical
  unfold shellZ
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  simp [eq_comm]

/-- A finite configuration uses only finitely many output values, even for natural radii. -/
theorem invisible_total (δ : S → V → R) (s₀ : S) (z : SignedConfiguration V)
    (hz : Invisible δ z) : (∑ v, z v) = 0 := by
  classical
  let radii := Finset.univ.image (δ s₀)
  have hs : (∑ r ∈ radii, shellZ δ z s₀ r) = ∑ v, z v := by
    unfold shellZ
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v hv
    have hm : δ s₀ v ∈ radii := Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩
    simp [eq_comm, hm]
  rw [← hs]
  simp [hz s₀]

omit [Fintype V] in
theorem positive_sub_negative (z : SignedConfiguration V) (v : V) :
    (positive z v : ℤ) - (negative z v : ℤ) = z v := by
  unfold positive negative
  omega

theorem positive_negative_mass (δ : S → V → R) (s₀ : S)
    (z : SignedConfiguration V) (hz : Invisible δ z) :
    mass (positive z) = mass (negative z) := by
  have e : (∑ v, ((positive z v : ℤ) - (negative z v : ℤ))) = 0 := by
    calc
      _ = ∑ v, z v := Finset.sum_congr rfl (fun v _ => positive_sub_negative z v)
      _ = 0 := invisible_total δ s₀ z hz
  have e' : (mass (positive z) : ℤ) - (mass (negative z) : ℤ) = 0 := by
    simpa only [mass, Nat.cast_sum, Finset.sum_sub_distrib] using e
  omega

theorem positive_difference_mass_le (x y : Configuration V) :
    mass (positive (difference x y)) ≤ mass x := by
  apply Finset.sum_le_sum
  intro v hv
  unfold positive difference
  omega

omit [Fintype V] in
theorem difference_ne_zero (x y : Configuration V) (hxy : x ≠ y) :
    difference x y ≠ 0 := by
  intro h
  apply hxy
  funext v
  have e := congrFun h v
  simp only [difference, Pi.zero_apply] at e
  omega

theorem parts_ne_of_ne_zero (z : SignedConfiguration V) (hz : z ≠ 0) :
    positive z ≠ negative z := by
  intro h
  apply hz
  funext v
  have e := positive_sub_negative z v
  have p : positive z v = negative z v := congrFun h v
  rw [p, sub_self] at e
  exact e.symm

theorem observation_parts (δ : S → V → R) (z : SignedConfiguration V)
    (hz : Invisible δ z) : SameObservation δ (positive z) (negative z) := by
  apply (invisible_difference_iff δ (positive z) (negative z)).mp
  have e : difference (positive z) (negative z) = z := by
    funext v
    exact positive_sub_negative z v
  rw [e]
  exact hz

/-- The low-trade criterion for any output alphabet and a chosen sensor.
The chosen sensor is what makes every invisible trade balanced. -/
theorem resolvesUpTo_iff_no_small_trade (δ : S → V → R) (s₀ : S) (h : ℕ) :
    ResolvesUpTo δ h ↔
      ∀ z : SignedConfiguration V, z ≠ 0 → Invisible δ z → h < mass (positive z) := by
  constructor
  · intro recover z hz hinv
    by_contra hn
    have hp : mass (positive z) ≤ h := by omega
    have hm := positive_negative_mass δ s₀ z hinv
    have hneg : mass (negative z) ≤ h := by omega
    have eqparts := recover (positive z) (negative z) hp hneg (observation_parts δ z hinv)
    exact parts_ne_of_ne_zero z hz eqparts
  · intro noTrade x y hx hy hobs
    by_contra hxy
    have hinv := (invisible_difference_iff δ x y).mpr hobs
    have big := noTrade (difference x y) (difference_ne_zero x y hxy) hinv
    have small := positive_difference_mass_le x y
    omega

omit [DecidableEq R] in
theorem resolvesUpTo_mono_bound (δ : S → V → R) {h k : ℕ}
    (hhk : h ≤ k) (hk : ResolvesUpTo δ k) : ResolvesUpTo δ h := by
  intro x y hx hy hobs
  exact hk x y (hx.trans hhk) (hy.trans hhk) hobs

omit [DecidableEq R] in
theorem resolvesUpTo_mono_sensors {T : Type*} (δ : T → V → R) (f : S → T)
    (h : ℕ) (hs : ResolvesUpTo (fun s v => δ (f s) v) h) : ResolvesUpTo δ h := by
  intro x y hx hy hobs
  apply hs x y hx hy
  intro s
  exact hobs (f s)

def shellMatrix (δ : S → V → R) : Matrix (S × R) V ℤ :=
  fun sr v => if δ sr.1 v = sr.2 then 1 else 0

theorem matrix_mul_eq_shells (δ : S → V → R) (z : SignedConfiguration V) :
    (shellMatrix δ).mulVec z = fun sr => shellZ δ z sr.1 sr.2 := by
  classical
  funext sr
  simp only [Matrix.mulVec, dotProduct, shellMatrix, shellZ]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : δ sr.1 v = sr.2 <;> simp [h]

/-- A faithful finite identity measurement pilot, not yet a path-graph adapter. -/
theorem identity_measurement_resolves (n h : ℕ) :
    ResolvesUpTo (fun (_ : Unit) (v : Fin n) => v) h := by
  intro x y hx hy hobs
  have hsh := (observation_iff_shells (fun (_ : Unit) (v : Fin n) => v) x y).mp hobs
  funext v
  simpa [shellN] using hsh () v

end ShellTomography

namespace ShellTomography

section ExtraFoundations
variable {V : Type u} {S : Type v} {R : Type w}
variable [Fintype V] [DecidableEq R]

/-- Equality of shell observations, a convenient matrix-free form. -/
def SameShells (δ : S → V → R) (x y : Configuration V) : Prop :=
  ∀ s r, shellN δ x s r = shellN δ y s r

@[simp] theorem sameObservation_iff_sameShells (δ : S → V → R) (x y : Configuration V) :
    SameObservation δ x y ↔ SameShells δ x y := observation_iff_shells δ x y

/-- Every signed configuration is the difference of its positive and negative parts. -/
theorem difference_parts (z : SignedConfiguration V) :
    difference (positive z) (negative z) = z := by
  funext v
  exact positive_sub_negative z v

/-- If a trade is invisible, its two nonnegative parts have the same observation. -/
theorem invisible_gives_collision (δ : S → V → R) (z : SignedConfiguration V)
    (hz : Invisible δ z) : SameObservation δ (positive z) (negative z) :=
  observation_parts δ z hz

/-- Exactly-h and at-most-h collision formulations agree in the multiplicity model. -/
def ResolvesExactly (δ : S → V → R) (h : ℕ) : Prop :=
  ∀ x y : Configuration V, mass x = h → mass y = h → SameObservation δ x y → x = y

omit [DecidableEq R] in
/-- Padding both sides at one fixed vertex converts a smaller collision to mass h. -/
theorem resolvesExactly_iff_resolvesUpTo [Nonempty V] [Nonempty S] (δ : S → V → R) (h : ℕ) :
    ResolvesExactly δ h ↔ ResolvesUpTo δ h := by
  classical
  constructor
  · intro hex x y hx hy hobs
    let v₀ : V := Classical.choice (inferInstance : Nonempty V)
    let px : Configuration V := fun v => if v = v₀ then h - mass x else 0
    let py : Configuration V := fun v => if v = v₀ then h - mass y else 0
    let x' : Configuration V := fun v => x v + px v
    let y' : Configuration V := fun v => y v + py v
    have hmx : mass x' = h := by
      unfold x' px mass
      simp only [Finset.sum_add_distrib]
      have : (∑ v : V, if v = v₀ then h - ∑ u, x u else 0) = h - ∑ u, x u := by
        simp
      rw [this]
      simp only [mass] at hx hy
      omega
    have hmy : mass y' = h := by
      unfold y' py mass
      simp only [Finset.sum_add_distrib]
      have : (∑ v : V, if v = v₀ then h - ∑ u, y u else 0) = h - ∑ u, y u := by
        simp
      rw [this]
      simp only [mass] at hx hy
      omega
    have hmxy : mass x = mass y := by
      -- Any sensor bag has cardinality equal to population mass.
      classical
      let s₀ : S := Classical.choice (inferInstance : Nonempty S)
      have e := congrArg Multiset.card (hobs s₀)
      simpa [bag, mass] using e
    have hpad : px = py := by
      funext v
      simp [px, py, hmxy]
    have hobs' : SameObservation δ x' y' := by
      intro s
      unfold x' y' bag
      simp only [Finset.sum_add_distrib, Multiset.replicate_add]
      rw [hpad]
      simpa [bag] using congrArg (fun m => m + ∑ v, Multiset.replicate (py v) (δ s v)) (hobs s)
    have heq := hex x' y' hmx hmy hobs'
    funext v
    have := congrFun heq v
    simp only [x', y', hpad] at this
    omega
  · intro hup x y hx hy hobs
    exact hup x y (by omega) (by omega) hobs

end ExtraFoundations

end ShellTomography

namespace ShellTomography
variable {V : Type*} {S : Type*} {R : Type*} [Fintype V] [DecidableEq V]

def pointConfig (p : V) : Configuration V := fun v => if v = p then 1 else 0

def pairConfig (p q : V) : Configuration V := fun v => pointConfig p v + pointConfig q v

@[simp] theorem mass_pointConfig (p : V) : mass (pointConfig p) = 1 := by
  simp [mass, pointConfig]

@[simp] theorem mass_pairConfig (p q : V) : mass (pairConfig p q) = 2 := by
  simp [mass, pairConfig, pointConfig, Finset.sum_add_distrib]

@[simp] theorem bag_pointConfig (δ : S → V → R) (p : V) (s : S) :
    bag δ (pointConfig p) s = {δ s p} := by
  classical
  unfold bag
  have he (v : V) : Multiset.replicate (pointConfig p v) (δ s v) =
      if v = p then {δ s p} else 0 := by
    by_cases hv : v = p <;> simp [pointConfig, hv]
  simp_rw [he]
  simp

@[simp] theorem bag_pairConfig (δ : S → V → R) (p q : V) (s : S) :
    bag δ (pairConfig p q) s = {δ s p, δ s q} := by
  classical
  change (∑ v, Multiset.replicate (pointConfig p v + pointConfig q v) (δ s v)) = _
  simp_rw [Multiset.replicate_add]
  rw [Finset.sum_add_distrib]
  change bag δ (pointConfig p) s + bag δ (pointConfig q) s = _
  rw [bag_pointConfig, bag_pointConfig]
  rfl

end ShellTomography
