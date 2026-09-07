import ShellTomography.UniformMinimum
import ShellTomography.UniformAttainer
import ShellTomography.GridLowerBound

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ShellTomography.Uniform

def ambiguityThreshold (n : ℕ) : ℕ := if Odd n then n-2 else n-3

theorem kernel_zero_vector (n : ℕ) : alternatingKernelVector n Params4.zero=0 := by
  funext v
  simp [alternatingKernelVector,oddKernelEntry,evenKernelEntry,Params4.zero]

theorem kernel_vector_ne_zero {n : ℕ} (hn : 6 ≤ n) (p : Params4) (hp : p ≠ Params4.zero) :
    alternatingKernelVector n p ≠ 0 := by
  intro h
  have hz := kernel_zero_vector n
  have hh := congrArg (alternatingExtract hn) (h.trans hz.symm)
  rw [extract_reconstruct_uniform,extract_reconstruct_uniform] at hh
  exact hp hh

theorem kernel_minimum_uniform {n : ℕ} (hn : 6 ≤ n) (p : Params4) (hp : p ≠ Params4.zero) :
    ambiguityThreshold n ≤ mass (positive (alternatingKernelVector n p)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  by_cases ho : Odd (m+1)
  · have h := kernel_minimum_odd (by omega) ho p hp
    simpa [ambiguityThreshold,ho,Nat.add_sub_assoc (show 1 ≤ m by omega)] using h
  · have h := kernel_minimum_even (by omega) ho p hp
    simpa [ambiguityThreshold,ho,Nat.add_sub_assoc (show 2 ≤ m by omega)] using h

theorem attainer_exists {n : ℕ} (hn : 6 ≤ n) :
    ∃ p : Params4, p ≠ Params4.zero ∧
      mass (positive (alternatingKernelVector n p))=ambiguityThreshold n := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  by_cases ho : Odd (m+1)
  · refine ⟨oddAttainer,by decide,?_⟩
    rw [odd_attainer_mass (by omega) ho]
    simp [ambiguityThreshold,ho]
  · refine ⟨evenAttainer,by decide,?_⟩
    rw [even_attainer_mass (by omega) ho]
    simp [ambiguityThreshold,ho]

/-- Exact all-order recovery threshold, including failure at the first trade. -/
theorem grid_capacity_uniform {n : ℕ} (hn : 6 ≤ n) (h : ℕ) :
    ResolvesUpTo (altDistance (n := n) (by omega)) h ↔ h < ambiguityThreshold n := by
  rw [resolvesUpTo_iff_no_small_trade _ (⟨0,by omega⟩ : AltSensor n)]
  constructor
  · intro hr
    obtain ⟨p,hp,hm⟩ := attainer_exists hn
    have hh := hr _ (kernel_vector_ne_zero hn p hp) (kernel_sound_uniform hn p)
    rwa [hm] at hh
  · intro hh z hz hi
    have he := kernel_complete_uniform hn z hi
    have hp : alternatingExtract hn z ≠ Params4.zero := by
      intro h
      rw [h,kernel_zero_vector] at he
      exact hz he
    have hm := kernel_minimum_uniform hn _ hp
    rw [← he] at hm
    omega

def alternatingSet {n : ℕ} (hn : 3 ≤ n) : Finset (Grid n) :=
  Finset.univ.image (altSensorVertex hn)

theorem altSensorVertex_injective {n : ℕ} (hn : 3 ≤ n) : Function.Injective (altSensorVertex hn) := by
  intro i j h
  have hh := congrArg (fun v : Grid n => v.1.val) h
  have hv (k : AltSensor n) : (altSensorVertex hn k).1.val=k.val+1 := by
    dsimp only [altSensorVertex]
    split_ifs <;> rfl
  change (altSensorVertex hn i).1.val=(altSensorVertex hn j).1.val at hh
  rw [hv,hv] at hh
  apply Fin.ext
  omega

theorem alternatingSet_card {n : ℕ} (hn : 3 ≤ n) : (alternatingSet hn).card=n-2 := by
  rw [alternatingSet,Finset.card_image_of_injective _ (altSensorVertex_injective hn)]
  simp [AltSensor]

theorem alternatingSet_resolves {n : ℕ} (hn : 6 ≤ n) (h : ℕ) (hh : h < ambiguityThreshold n) :
    ResolvesUpTo (fun (s : alternatingSet (by omega)) v => (gridGraph n).dist s.val v) h := by
  have hr := (grid_capacity_uniform hn h).mpr hh
  intro x y hx hy hobs
  apply hr x y hx hy
  intro k
  have hk : altSensorVertex (by omega) k ∈ alternatingSet (n := n) (by omega) := by
    exact Finset.mem_image.mpr ⟨k,Finset.mem_univ k,rfl⟩
  have hc := hobs ⟨altSensorVertex (by omega) k,hk⟩
  simpa only [bag,grid_dist_eq_manhattan,altDistance] using hc

/-- The construction achieves the minimum sensor count throughout its nontrivial recovery range. -/
theorem grid_sensor_optimality {n : ℕ} (hn : 6 ≤ n) (h : ℕ)
    (hh : 2 ≤ h) (ht : h < ambiguityThreshold n) :
    (∃ S : Finset (Grid n), S.card=n-2 ∧
      ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h) ∧
    (∀ S : Finset (Grid n), ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) h →
      n-2 ≤ S.card) := by
  constructor
  · exact ⟨alternatingSet (by omega),alternatingSet_card (by omega),alternatingSet_resolves hn h ht⟩
  · intro S hs
    by_contra hc
    have hsmall := grid_two_target_lower_bound S (by omega)
    exact hsmall (resolvesUpTo_mono_bound _ hh hs)

/-- Every complete observation fibre is an explicitly parameterized integral affine slice. -/
theorem grid_fibre_uniform {n : ℕ} (hn : 6 ≤ n) (x y : Configuration (Grid n)) :
    SameObservation (altDistance (n := n) (by omega)) x y ↔
      ∃! p : Params4, ∀ v, (y v : ℤ)=(x v : ℤ)+alternatingKernelVector n p v := by
  have h := grid_kernel_uniform hn (difference y x)
  have he : Invisible (altDistance (n := n) (by omega)) (difference y x) ↔
      SameObservation (altDistance (n := n) (by omega)) x y := by
    rw [invisible_difference_iff]
    exact ⟨fun hh s => (hh s).symm,fun hh s => (hh s).symm⟩
  rw [he] at h
  rw [h]
  have hf (p : Params4) : difference y x=alternatingKernelVector n p ↔
      ∀ v, (y v : ℤ)=(x v : ℤ)+alternatingKernelVector n p v := by
    rw [funext_iff]
    simp only [difference]
    constructor <;> intro h v <;> have hh := h v <;> omega
  simp_rw [hf]

end ShellTomography.Uniform
