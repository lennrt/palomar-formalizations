module

public import ShellObservability.Robust

@[expose] public section

/-! Exact finite-multiset representation of occupancy configurations, and the
padding bridge from exact-mass recovery to recovery of all smaller populations. -/

namespace ShellObservability

open ShellTomography

section Representation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The actual population multiset, with one entry for each occupied copy. -/
def population (x : Configuration V) : Multiset V := bag (fun (_ : Unit) v => v) x ()

omit [DecidableEq V] in
@[simp] theorem population_card (x : Configuration V) : (population x).card = mass x := by
  simp [population, bag, mass]

@[simp] theorem population_count (x : Configuration V) (v : V) :
    (population x).count v = x v := by
  rw [population, count_bag]
  simp [shellN]

theorem population_injective : Function.Injective (population (V := V)) := by
  intro x y h
  funext v
  have hc := congrArg (Multiset.count v) h
  simpa only [population_count] using hc

@[simp] theorem population_pairConfig (p q : V) : population (pairConfig p q) = {p,q} := by
  exact bag_pairConfig _ p q ()

/-- Every mass-two configuration is a literal pair, allowing repetitions. -/
theorem mass_two_iff_pairConfig (x : Configuration V) :
    mass x = 2 ↔ ∃ p q, x = pairConfig p q := by
  constructor
  · intro hx
    have hp : (population x).card = 2 := by simpa using hx
    obtain ⟨p,q,hpq⟩ := Multiset.card_eq_two.mp hp
    refine ⟨p,q,population_injective ?_⟩
    simpa only [population_pairConfig] using hpq
  · rintro ⟨p,q,rfl⟩
    exact mass_pairConfig p q

/-- Equality of pair configurations is exactly equality of the two-point
multisets, including repeated targets. -/
theorem pairConfig_eq_iff_pair_eq (p q r s : V) :
    pairConfig p q = pairConfig r s ↔ ({p,q} : Multiset V) = {r,s} := by
  constructor
  · intro h
    simpa only [population_pairConfig] using congrArg population h
  · intro h
    apply population_injective
    simpa only [population_pairConfig] using h

end Representation

section Padding

variable {V S R : Type*} [Fintype V] [Fintype S] [Nonempty V] [DecidableEq R]

omit [Fintype S] [DecidableEq R] in
/-- Exact-mass erasure recovery extends to all smaller masses whenever every
allowed erasure leaves a sensor. The imported padding theorem supplies the
configuration argument, so zero, one, and repeated targets are all covered. -/
theorem toleratesErasures_upTo_of_exact
    (δ : S → V → R) (h e : ℕ)
    (hsurvive : ∀ erased : Finset S, erased.card ≤ e → ∃ s, s ∉ erased)
    (hexact : ToleratesErasures (bag δ) (fun x => mass x = h) e) :
    ToleratesErasures (bag δ) (fun x => mass x ≤ h) e := by
  classical
  intro erased herased x y hx hy hagree
  obtain ⟨s₀, hs₀⟩ := hsurvive erased herased
  let Surviving := {s : S // s ∉ erased}
  letI : Nonempty Surviving := ⟨⟨s₀,hs₀⟩⟩
  let δ' : Surviving → V → R := fun s v => δ s.val v
  have hresolve : ResolvesExactly δ' h := by
    intro x' y' hx' hy' hobs
    apply hexact erased herased x' y' hx' hy'
    intro s hs
    exact hobs ⟨s,hs⟩
  have hup := (resolvesExactly_iff_resolvesUpTo δ' h).mp hresolve
  apply hup x y hx hy
  intro s
  exact hagree s.val s.property

end Padding

end ShellObservability
