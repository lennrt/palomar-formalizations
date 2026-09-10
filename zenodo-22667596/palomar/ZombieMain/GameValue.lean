import ZombieMain.GameValueDefinitions

/-! The numerical value is characterized by the same adversarial game,
including eventual objectives and the full-damage endpoint. -/
namespace ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : Graph V}

theorem damageCount_le_card (s : State V) : damageCount s ≤ Fintype.card V := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem card_le_damageCount_iff (s : State V) :
    Fintype.card V ≤ damageCount s ↔ AllDamaged s := by
  classical
  constructor
  · intro h
    have he : Finset.univ.filter s.damaged = Finset.univ :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) h
    intro v
    have hv : v ∈ Finset.univ.filter s.damaged := by rw [he]; exact Finset.mem_univ v
    exact (Finset.mem_filter.mp hv).2
  · intro h
    simp [damageCount, show ∀ v, s.damaged v from h]

theorem CanForceDamage.mono {j k : Nat} (h : CanForceDamage G k) (hjk : j ≤ k) :
    CanForceDamage G j := by
  obtain ⟨hc, b, hb⟩ := h
  refine ⟨hjk.trans hc, b, fun z => ?_⟩
  obtain ⟨v, hne, hv⟩ := hb z
  exact ⟨v, hne, hv.mono (fun _ _ ht => hjk.trans ht)⟩

theorem zero_mem_forceableScores : 0 ∈ forceableScores G := by
  classical
  simp [forceableScores]

theorem number_mem_forceableScores : zombieDamageNumber G ∈ forceableScores G := by
  classical
  have h := Finset.sup_mem_of_nonempty (f := id)
    (show (forceableScores G).Nonempty from ⟨0, zero_mem_forceableScores⟩)
  simpa [zombieDamageNumber] using h

theorem zombieDamageNumber_le_card : zombieDamageNumber G ≤ Fintype.card V := by
  classical
  apply Finset.sup_le
  intro k hk
  have := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  exact Nat.le_of_lt_succ this

/-- Every positive threshold lies below the value exactly when the survivor
can force that threshold. In particular the definition is an attained optimum. -/
theorem canForceDamage_iff_le_number {k : Nat} (hk : 0 < k) :
    CanForceDamage G k ↔ k ≤ zombieDamageNumber G := by
  classical
  constructor
  · intro h
    exact Finset.le_sup (f := id) (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h.1), Or.inr h⟩)
  · intro h
    have hm := Finset.mem_filter.mp (number_mem_forceableScores (G := G))
    rcases hm.2 with hz | hw
    · omega
    · exact hw.mono h

theorem canForceDamage_card_iff : CanForceDamage G (Fintype.card V) ↔ FullDamage G := by
  have hp : (fun (_ : Phase) (s : State V) => Fintype.card V ≤ damageCount s) =
      (fun _ s => AllDamaged s) := by
    funext p s
    exact propext (card_le_damageCount_iff s)
  simp only [CanForceDamage, FullDamage, FullDamageWithin, hp, le_refl, true_and]

/-- On finite graphs the score definition does not require a stronger
preassigned horizon: eventual forcing and one uniform finite bound agree. -/
theorem canForceDamage_iff_eventual (k : Nat) : CanForceDamage G k ↔
    k ≤ Fintype.card V ∧ ∀ z, ∃ v, z ≠ v ∧
      ForcesEventually G (fun _ s => k ≤ damageCount s) .zombie (initial z v) := by
  classical
  let vs := (Finset.univ : Finset V).toList
  have hevery : ∀ v, v ∈ vs := by intro v; simp [vs]
  constructor
  · rintro ⟨hc, b, hb⟩
    refine ⟨hc, fun z => ?_⟩
    obtain ⟨v, hne, hv⟩ := hb z
    exact ⟨v, hne, hv.eventually⟩
  · rintro ⟨hc, h⟩
    have hb := uniform_bound vs
      (fun b z => ∃ v, z ≠ v ∧ ForcesWithin G
        (fun _ s => k ≤ damageCount s) b .zombie (initial z v))
      (fun b c hbc z hb => by
        obtain ⟨v, hne, hv⟩ := hb
        exact ⟨v, hne, hv.mono_budget hbc⟩) (fun z _ => by
        obtain ⟨v, hne, hv⟩ := h z
        obtain ⟨b, hb⟩ := ForcesEventually.bounded G hv vs hevery
        exact ⟨b, v, hne, hb⟩)
    obtain ⟨b, hb⟩ := hb
    exact ⟨hc, b, fun z => hb z (hevery z)⟩

theorem zombieDamageNumber_eq_card_iff (hn : 0 < Fintype.card V) :
    zombieDamageNumber G = Fintype.card V ↔ FullDamage G := by
  rw [← canForceDamage_card_iff, canForceDamage_iff_le_number hn]
  exact ⟨fun h => h.ge, fun h => Nat.le_antisymm zombieDamageNumber_le_card h⟩

end ZombieDamage.FullGame
