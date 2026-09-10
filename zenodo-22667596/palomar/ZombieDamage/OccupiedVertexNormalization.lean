import ZombieDamage.FullGame

/-!
Damage-only objectives are unchanged if the survivor may enter the occupied
zombie vertex. Such a move ends play after crediting its source. Replacing
it by a pass gives exactly the same damaged set within the same move budget.
This module does not assert equivalence for position-sensitive objectives.
-/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

/-- The full game with every neighboring survivor destination permitted.
At coincident positions only an already achieved objective can hold: both
nonterminal constructors require distinct positions. -/
inductive PermissiveForces (objective : (V → Prop) → Prop) :
    Nat → Phase → State V → Prop where
  | done (b : Nat) (p : Phase) (s : State V) :
      objective s.damaged → PermissiveForces objective b p s
  | zombie (b : Nat) (s : State V) :
      s.zombie ≠ s.survivor →
      (∃ z, LegalZombie G s z) →
      (∀ z, LegalZombie G s z → z ≠ s.survivor) →
      (∀ z, LegalZombie G s z →
        PermissiveForces objective b .survivor (s.zombieTo z)) →
      PermissiveForces objective b .zombie s
  | survivor (b : Nat) (s : State V) (w : V) :
      s.zombie ≠ s.survivor →
      (w = s.survivor ∨ G.adj s.survivor w) →
      PermissiveForces objective b .zombie (s.survivorTo w) →
      PermissiveForces objective (b + 1) .survivor s

namespace PermissiveForces
variable {G} {objective : (V → Prop) → Prop} {b : Nat}
    {p : Phase} {s : State V}

theorem normalize (h : PermissiveForces G objective b p s) :
    ForcesWithin G (fun _ t => objective t.damaged) b p s := by
  induction h with
  | done b p s hobj => exact .done b p s hobj
  | zombie b s hne hex hcap hnext ih =>
    exact ForcesWithin.zombie b s hne hex hcap ih
  | survivor b s w hne hlegal hnext ih =>
    by_cases hw : w = s.zombie
    · have hobj : objective (s.survivorTo w).damaged := by
        cases hnext with
        | done _ _ _ hobj => exact hobj
        | zombie _ _ hdistinct _ _ _ =>
          exact False.elim (hdistinct hw.symm)
      exact ForcesWithin.survivor b s s.survivor hne
        ⟨hne.symm, Or.inl rfl⟩ (.done b .zombie _ hobj)
    · exact ForcesWithin.survivor b s w hne ⟨hw, hlegal⟩ ih

theorem of_normalized
    (h : ForcesWithin G (fun _ t => objective t.damaged) b p s) :
    PermissiveForces G objective b p s := by
  induction h with
  | done b p s hobj => exact .done b p s hobj
  | zombie b s hne hex hcap hnext ih =>
    exact PermissiveForces.zombie b s hne hex hcap ih
  | survivor b s w hne hlegal hnext ih =>
    exact PermissiveForces.survivor b s w hne hlegal.2 ih

/-- Normalization preserves every objective depending only on the damaged set,
at every state, phase and survivor-move budget. -/
theorem iff_normalized :
    PermissiveForces G objective b p s ↔
    ForcesWithin G (fun _ t => objective t.damaged) b p s :=
  ⟨normalize, of_normalized⟩

end PermissiveForces

/-- In particular the normalization preserves the original full-damage claim,
including the initial zombie/survivor quantifier order. -/
theorem fullDamage_iff_permissive : FullDamage G ↔
    ∃ b, ∀ z, ∃ v, z ≠ v ∧
      PermissiveForces G (fun D => ∀ x, D x) b .zombie (initial z v) := by
  constructor
  · rintro ⟨b, h⟩
    refine ⟨b, fun z => ?_⟩
    obtain ⟨v, hne, hw⟩ := h z
    exact ⟨v, hne, PermissiveForces.of_normalized hw⟩
  · rintro ⟨b, h⟩
    refine ⟨b, fun z => ?_⟩
    obtain ⟨v, hne, hw⟩ := h z
    exact ⟨v, hne, hw.normalize⟩

end ZombieDamage.FullGame
