import ZombieDamage.FullGame

/-! All-graph checks of two original-paper conventions. No numerical solver
or finite enumeration is used in these proofs. -/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

theorem adjacent_can_capture {u v : V} (h : G.adj u v) :
    G.GeodesicReply u v v := by
  refine ⟨h, 0, G.adjacency_distance_one h, ?_⟩
  exact ⟨Graph.Walk.nil v, fun _ _ => Nat.zero_le _⟩

/-- If an adjacent zombie has the next turn, no new goal can be forced before
it captures. In particular, arrival alone has not yet damaged the survivor's
vertex. This checks the zero-score convention in Davila's Proposition 3. -/
theorem first_capture_blocks_goal {P : Phase → State V → Prop}
    (s : State V) (hgoal : ¬ P .zombie s) (hadj : G.adj s.zombie s.survivor)
    (budget : Nat) : ¬ ForcesWithin G P budget .zombie s := by
  intro h
  cases h with
  | done _ _ _ hp => exact hgoal hp
  | zombie _ _ _ _ hcap _ =>
    exact hcap s.survivor (adjacent_can_capture G hadj) rfl

/-- A universal starting vertex prevents full damage at every finite horizon,
for every survivor placement. The order is not restricted to test fixtures. -/
theorem universal_vertex_not_fullDamage (u : V)
    (hu : ∀ v, u ≠ v → G.adj u v) : ¬ FullDamage G := by
  rintro ⟨b, hfull⟩
  obtain ⟨v, hne, hwin⟩ := hfull u
  have hgoal : ¬ (fun _ => AllDamaged) Phase.zombie (initial u v) := by
    intro h
    exact h u
  exact first_capture_blocks_goal G (initial u v) hgoal (hu v hne) b hwin

/-- A survivor can always earn its source vertex by passing after a
noncapturing zombie turn, even if the next zombie turn would capture it. -/
theorem pass_damages_source (s : State V) (hne : s.zombie ≠ s.survivor) :
    ForcesWithin G (fun _ t => t.damaged s.survivor) 1 .survivor s := by
  apply ForcesWithin.survivor 0 s s.survivor hne ⟨hne.symm, Or.inl rfl⟩
  exact .done 0 .zombie _ (Or.inr rfl)

end ZombieDamage.FullGame
