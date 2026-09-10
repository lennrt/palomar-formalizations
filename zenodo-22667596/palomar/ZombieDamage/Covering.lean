import ZombieDamage.FullGame

/-!
The scheduling part of the global argument, proved for the full game.
The one-target contract and initialization are EXPLICIT prerequisites here;
this theorem does not establish those contracts for bridgeless cubic graphs.
-/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

def TargetContract (I : State V → Prop) (cost : Nat) : Prop :=
  ∀ s, I s → ∀ v, ForcesWithin G
    (fun p t => p = .survivor ∧ I t ∧ t.damaged v) cost .survivor s

def Serves (I : State V → Prop) (targets : List V)
    (p : Phase) (s : State V) : Prop :=
  p = .survivor ∧ I s ∧ ∀ v, v ∈ targets → s.damaged v

/-- Adaptive strategies can serve any finite target list in order. The
proof preserves earlier damage while allowing every later zombie reply. -/
theorem serve_list (I : State V → Prop) (cost : Nat)
    (hc : TargetContract G I cost) (targets : List V)
    (s : State V) (hs : I s) :
    ForcesWithin G (Serves I targets) (targets.length * cost) .survivor s := by
  induction targets generalizing s with
  | nil =>
    apply ForcesWithin.done
    exact ⟨rfl, hs, by simp⟩
  | cons v vs ih =>
    have ht := hc s hs v
    have hb := ht.bind (Q := Serves I (v :: vs)) (vs.length * cost) (fun p t hp => by
      obtain ⟨hphase, hi, hv⟩ := hp
      subst p
      have ht := (ih t hi).preserve_set (fun w => w = v)
        (fun w hw => hw ▸ hv)
      apply ht.mono
      intro p u hu
      obtain ⟨⟨hphase, hi, hvs⟩, hv⟩ := hu
      refine ⟨hphase, hi, ?_⟩
      intro w hw
      rcases List.mem_cons.mp hw with h | h
      · exact hv w h
      · exact hvs w h)
    simpa [List.length_cons, Nat.add_mul, Nat.add_comm] using hb

/-- Initialization and one-target routing give full damage. Both input
contracts are stated in the same full game, with the correct initial order. -/
theorem fullDamage_of_contract (I : State V → Prop) (cost startCost : Nat)
    (targets : List V) (hevery : ∀ v, v ∈ targets)
    (hc : TargetContract G I cost)
    (hinit : ∀ z, ∃ v, z ≠ v ∧ ForcesWithin G
      (fun p t => p = .survivor ∧ I t) startCost .zombie (initial z v)) :
    FullDamageWithin G (startCost + targets.length * cost) := by
  intro z
  obtain ⟨v, hne, hstart⟩ := hinit z
  refine ⟨v, hne, ?_⟩
  apply hstart.bind (targets.length * cost)
  intro p s hs
  obtain ⟨hp, hi⟩ := hs
  subst p
  apply (serve_list G I cost hc targets s hi).mono
  intro _ t ht w
  exact ht.2.2 w (hevery w)

/-- Exact arithmetic behind the paper's 2n(n+1) first-cover bound. This is
conditional on actual initialization and target contracts, not a theorem
asserting those contracts for all graphs. -/
theorem twice_order_bound (n : Nat) :
    2 * n + n * (2 * n) = 2 * n * (n + 1) := by
  rw [Nat.mul_add, Nat.mul_one]
  rw [Nat.add_comm]
  congr 1
  rw [Nat.mul_comm n (2 * n)]

end ZombieDamage.FullGame
