import ZombieDamage.Graph

/-!
Source theory: Randy Davila introduced the zombie damage number and this game
in Definition 1 of "The Zombie Damage Number of a Graph", arXiv:2607.16382v1
(17 July 2026), https://doi.org/10.48550/arXiv.2607.16382.
Formalization author: Lennart Rudolph, with the AI assistance disclosed in the
accompanying manuscript. The game definition is attributed to Davila; see
../SOURCE_THEORY.md for the source-to-formalization attribution map.

The full one-zombie damage game. Both positions and the set of damaged
vertices are recorded. The zombie moves first, survivor passes are allowed,
and damage is credited to the source of a completed survivor move.
`ForcesWithin` is a contingent strategy tree: every legal zombie reply is
included. Bounds count survivor moves only. Reaching the objective ends the
finite-horizon obligation; later capture does not undo recorded damage.
No decomposition or main theorem is assumed by this module.
-/
namespace ZombieDamage.FullGame

inductive Phase where
  | zombie | survivor
  deriving DecidableEq, Repr

structure State (V : Type) where
  zombie : V
  survivor : V
  damaged : V → Prop

variable {V : Type} (G : Graph V)

def State.zombieTo (s : State V) (z : V) : State V :=
  { s with zombie := z }

def State.survivorTo (s : State V) (w : V) : State V :=
  ⟨s.zombie, w, fun v => s.damaged v ∨ v = s.survivor⟩

/-- Passes are allowed; next-turn safety is a strategy obligation. Moving onto
the zombie is omitted: a pass credits the same source before forced capture,
so this normalization preserves damage-only objectives (OccupiedVertexNormalization). -/
def LegalSurvivor (s : State V) (w : V) : Prop :=
  w ≠ s.zombie ∧ (w = s.survivor ∨ G.adj s.survivor w)

def LegalZombie (s : State V) (z : V) : Prop :=
  G.GeodesicReply s.zombie s.survivor z

/-- Nonterminal zombie turns have at least one legal reply, and every reply
must avoid capture and meet the continuation obligation. -/
inductive ForcesWithin (goal : Phase → State V → Prop) : Nat → Phase → State V → Prop where
  | done (budget : Nat) (phase : Phase) (s : State V) :
      goal phase s → ForcesWithin goal budget phase s
  | zombie (budget : Nat) (s : State V) :
      s.zombie ≠ s.survivor →
      (∃ z, LegalZombie G s z) →
      (∀ z, LegalZombie G s z → z ≠ s.survivor) →
      (∀ z, LegalZombie G s z →
        ForcesWithin goal budget .survivor (s.zombieTo z)) →
      ForcesWithin goal budget .zombie s
  | survivor (budget : Nat) (s : State V) (w : V) :
      s.zombie ≠ s.survivor → LegalSurvivor G s w →
      ForcesWithin goal budget .zombie (s.survivorTo w) →
      ForcesWithin goal (budget + 1) .survivor s

def initial (z v : V) : State V := ⟨z, v, fun _ => False⟩
def AllDamaged (s : State V) : Prop := ∀ v, s.damaged v

/-- Zombie chooses first; survivor sees that choice and selects a start;
then the zombie has the first turn. No prescribed zombie path is assumed. -/
def FullDamageWithin (budget : Nat) : Prop :=
  ∀ z, ∃ v, z ≠ v ∧
    ForcesWithin G (fun _ => AllDamaged) budget .zombie (initial z v)

def FullDamage : Prop := ∃ budget, FullDamageWithin G budget

namespace ForcesWithin
variable {G} {P Q : Phase → State V → Prop} {b : Nat} {phase : Phase} {s : State V}

theorem mono (h : ForcesWithin G P b phase s)
    (hPQ : ∀ p t, P p t → Q p t) : ForcesWithin G Q b phase s := by
  induction h with
  | done b p s hp => exact .done b p s (hPQ p s hp)
  | zombie b s hne hex hcap hnext ih =>
    exact ForcesWithin.zombie b s hne hex hcap ih
  | survivor b s w hne hlegal hnext ih =>
    exact .survivor b s w hne hlegal ih

theorem pad (h : ForcesWithin G P b phase s) (c : Nat) :
    ForcesWithin G P (b + c) phase s := by
  induction h with
  | done b p s hp => exact .done _ p s hp
  | zombie b s hne hex hcap hnext ih =>
    exact ForcesWithin.zombie _ s hne hex hcap ih
  | survivor b s w hne hlegal hnext ih =>
    have hn := ForcesWithin.survivor (b + c) s w hne hlegal ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn

/-- Sequential composition preserves game phases and adds survivor moves. -/
theorem bind (h : ForcesWithin G P b phase s) (c : Nat)
    (hPQ : ∀ p t, P p t → ForcesWithin G Q c p t) :
    ForcesWithin G Q (b + c) phase s := by
  induction h with
  | done b p s hp =>
    simpa [Nat.add_comm] using (hPQ p s hp).pad b
  | zombie b s hne hex hcap hnext ih =>
    exact ForcesWithin.zombie _ s hne hex hcap ih
  | survivor b s w hne hlegal hnext ih =>
    have hn := ForcesWithin.survivor (b + c) s w hne hlegal ih
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn

/-- Previously damaged vertices are preserved throughout the strategy. -/
theorem preserve_set (h : ForcesWithin G P b phase s) (D : V → Prop)
    (hD : ∀ v, D v → s.damaged v) :
    ForcesWithin G (fun p t => P p t ∧ ∀ v, D v → t.damaged v) b phase s := by
  induction h with
  | done b p s hp => exact .done b p s ⟨hp, hD⟩
  | zombie b s hne hex hcap hnext ih =>
    apply ForcesWithin.zombie b s hne hex hcap
    intro z hz
    exact ih z hz hD
  | survivor b s w hne hlegal hnext ih =>
    exact .survivor b s w hne hlegal (ih (fun v hv => Or.inl (hD v hv)))

end ForcesWithin

/-- Distance two gives a nonempty reply set and all replies avoid capture. -/
theorem twoApart_zombie_turn {u v : V} (h : G.TwoApart u v) :
    (∃ z, G.GeodesicReply u v z) ∧
    ∀ z, G.GeodesicReply u v z → z ≠ v := by
  constructor
  · obtain ⟨z, huz, hzv⟩ := h.2.2
    exact ⟨z, (G.geodesicReply_iff_commonNeighbor h).2 ⟨huz, hzv⟩⟩
  · intro z hz he
    have haz := (G.geodesicReply_iff_commonNeighbor h).1 hz
    subst z
    exact G.loopless v haz.2

/-- Routing steps are full-game steps with all replies and source damage. -/
theorem safe_step {P : Phase → State V → Prop} {b : Nat} (s : State V) (w : V)
    (huv : G.adj s.zombie s.survivor) (hvw : G.adj s.survivor w)
    (htwo : G.TwoApart s.zombie w)
    (hn : ∀ z, G.GeodesicReply s.zombie w z →
      ForcesWithin G P b .survivor ((s.survivorTo w).zombieTo z)) :
    ForcesWithin G P (b + 1) .survivor s := by
  have hzne : s.zombie ≠ s.survivor := by
    intro he
    exact G.loopless s.survivor (he ▸ huv)
  apply ForcesWithin.survivor b s w hzne ⟨htwo.1.symm, Or.inr hvw⟩
  apply ForcesWithin.zombie b (s.survivorTo w) htwo.1
  · exact (twoApart_zombie_turn G htwo).1
  · exact (twoApart_zombie_turn G htwo).2
  · exact hn

end ZombieDamage.FullGame
