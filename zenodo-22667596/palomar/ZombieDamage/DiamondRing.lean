import ZombieDamage.Observation

/-!
The observation half of the ring-of-diamonds proposition, symbolic in the
number of diamonds. Parameter k gives t = k+3 diamonds; no small-graph census
is a premise. Not formalized here: cubicity, bridgelessness, clean connecting
edges, the cardinality corollary, or any full-damage conclusion.
-/

-- BEGIN DIAMOND DEFINITIONS
namespace ZombieDamage.DiamondRing

/-- a,b are the adjacent central vertices; c,d are the two nonadjacent ports. -/
inductive Role where
  | a | b | c | d
  deriving DecidableEq, Repr

def Vertex (k : Nat) := Fin (k + 3) × Role

def next {k : Nat} (i : Fin (k + 3)) : Fin (k + 3) :=
  ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩

/-- Literal K4-minus-cd adjacency: ten ordered edges, no loops. -/
def internal : Role → Role → Bool
  | .a, .b => true
  | .a, .c => true
  | .a, .d => true
  | .b, .a => true
  | .b, .c => true
  | .b, .d => true
  | .c, .a => true
  | .c, .b => true
  | .d, .a => true
  | .d, .b => true
  | _, _ => false

/-- Diamonds are joined only by d_i--c_(i+1), cyclically. -/
def adjacency {k : Nat} (u v : Vertex k) : Prop :=
  (u.1 = v.1 ∧ internal u.2 v.2 = true) ∨
  (u.2 = .d ∧ v.2 = .c ∧ next u.1 = v.1) ∨
  (u.2 = .c ∧ v.2 = .d ∧ next v.1 = u.1)

def graph (k : Nat) : Graph (Vertex k) where
  adj := adjacency
  symm := by
    rintro ⟨i, r⟩ ⟨j, s⟩ h
    rcases h with ⟨hij, hrs⟩ | ⟨hr, hs, hn⟩ | ⟨hr, hs, hn⟩
    · apply Or.inl
      refine ⟨hij.symm, ?_⟩
      have heq : internal r s = internal s r := by
        cases r <;> cases s <;> rfl
      exact heq ▸ hrs
    · exact Or.inr (Or.inr ⟨hs, hr, hn⟩)
    · exact Or.inr (Or.inl ⟨hs, hr, hn⟩)
  loopless := by
    rintro ⟨i, r⟩ h
    cases r <;> simp [adjacency, internal] at h

end ZombieDamage.DiamondRing
-- END DIAMOND DEFINITIONS

namespace ZombieDamage.DiamondRing

def swapRole : Role → Role
  | .a => .b
  | .b => .a
  | .c => .c
  | .d => .d

def swapAt {k : Nat} (i : Fin (k + 3)) (v : Vertex k) : Vertex k :=
  (v.1, if v.1 = i then swapRole v.2 else v.2)

theorem swapAt_involutive {k : Nat} (i : Fin (k + 3)) :
    ∀ v : Vertex k, swapAt i (swapAt i v) = v := by
  rintro ⟨j, r⟩
  by_cases hj : j = i <;> cases r <;> simp [swapAt, swapRole, hj]

theorem swapAt_preserves_adj {k : Nat} (i : Fin (k + 3)) :
    ∀ u v : Vertex k, (graph k).adj u v →
      (graph k).adj (swapAt i u) (swapAt i v) := by
  rintro ⟨j, r⟩ ⟨l, s⟩ h
  by_cases hj : j = i <;> by_cases hl : l = i <;>
    cases r <;> cases s <;>
    simp_all [graph, adjacency, internal, swapAt, swapRole]

theorem swapAt_fixed {k : Nat} (i : Fin (k + 3)) (v : Vertex k)
    (ha : v ≠ (i, .a)) (hb : v ≠ (i, .b)) : swapAt i v = v := by
  rcases v with ⟨j, r⟩
  by_cases hj : j = i
  · subst j
    cases r <;> simp_all [swapAt, swapRole]
  · simp [swapAt, hj]

/-- Every resolving sensor set must hit the central pair of EVERY diamond.
This is the all-parameter sensor-pair requirement used by the paper; the
additional cardinality count and the pursuit theorem are not bundled here. -/
theorem central_pair_sensor (k : Nat) (S : Vertex k → Prop)
    (h : Nat) (hh : 1 ≤ h) (hrec : (graph k).Recovers S h)
    (i : Fin (k + 3)) : S (i, .a) ∨ S (i, .b) := by
  classical
  apply Classical.byContradiction
  intro hmiss
  have hfix : ∀ v, S v → swapAt i v = v := by
    intro v hs
    apply swapAt_fixed i v
    · intro he
      exact hmiss (Or.inl (he ▸ hs))
    · intro he
      exact hmiss (Or.inr (he ▸ hs))
  have hne : (i, Role.a) ≠ (i, Role.b) := by
    intro he
    have hr : Role.a = Role.b := congrArg Prod.snd he
    cases hr
  have hab : swapAt i (i, Role.a) = (i, Role.b) := by
    simp [swapAt, swapRole]
  exact (graph k).involution_blocks_recovery
    (swapAt i) (swapAt_involutive i) (swapAt_preserves_adj i)
    S hfix (i, Role.a) (i, Role.b) hne hab h hh hrec

end ZombieDamage.DiamondRing
