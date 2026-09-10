import Std

/-!
# Independent game statement surface

The twenty-four intentional holes below state the previously verified game,
metric routing and observation results independently of their implementation.
This module is checked by verification/game-comparator.json and is never
imported by any proof. The complete Conjecture 24 proof and full-game library
are selected together by the root comparator.json; see Challenge.lean.

Source game and zombie damage number: Randy Davila, arXiv:2607.16382v1.
Formalization: Lennart Rudolph, with the AI assistance disclosed in README.md.
-/
namespace ZombieDamage
structure Graph (V : Type) where
  adj : V → V → Prop
  symm : ∀ {u v}, adj u v → adj v u
  loopless : ∀ v, ¬ adj v v

namespace Graph
variable {V : Type} (G : Graph V)

inductive Walk : Nat → V → V → Prop where
  | nil (v : V) : Walk 0 v v
  | cons {k : Nat} {u v w : V} :
      G.adj u v → Walk k v w → Walk (Nat.succ k) u w

def Distance (k : Nat) (u v : V) : Prop :=
  G.Walk k u v ∧ ∀ j, G.Walk j u v → k ≤ j

def TwoApart (u w : V) : Prop :=
  u ≠ w ∧ ¬ G.adj u w ∧ ∃ v, G.adj u v ∧ G.adj v w

def GeodesicReply (u w x : V) : Prop :=
  G.adj u x ∧ ∃ d, G.Distance (Nat.succ d) u w ∧ G.Distance d x w

/-- Absence of actual triangles and quadrilaterals through the edge ab.
The two displayed inequalities, together with looplessness of the four edges,
ensure four distinct vertices in the quadrilateral clause. -/
def Clean (a b : V) : Prop :=
  G.adj a b ∧
  (∀ c, ¬ (G.adj b c ∧ G.adj c a)) ∧
  (∀ c d, a ≠ c → b ≠ d →
    ¬ (G.adj b c ∧ G.adj c d ∧ G.adj d a))

/-- An edge lying on a triangle or quadrilateral: on an actual edge this is
exactly the negation of `Clean`. No ambient graph or cycle oracle is assumed. -/
def ShortAdj (u v : V) : Prop := G.adj u v ∧ ¬ G.Clean u v

end Graph

structure Position (N : Nat) where
  seen : Bool
  zombie : Fin N
  survivor : Fin N
  deriving DecidableEq, Repr

structure Task (N : Nat) where
  adj : Fin N → Fin N → Bool
  inside : Fin N → Bool
  target : Option (Fin N)
  allowedExit : Fin N → Bool

namespace Task
variable {N : Nat}

def GoodGraph (T : Task N) : Prop :=
  (∀ u v, T.adj u v = T.adj v u) ∧ ∀ u, T.adj u u = false

instance (T : Task N) : Decidable T.GoodGraph := by
  unfold GoodGraph
  infer_instance

def graph (T : Task N) (h : T.GoodGraph) : Graph (Fin N) where
  adj u v := T.adj u v = true
  symm := by
    intro u v huv
    rw [← h.1 u v]
    exact huv
  loopless := by
    intro v hv
    rw [h.2 v] at hv
    cases hv

/-- Targets are credited on departure from the SOURCE survivor vertex. -/
def afterSeen (T : Task N) (s : Position N) : Bool :=
  s.seen || match T.target with
    | none => true
    | some t => decide (s.survivor = t)

def next (T : Task N) (s : Position N) (w z : Fin N) : Position N :=
  ⟨T.afterSeen s, z, w⟩

def Safe (T : Task N) (s : Position N) (w : Fin N) : Prop :=
  T.inside s.survivor = true ∧
  T.adj s.zombie s.survivor = true ∧
  T.adj s.survivor w = true ∧
  s.zombie ≠ w ∧ T.adj s.zombie w = false

def Reply (T : Task N) (s : Position N) (w z : Fin N) : Prop :=
  T.adj s.zombie z = true ∧ T.adj z w = true

def Exit (T : Task N) (s : Position N) (w : Fin N) : Prop :=
  T.inside w = false ∧ T.allowedExit w = true ∧ T.afterSeen s = true

instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Safe s w) := by unfold Safe; infer_instance
instance (T : Task N) (s : Position N) (w z : Fin N) :
    Decidable (T.Reply s w z) := by unfold Reply; infer_instance
instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Exit s w) := by unfold Exit; infer_instance

/-- Finite-horizon forcing in the shortest-walk metric. `budget` counts survivor
moves including the exit; an early exit may leave some budget unused.
The step constructor includes all geodesic replies and requires at least one,
so a position with no replies is not a vacuous winning position. -/
inductive MetricForcesWithin (T : Task N) (hg : T.GoodGraph) :
    Nat → Position N → Prop where
  | exit (budget : Nat) (s : Position N) (w : Fin N) :
      0 < budget → T.Safe s w → T.Exit s w →
      MetricForcesWithin T hg budget s
  | step (budget : Nat) (s : Position N) (w : Fin N) :
      T.Safe s w → T.inside w = true →
      (∃ z, (T.graph hg).GeodesicReply s.zombie w z) →
      (∀ z, (T.graph hg).GeodesicReply s.zombie w z →
        MetricForcesWithin T hg budget (T.next s w z)) →
      MetricForcesWithin T hg (Nat.succ budget) s

end Task
end ZombieDamage

namespace ZombieDamage

/-- Exactly the five graphs in the exceptional-component routing lemma. -/
inductive Gadget where
  | k23 | k33e | prism3e | cubeV | cubeE
  deriving DecidableEq, Repr

namespace Gadget

/-- Number of internal vertices, excluding auxiliary port leaves. -/
abbrev order : Gadget → Nat
  | .k23 => 5 | .k33e => 6 | .prism3e => 6 | .cubeV => 7 | .cubeE => 8

/-- Unordered internal edges with the literal labels used in the paper. -/
def edges : Gadget → List (Nat × Nat)
  | .k23 => [(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)]
  | .k33e => [(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
  | .prism3e => [(0,2),(1,2),(3,4),(3,5),(4,5),(0,3),(1,4),(2,5)]
  | .cubeV => [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
  | .cubeE => [(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]

/-- The pairs (port, auxiliary leaf). The ports are the degree-two vertices. -/
abbrev leaves : Gadget → List (Nat × Nat)
  | .k23 => [(2,5),(3,6),(4,7)]
  | .k33e => [(0,6),(3,7)]
  | .prism3e => [(0,6),(1,7)]
  | .cubeV => [(3,7),(5,8),(6,9)]
  | .cubeE => [(0,8),(1,9)]

/-- Internal vertices followed by one different leaf for each port. -/
abbrev size (g : Gadget) : Nat := g.order + g.leaves.length
abbrev Vertex (g : Gadget) := Fin g.size

/-- Undirected adjacency of the leaf-augmented finite graph. -/
def adj (g : Gadget) (u v : g.Vertex) : Bool :=
  decide ((u.val, v.val) ∈ g.edges ++ g.leaves ∨
          (v.val, u.val) ∈ g.edges ++ g.leaves)

/-- The survivor is inside the component exactly at an internal vertex. -/
def inside (g : Gadget) (v : g.Vertex) : Bool := decide (v.val < g.order)

/-- A port is an internal endpoint in the displayed leaf list. -/
def port (g : Gadget) (v : g.Vertex) : Bool :=
  g.leaves.any (fun e => decide (e.1 = v.val))

/-- The leaf of a port. Values on nonports are immaterial: every public
routing theorem explicitly assumes the entering/exiting vertices are ports. -/
def stub : (g : Gadget) → g.Vertex → g.Vertex
  | .k23, p => if p.val = 2 then 5 else if p.val = 3 then 6 else 7
  | .k33e, p => if p.val = 0 then 6 else 7
  | .prism3e, p => if p.val = 0 then 6 else 7
  | .cubeV, p => if p.val = 3 then 7 else if p.val = 5 then 8 else 9
  | .cubeE, p => if p.val = 0 then 8 else 9

/-- Prescribed-exit task with no target; only the named port leaf is allowed. -/
def exitTask (g : Gadget) (q : g.Vertex) : Task g.size where
  adj := g.adj
  inside := g.inside
  target := none
  allowedExit v := decide (v = g.stub q)

/-- Target task: leave the target safely, then exit at any NONENTRY port. -/
def targetTask (g : Gadget) (p t : g.Vertex) : Task g.size where
  adj := g.adj
  inside := g.inside
  target := some t
  allowedExit v := g.leaves.any
    (fun e => decide (e.1 ≠ p.val) && decide (e.2 = v.val))

/-- Adjacent position immediately after a zombie turn at an entry. -/
def entry (g : Gadget) (p : g.Vertex) : Position g.size :=
  ⟨false, g.stub p, p⟩

/-- A metric survivor strategy for (A), with at most twice the internal order
many survivor moves. Symmetry and looplessness are included, not presumed. -/
def RouteExit (g : Gadget) (p q : g.Vertex) : Prop :=
  ∃ hg : (g.exitTask q).GoodGraph,
    (g.exitTask q).MetricForcesWithin hg (2 * g.order) (g.entry p)

/-- A metric survivor strategy for (B), with the same explicit time bound. -/
def RouteTarget (g : Gadget) (p t : g.Vertex) : Prop :=
  ∃ hg : (g.targetTask p t).GoodGraph,
    (g.targetTask p t).MetricForcesWithin hg (2 * g.order) (g.entry p)

end Gadget
end ZombieDamage

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)
theorem geodesicReply_iff_commonNeighbor {u w x : V}
    (h : G.TwoApart u w) :
    G.GeodesicReply u w x ↔ G.adj u x ∧ G.adj x w := by
  sorry

theorem cleanEdge_forces_reply {u v w x : V}
    (hc : G.Clean v w) (huv : G.adj u v) (huw : u ≠ w) :
    G.GeodesicReply u w x ↔ x = v := by
  sorry

theorem short_twoStep_closed {u v w : V}
    (huv : G.ShortAdj u v) (hvw : G.ShortAdj v w) (hne : u ≠ w) :
    (G.adj u w → G.ShortAdj u w) ∧
    (∀ x, G.adj u x → G.adj x w →
      G.ShortAdj u x ∧ G.ShortAdj x w) := by
  sorry
end ZombieDamage.Graph

namespace ZombieDamage.Verified
/-- All port and target choices, with no symmetry or certificate-validity
hypothesis and with at most twice the component order many survivor moves. -/
theorem finite_component_routing (g : Gadget) :
    (∀ p q : g.Vertex, g.port p = true → g.port q = true → p ≠ q →
      g.RouteExit p q) ∧
    (∀ p t : g.Vertex, g.port p = true → g.inside t = true →
      g.RouteTarget p t) := by
  sorry
end ZombieDamage.Verified

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

/-- Multiplicity of radius r in the distance histogram of a finite population.
Order is ignored and repeated vertices are retained. -/
noncomputable def shellCount (r : Nat) (s : V) (population : List V) : Nat := by
  classical
  exact (population.filter (fun v => decide (G.Distance r s v))).length

/-- Sensor identities are retained; target labels and cross-sensor matching
are not. Equality is required at every nonnegative integral radius. -/
def SameShellData (S : V → Prop) (xs ys : List V) : Prop :=
  ∀ s, S s → ∀ r, G.shellCount r s xs = G.shellCount r s ys

/-- Recovery of all populations of mass at most h, including multiplicities
and the empty population. Equality of populations is list permutation. -/
def Recovers (S : V → Prop) (h : Nat) : Prop :=
  ∀ xs ys : List V, xs.length ≤ h → ys.length ≤ h →
    G.SameShellData S xs ys → xs.Perm ys

end ZombieDamage.Graph

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

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)
theorem involution_blocks_recovery (f : V → V)
    (hinv : ∀ v, f (f v) = v)
    (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    (S : V → Prop) (hfix : ∀ s, S s → f s = s)
    (a b : V) (hne : a ≠ b) (hab : f a = b)
    (h : Nat) (hh : 1 ≤ h) : ¬ G.Recovers S h := by
  sorry
end ZombieDamage.Graph

namespace ZombieDamage.DiamondRing
theorem central_pair_sensor (k : Nat) (S : Vertex k → Prop)
    (h : Nat) (hh : 1 ≤ h) (hrec : (graph k).Recovers S h)
    (i : Fin (k + 3)) : S (i, .a) ∨ S (i, .b) := by
  sorry
end ZombieDamage.DiamondRing

/-! Source theory: Randy Davila, The Zombie Damage Number of a Graph,
arXiv:2607.16382v1, Definition 1 and the original results identified below.
Formalization author: Lennart Rudolph, with disclosed AI assistance.
Full-game extension. The universal short-cycle classification, quotient
construction and the final Conjecture 24 theorem are NOT supplied by these
statements. Open strips have all-length local routing contracts. The contract theorem lists
its routing/initialization prerequisites explicitly. Positive closed-family
results and the four exceptions use the complete game defined below. -/

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
end ZombieDamage.FullGame

namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

inductive ForcesEventually (goal : Phase → State V → Prop) : Phase → State V → Prop where
  | done (p : Phase) (s : State V) : goal p s → ForcesEventually goal p s
  | zombie (s : State V) : s.zombie ≠ s.survivor →
      (∃ z, LegalZombie G s z) →
      (∀ z, LegalZombie G s z → z ≠ s.survivor) →
      (∀ z, LegalZombie G s z → ForcesEventually goal .survivor (s.zombieTo z)) →
      ForcesEventually goal .zombie s
  | survivor (s : State V) (w : V) : s.zombie ≠ s.survivor →
      LegalSurvivor G s w → ForcesEventually goal .zombie (s.survivorTo w) →
      ForcesEventually goal .survivor s
end ZombieDamage.FullGame

namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)
def EventualFullDamage : Prop := ∀ z, ∃ v, z≠v ∧
  ForcesEventually G (fun _ => AllDamaged) .zombie (initial z v)
end ZombieDamage.FullGame

namespace ZombieDamage.Task
variable {N : Nat} (T : Task N)
def BoundaryLeaves : Prop := ∀ v, T.inside v=false →
  ∀ u w, T.adj v u=true → T.adj v w=true → u=w

def FlagComplete (s : Position N) (D : Fin N → Prop) : Prop :=
  ∀ v, T.target=some v → D v → s.seen=true
end ZombieDamage.Task

namespace ZombieDamage.Cyclic
variable {n : Nat}

def shift (hn : 0 < n) (i : Fin n) (a : Nat) : Fin n :=
  ⟨(i.val + a) % n, Nat.mod_lt _ hn⟩

theorem shift_zero (hn : 0 < n) (i : Fin n) : shift hn i 0 = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]

theorem shift_add (hn : 0 < n) (i : Fin n) (a b : Nat) :
    shift hn (shift hn i a) b = shift hn i (a+b) := by
  apply Fin.ext
  simp [shift, Nat.mod_add_mod, Nat.add_assoc]

theorem shift_ne (hn : 0 < n) (i : Fin n) (a : Nat)
    (ha : 0 < a) (han : a < n) : shift hn i a ≠ i := by
  intro he
  have hv := congrArg Fin.val he
  change (i.val+a)%n=i.val at hv
  by_cases hlt : i.val+a<n
  · rw [Nat.mod_eq_of_lt hlt] at hv
    omega
  · have hge : n ≤ i.val+a := by omega
    have hsmall : i.val+a-n<n := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsmall] at hv
    omega

theorem shift_n (hn : 0 < n) (i : Fin n) : shift hn i n = i := by
  apply Fin.ext
  simp [shift, Nat.mod_eq_of_lt i.isLt]
end ZombieDamage.Cyclic

namespace ZombieDamage.CycleGame
open Cyclic FullGame

variable {n : Nat}
theorem pos (hn : 5 ≤ n) : 0 < n := by omega

def graph (hn : 5 ≤ n) : Graph (Fin n) where
  adj u v := v = shift (pos hn) u 1 ∨ u = shift (pos hn) v 1
  symm := fun h => h.symm
  loopless := by
    intro v hv
    have hne := shift_ne (pos hn) v 1 (by omega) (by omega)
    rcases hv with h | h <;> exact hne h.symm
end ZombieDamage.CycleGame

namespace ZombieDamage.MobiusGame
open Cyclic FullGame
variable {m : Nat}
theorem pos (hm : 4 ≤ m) : 0 < 2*m := by omega

def adjacency (hm : 4 ≤ m) (u v : Fin (2*m)) : Prop :=
  v = shift (pos hm) u 1 ∨ v = shift (pos hm) u (2*m-1) ∨
    v = shift (pos hm) u m

def graph (hm : 4 ≤ m) : Graph (Fin (2*m)) where
  adj := adjacency hm
  symm := by
    intro u v h
    rcases h with h | h | h
    · apply Or.inr; apply Or.inl
      rw [h, shift_add]
      have he : 1+(2*m-1)=2*m := by omega
      rw [he, shift_n]
    · apply Or.inl
      rw [h, shift_add]
      have he : 2*m-1+1=2*m := by omega
      rw [he, shift_n]
    · apply Or.inr; apply Or.inr
      rw [h, shift_add]
      have he : m+m=2*m := by omega
      rw [he, shift_n]
  loopless := by
    intro u h
    rcases h with h | h | h
    · exact shift_ne (pos hm) u 1 (by omega) (by omega) h.symm
    · exact shift_ne (pos hm) u (2*m-1) (by omega) (by omega) h.symm
    · exact shift_ne (pos hm) u m (by omega) (by omega) h.symm
end ZombieDamage.MobiusGame

namespace ZombieDamage.PrismGame
open Cyclic FullGame
variable {m : Nat}

def graph (hm : 5 ≤ m) : Graph (Fin m × Bool) where
  adj u v := (u.2=v.2 ∧ (CycleGame.graph hm).adj u.1 v.1) ∨
    (u.1=v.1 ∧ u.2≠v.2)
  symm := by
    intro u v h
    rcases h with ⟨hs,hi⟩ | ⟨hi,hs⟩
    · exact Or.inl ⟨hs.symm,(CycleGame.graph hm).symm hi⟩
    · exact Or.inr ⟨hi.symm,hs.symm⟩
  loopless := by
    intro u h
    rcases h with ⟨_,hi⟩ | ⟨_,hs⟩
    · exact (CycleGame.graph hm).loopless u.1 hi
    · exact hs rfl
end ZombieDamage.PrismGame

namespace ZombieDamage.Exceptions
open FullGame
inductive Kind where
  | k4 | k33 | prism3 | cube
  deriving DecidableEq, Repr
abbrev order : Kind → Nat
  | .k4 => 4 | .k33 => 6 | .prism3 => 6 | .cube => 8
abbrev Vertex (g : Kind) := Fin (order g)

def edge (g : Kind) (u v : Vertex g) : Bool :=
  match g with
  | .k4 => u != v
  | .k33 => (u.val<3 && v.val≥3) || (v.val<3 && u.val≥3)
  | .prism3 => u != v && (u.val/3 == v.val/3 || u.val%3 == v.val%3)
  | .cube => decide ((u.val ^^^ v.val) ∈ [1,2,4])

def graph (g : Kind) : Graph (Vertex g) where
  adj u v := edge g u v = true
  symm := by cases g <;> decide
  loopless := by cases g <;> decide

instance (g : Kind) (u v : Vertex g) : Decidable ((graph g).adj u v) := by
  change Decidable (edge g u v = true)
  infer_instance
end ZombieDamage.Exceptions

namespace ZombieDamage.Task
open FullGame
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)

def TargetDamaged (D : Fin N → Prop) : Prop :=
  ∀ v, T.target = some v → D v

def FlagSound (s : Position N) (D : Fin N → Prop) : Prop :=
  s.seen = true → T.TargetDamaged D

def fullState (s : Position N) (D : Fin N → Prop) : State (Fin N) :=
  ⟨s.zombie, s.survivor, D⟩

def FullExit (phase : Phase) (s : State (Fin N)) : Prop :=
  phase = .survivor ∧ T.inside s.survivor = false ∧
    T.allowedExit s.survivor = true ∧ T.TargetDamaged s.damaged
end ZombieDamage.Task

namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

def TargetContract (I : State V → Prop) (cost : Nat) : Prop :=
  ∀ s, I s → ∀ v, ForcesWithin G
    (fun p t => p = .survivor ∧ I t ∧ t.damaged v) cost .survivor s

def Serves (I : State V → Prop) (targets : List V)
    (p : Phase) (s : State V) : Prop :=
  p = .survivor ∧ I s ∧ ∀ v, v ∈ targets → s.damaged v
end ZombieDamage.FullGame

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

structure MetricCertificate where
  value : V → V → Nat
  zero_self : ∀ u, value u u = 0
  zero_eq : ∀ u v, value u v = 0 → u = v
  edge_bound : ∀ u x v, G.adj u x → value u v ≤ value x v + 1
  descent : ∀ u v, 0 < value u v →
    ∃ x, G.adj u x ∧ value u v = value x v + 1
end ZombieDamage.Graph

namespace ZombieDamage

structure GraphIso {V W : Type} (G : Graph V) (H : Graph W) where
  toFun : V → W
  invFun : W → V
  left_inv : ∀ v, invFun (toFun v)=v
  right_inv : ∀ w, toFun (invFun w)=w
  adjacency : ∀ u v, G.adj u v ↔ H.adj (toFun u) (toFun v)
end ZombieDamage

namespace ZombieDamage
variable {N : Nat} {V : Type}

structure ShortComponentModel (T : Task N) (G : Graph V) where
  map : Fin N → V
  internal_injective : ∀ u v, T.inside u=true → T.inside v=true → map u=map v → u=v
  edges : ∀ u v, T.adj u v=true → G.adj (map u) (map v)
  internal_edges : ∀ u v, T.inside u=true → T.inside v=true →
    (T.adj u v=true ↔ G.ShortAdj (map u) (map v))
  clean_boundary : ∀ u v, T.inside u=true → T.inside v=false →
    T.adj u v=true → G.Clean (map u) (map v)
  one_stub : ∀ u v w, T.inside v=true → T.inside u=false → T.inside w=false →
    T.adj u v=true → T.adj v w=true → u=w
  closed : ∀ u, T.inside u=true → ∀ x, G.ShortAdj (map u) x →
    ∃ v, T.inside v=true ∧ map v=x
end ZombieDamage

namespace ZombieDamage.ShortComponentModel
variable {N : Nat} {V : Type} {T : Task N} {G : Graph V}
variable (M : ShortComponentModel T G) (hg : T.GoodGraph)
def state (s : Position N) (D : V → Prop) : FullGame.State V :=
  ⟨M.map s.zombie,M.map s.survivor,D⟩

def FlagSound (s : Position N) (D : V → Prop) : Prop :=
  s.seen=true → ∀ v, T.target=some v → D (M.map v)

def Exit (phase : FullGame.Phase) (s : FullGame.State V) : Prop :=
  phase = .survivor ∧ G.Clean s.zombie s.survivor ∧
    (∃ w, T.inside w=false ∧ T.allowedExit w=true ∧ s.survivor=M.map w) ∧
    ∀ v, T.target=some v → s.damaged (M.map v)
end ZombieDamage.ShortComponentModel

namespace ZombieDamage.OpenStrip
variable (m : Nat) (left right : Bool)

def Adj (u v : Nat) : Prop :=
  (u<m ∧ v<m ∧ (u+1=v ∨ v+1=u)) ∨
  (m≤u ∧ u<2*m ∧ m≤v ∧ v<2*m ∧ (u+1=v ∨ v+1=u)) ∨
  (u<m ∧ v=u+m) ∨ (v<m ∧ u=v+m) ∨
  (left=true ∧ ((u=2*m ∧ (v=0 ∨ v=m ∨ v=2*m+6)) ∨
                 (v=2*m ∧ (u=0 ∨ u=m ∨ u=2*m+6)))) ∨
  (right=true ∧ ((u=2*m+1 ∧ (v=m-1 ∨ v=2*m-1 ∨ v=2*m+7)) ∨
                  (v=2*m+1 ∧ (u=m-1 ∨ u=2*m-1 ∨ u=2*m+7)))) ∨
  (left=false ∧ ((u=0 ∧ v=2*m+2) ∨ (v=0 ∧ u=2*m+2) ∨
                  (u=m ∧ v=2*m+3) ∨ (v=m ∧ u=2*m+3))) ∨
  (right=false ∧ ((u=m-1 ∧ v=2*m+4) ∨ (v=m-1 ∧ u=2*m+4) ∨
                   (u=2*m-1 ∧ v=2*m+5) ∨ (v=2*m-1 ∧ u=2*m+5)))

instance (u v : Nat) : Decidable (Adj m left right u v) := by unfold Adj; infer_instance

def graph (hm : 2≤m) : Graph (Fin (2*m+8)) where
  adj u v := Adj m left right u.val v.val
  symm := by
    intro u v h
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨h.2.1,h.1,h.2.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.1,h.2.2.2.2.symm⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,h.2.symm⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,h.2.symm⟩)))))
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨h.1,?_⟩
      rcases h.2 with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨h.1,?_⟩
      rcases h.2 with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  loopless := by intro u h; unfold Adj at h; omega

def rail (b : Bool) (i : Nat) (hi : i<m) : Fin (2*m+8) :=
  ⟨if b then m+i else i,by split <;> omega⟩
def cap (b : Bool) : Fin (2*m+8) := ⟨if b then 2*m+1 else 2*m,by split <;> omega⟩
def stub (side b : Bool) : Fin (2*m+8) :=
  ⟨2*m+2+(if side then 2 else 0)+(if b then 1 else 0),by split <;> split <;> omega⟩
def capStub (side : Bool) : Fin (2*m+8) := ⟨2*m+6+(if side then 1 else 0),by split <;> omega⟩
end ZombieDamage.OpenStrip

namespace ZombieDamage.OpenStrip
open FullGame

/-- A boundary incidence is a side and either its cap or one of its rails.
Inactive incidences are excluded by `Active`; they are never local targets. -/
abbrev Port := Bool × Option Bool

def flipPort (p : Port) : Port := (!p.1,p.2)
def capOn (left right side : Bool) : Bool := if side then right else left

def Active (left right : Bool) (p : Port) : Prop :=
  capOn left right p.1 = p.2.isNone

def portVertex (m : Nat) (hm : 2≤m) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => cap m p.1
  | some b => rail m b (if p.1 then m-1 else 0) (by split <;> omega)

def portStub (m : Nat) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => capStub m p.1
  | some b => stub m p.1 b

def Internal (m : Nat) (left right : Bool) (x : Fin (2*m+8)) : Prop :=
  (∃ b i, ∃ hi : i<m, x=rail m b i hi) ∨
  (left=true ∧ x=cap m false) ∨ (right=true ∧ x=cap m true)

def ExitAt (m : Nat) (hm : 2≤m) (q : Port) (phase : Phase) (s : State (Fin (2*m+8))) : Prop :=
  phase=.survivor ∧ s.zombie=portVertex m hm q ∧ s.survivor=portStub m q

def TargetExit (m : Nat) (hm : 2≤m) (left right : Bool) (entry : Port)
    (x : Fin (2*m+8)) (phase : Phase) (s : State (Fin (2*m+8))) : Prop :=
  ∃ q, Active left right q ∧ q≠entry ∧ ExitAt m hm q phase s ∧ s.damaged x
end ZombieDamage.OpenStrip

namespace ZombieDamage.OpenStrip
variable (m : Nat) (hm : 2≤m) (left right : Bool)
def inside (v : Fin (2*m+8)) : Bool :=
  decide (v.val<2*m ∨ (left=true ∧ v.val=2*m) ∨ (right=true ∧ v.val=2*m+1))
def allPorts : List Port := [(false,none),(false,some false),(false,some true),
  (true,none),(true,some false),(true,some true)]
instance (p : Port) : Decidable (Active left right p) := by unfold Active; infer_instance

def task (target : Option (Fin (2*m+8))) (allowed : Port → Bool) : Task (2*m+8) where
  adj u v := decide (Adj m left right u.val v.val)
  inside := inside m left right
  target := target
  allowedExit v := allPorts.any (fun p => decide (Active left right p) && allowed p && decide (v=portStub m p))

include hm in
theorem task_good (target : Option (Fin (2*m+8))) (allowed : Port → Bool) :
    (task m left right target allowed).GoodGraph := by
  constructor
  · intro u v
    change decide (Adj m left right u.val v.val)=decide (Adj m left right v.val u.val)
    have he : Adj m left right u.val v.val ↔ Adj m left right v.val u.val :=
      ⟨(graph m left right hm).symm,(graph m left right hm).symm⟩
    simp only [he]
  · intro u
    change decide (Adj m left right u.val u.val)=false
    exact decide_eq_false ((graph m left right hm).loopless u)
end ZombieDamage.OpenStrip

namespace ZombieDamage.TriangleRoute
open FullGame

def vertex (p : Fin 3) : Fin 6 := ⟨p.val,by omega⟩
def stub (p : Fin 3) : Fin 6 := ⟨p.val+3,by omega⟩
def Adj (u v : Fin 6) : Prop :=
  (u.val<3 ∧ v.val<3 ∧ u≠v) ∨
  (u.val<3 ∧ v.val=u.val+3) ∨ (v.val<3 ∧ u.val=v.val+3)
instance : DecidableRel Adj := by
  intro u v
  unfold Adj
  infer_instance

def graph : Graph (Fin 6) where
  adj := Adj
  symm := by decide
  loopless := by decide

instance : DecidableRel graph.adj := inferInstanceAs (DecidableRel Adj)
end ZombieDamage.TriangleRoute

namespace ZombieDamage.DiamondRoute
open FullGame

def port (p : Bool) : Fin 6 := if p then 3 else 0
def stub (p : Bool) : Fin 6 := if p then 5 else 4
def middle (b : Bool) : Fin 6 := if b then 2 else 1

def Adj (u v : Fin 6) : Prop :=
  (u.val<4 ∧ v.val<4 ∧ u≠v ∧ ¬(u.val=0 ∧ v.val=3) ∧ ¬(u.val=3 ∧ v.val=0)) ∨
  (u.val=0 ∧ v.val=4) ∨ (u.val=4 ∧ v.val=0) ∨
  (u.val=3 ∧ v.val=5) ∨ (u.val=5 ∧ v.val=3)
instance : DecidableRel Adj := by intro u v; unfold Adj; infer_instance

def graph : Graph (Fin 6) where
  adj := Adj
  symm := by decide
  loopless := by decide
instance : DecidableRel graph.adj := inferInstanceAs (DecidableRel Adj)
end ZombieDamage.DiamondRoute

namespace ZombieDamage.OpenStrip
open FullGame Cyclic
variable (m : Nat) (hm : 2≤m) (left right : Bool)
/-- All-length open-strip routing to any prescribed nonentry active port. -/
theorem metric_exit_contract (entry q : Port) (hin : Active left right entry)
    (hq : Active left right q) (hne : q≠entry) :
    (task m left right none (fun p => decide (p=q))).MetricForcesWithin
      (task_good m hm left right none (fun p => decide (p=q))) (2*m)
      ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  sorry
end ZombieDamage.OpenStrip

namespace ZombieDamage.OpenStrip
open FullGame Cyclic
variable (m : Nat) (hm : 2≤m) (left right : Bool)
/-- All-length open-strip routing through any internal target before a nonentry exit. -/
theorem metric_target_contract (entry : Port) (hin : Active left right entry)
    (x : Fin (2*m+8)) (hx : Internal m left right x) :
    (task m left right (some x) (fun p => decide (p≠entry))).MetricForcesWithin
      (task_good m hm left right (some x) (fun p => decide (p≠entry))) (2*m)
      ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  sorry
end ZombieDamage.OpenStrip

namespace ZombieDamage.TriangleRoute
open FullGame Cyclic

/-- Every ordered pair of distinct triangle ports, in two survivor moves. -/
theorem prescribed_exit (p q : Fin 3) (hne : p≠q) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=vertex p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      t.zombie=vertex q ∧ t.survivor=stub q ∧
      t.damaged (vertex p) ∧ t.damaged (vertex q)) 2 .survivor s := by
  sorry
end ZombieDamage.TriangleRoute

namespace ZombieDamage.TriangleRoute
open FullGame Cyclic

/-- Every triangle entry and target, in two survivor moves. -/
theorem target_route (p a : Fin 3) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=vertex p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      ∃ q, q≠p ∧ t.zombie=vertex q ∧ t.survivor=stub q ∧ t.damaged (vertex a))
      2 .survivor s := by
  sorry
end ZombieDamage.TriangleRoute

namespace ZombieDamage.DiamondRoute
open FullGame Cyclic

/-- Every diamond entry and internal target, in three survivor moves. -/
theorem target_route (p : Bool) (a : Fin 6) (ha : a.val<4) (s : State (Fin 6))
    (hz : s.zombie=stub p) (hs : s.survivor=port p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧
      t.zombie=port (!p) ∧ t.survivor=stub (!p) ∧ t.damaged a)
      3 .survivor s := by
  sorry
end ZombieDamage.DiamondRoute

namespace ZombieDamage.Task
open FullGame Cyclic
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)
/-- Full-game exit forcing implies local metric routing for leaf boundaries. -/
theorem fullGame_metricForcesWithin (hl : T.BoundaryLeaves) (b : Nat)
    (s : Position N) (D : Fin N → Prop)
    (hinside : T.inside s.survivor=true) (hadj : T.adj s.zombie s.survivor=true)
    (hflag : T.FlagComplete s D)
    (h : ForcesWithin (T.graph hg) T.FullExit b .survivor (fullState s D)) :
    T.MetricForcesWithin hg b s := by
  sorry
end ZombieDamage.Task

namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Bounded and eventual full damage agree on a finite graph. -/
theorem fullDamage_iff_eventual (vs : List V) (hevery : ∀ v, v ∈ vs) :
    FullDamage G ↔ EventualFullDamage G := by
  sorry
end ZombieDamage.FullGame

namespace ZombieDamage.Graph.MetricCertificate
open FullGame Cyclic
variable {V : Type} {G : Graph V} (M : G.MetricCertificate)
/-- Actual shortest-walk distance from a validated metric certificate. -/
theorem distance (u v : V) : G.Distance (M.value u v) u v := by
  sorry
end ZombieDamage.Graph.MetricCertificate

namespace ZombieDamage.Task
open FullGame Cyclic
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)
/-- Finite local routing interpreted in the full game. -/
theorem metricForcesWithin_fullGame {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (D : Fin N → Prop)
    (hs : T.FlagSound s D) :
    ForcesWithin (T.graph hg) T.FullExit b .survivor (fullState s D) := by
  sorry
end ZombieDamage.Task

namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Full-game target scheduling, conditional on explicit routing and initialization contracts. -/
theorem fullDamage_of_contract (I : State V → Prop) (cost startCost : Nat)
    (targets : List V) (hevery : ∀ v, v ∈ targets)
    (hc : TargetContract G I cost)
    (hinit : ∀ z, ∃ v, z ≠ v ∧ ForcesWithin G
      (fun p t => p = .survivor ∧ I t) startCost .zombie (initial z v)) :
    FullDamageWithin G (startCost + targets.length * cost) := by
  sorry
end ZombieDamage.FullGame

namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Universal starting vertices prevent full damage. -/
theorem universal_vertex_not_fullDamage (u : V)
    (hu : ∀ v, u ≠ v → G.adj u v) : ¬ FullDamage G := by
  sorry
end ZombieDamage.FullGame

namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- A survivor pass credits its departure source. -/
theorem pass_damages_source (s : State V) (hne : s.zombie ≠ s.survivor) :
    ForcesWithin G (fun _ t => t.damaged s.survivor) 1 .survivor s := by
  sorry
end ZombieDamage.FullGame

namespace ZombieDamage.CycleGame
open FullGame Cyclic
variable {n : Nat}
/-- Every cycle of order at least five, within n survivor moves. -/
theorem full_damage (hn : 5 ≤ n) : FullDamageWithin (graph hn) n := by
  sorry
end ZombieDamage.CycleGame

namespace ZombieDamage.MobiusGame
open FullGame Cyclic
variable {m : Nat}
/-- Every Mobius ladder with m at least four, within 2m moves. -/
theorem full_damage (hm : 4 ≤ m) : FullDamageWithin (graph hm) (2*m) := by
  sorry
end ZombieDamage.MobiusGame

namespace ZombieDamage.PrismGame
open FullGame Cyclic
variable {m : Nat}
/-- Every prism with m at least five, within 2m moves. -/
theorem full_damage (hm : 5 ≤ m) : FullDamageWithin (graph hm) (2*m) := by
  sorry
end ZombieDamage.PrismGame

namespace ZombieDamage.Exceptions
open FullGame Cyclic

/-- The four explicitly defined exceptions cannot force full damage at any horizon. -/
theorem not_full_damage (g : Kind) : ¬ FullGame.FullDamage (graph g) := by
  sorry
end ZombieDamage.Exceptions

namespace ZombieDamage.GraphIso
open FullGame Cyclic
variable {V W : Type} {G : Graph V} {H : Graph W} (F : GraphIso G H)
include F
/-- Full-game invariance under graph isomorphism. -/
theorem fullDamage_iff : FullGame.FullDamage G ↔ FullGame.FullDamage H := by
  sorry
end ZombieDamage.GraphIso

namespace ZombieDamage.ShortComponentModel
open FullGame Cyclic
variable {N : Nat} {V : Type} {T : Task N} {G : Graph V}
variable (M : ShortComponentModel T G) (hg : T.GoodGraph)
/-- Complete strategy transfer for a faithful short-component model, including identified stubs. -/
theorem metricForcesWithin_ambient {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (D : V → Prop) (hD : M.FlagSound s D) :
    FullGame.ForcesWithin G M.Exit b .survivor (M.state s D) := by
  sorry
end ZombieDamage.ShortComponentModel
