import Std
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

noncomputable def PalomarVerified.degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Nat := G.degree v
-- Preserve the original Std instance used to elaborate finite-vertex literals.
attribute [-instance] List.instNeZeroNatLengthCons

/-!
# Short-cycle decompositions and full zombie damage
Lennart Rudolph. Associated paper: DOI 10.5281/zenodo.22667596.
The 42 independently stated results include the all-order four-exception theorem,
Davila Conjecture 24 as a numerical equality, its 2n(n+1) move bound, recurrent
coverage, universal short-cycle structure and the complete supplied game interface.
Definitions below retain actual graph metrics, adversarial reply quantifiers,
source-vertex damage and the original starting/turn order. No local proof is imported.
Only selected statements have intentional holes; Solution proves them independently.
Small proofs in definitions establish graph validity and finite-label arithmetic.
Known closed classifications and sensor bounds are supporting results, not priority claims.
The degree-independent arbitrary-game interface and Remark 19's ring-structure
connection remain written-only; the entire cubic-game application is formalized.
See README.md, GAME.md and SOURCE_THEORY.md for scope, attribution and AI disclosure.
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
def Distance (k : Nat) (u v : V) : Prop := G.Walk k u v ∧ ∀ j, G.Walk j u v → k ≤ j
def TwoApart (u w : V) : Prop := u ≠ w ∧ ¬ G.adj u w ∧ ∃ v, G.adj u v ∧ G.adj v w
def GeodesicReply (u w x : V) : Prop := G.adj u x ∧ ∃ d, G.Distance (Nat.succ d) u w ∧ G.Distance d x w
/-- Absence of actual triangles and quadrilaterals through the edge ab. The two displayed inequalities, together with
looplessness of the four edges, ensure four distinct vertices in the quadrilateral clause. -/
def Clean (a b : V) : Prop := G.adj a b ∧
  (∀ c, ¬ (G.adj b c ∧ G.adj c a)) ∧
  (∀ c d, a ≠ c → b ≠ d →
    ¬ (G.adj b c ∧ G.adj c d ∧ G.adj d a))
/-- An edge lying on a triangle or quadrilateral: on an actual edge this is exactly the negation of `Clean`. No
ambient graph or cycle oracle is assumed. -/
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
def GoodGraph (T : Task N) : Prop := (∀ u v, T.adj u v = T.adj v u) ∧ ∀ u, T.adj u u = false
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
def next (T : Task N) (s : Position N) (w z : Fin N) : Position N := ⟨T.afterSeen s, z, w⟩
def Safe (T : Task N) (s : Position N) (w : Fin N) : Prop := T.inside s.survivor = true ∧
  T.adj s.zombie s.survivor = true ∧
  T.adj s.survivor w = true ∧
  s.zombie ≠ w ∧ T.adj s.zombie w = false
def Exit (T : Task N) (s : Position N) (w : Fin N) : Prop :=
  T.inside w = false ∧ T.allowedExit w = true ∧ T.afterSeen s = true
instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Safe s w) := by unfold Safe; infer_instance
instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Exit s w) := by unfold Exit; infer_instance
/-- Finite-horizon forcing in the shortest-walk metric. `budget` counts survivor moves including the exit; an early
exit may leave some budget unused. The step constructor includes all geodesic replies and requires at least one, so a
position with no replies is not a vacuous winning position. -/
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
def adj (g : Gadget) (u v : g.Vertex) : Bool := decide ((u.val, v.val) ∈ g.edges ++ g.leaves ∨
          (v.val, u.val) ∈ g.edges ++ g.leaves)
/-- The survivor is inside the component exactly at an internal vertex. -/
def inside (g : Gadget) (v : g.Vertex) : Bool := decide (v.val < g.order)
/-- A port is an internal endpoint in the displayed leaf list. -/
def port (g : Gadget) (v : g.Vertex) : Bool := g.leaves.any (fun e => decide (e.1 = v.val))
/-- The leaf of a port. Values on nonports are immaterial: every public routing theorem explicitly assumes the
entering/exiting vertices are ports. -/
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
def entry (g : Gadget) (p : g.Vertex) : Position g.size := ⟨false, g.stub p, p⟩
/-- A metric survivor strategy for (A), with at most twice the internal order many survivor moves. Symmetry and
looplessness are included, not presumed. -/
def RouteExit (g : Gadget) (p q : g.Vertex) : Prop := ∃ hg : (g.exitTask q).GoodGraph,
    (g.exitTask q).MetricForcesWithin hg (2 * g.order) (g.entry p)
/-- A metric survivor strategy for (B), with the same explicit time bound. -/
def RouteTarget (g : Gadget) (p t : g.Vertex) : Prop := ∃ hg : (g.targetTask p t).GoodGraph,
    (g.targetTask p t).MetricForcesWithin hg (2 * g.order) (g.entry p)
end Gadget
end ZombieDamage
namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)
/-- At distance two, the geodesic replies are exactly the common neighbors. -/
theorem geodesicReply_iff_commonNeighbor {u w x : V} (h : G.TwoApart u w) : G.GeodesicReply u w x ↔ G.adj u x ∧ G.adj
    x w := by sorry
/-- Crossing a clean edge forces the zombie to the preceding survivor vertex. -/
theorem cleanEdge_forces_reply {u v w x : V} (hc : G.Clean v w) (huv : G.adj u v) (huw : u ≠ w) : G.GeodesicReply u w
    x ↔ x = v := by sorry
/-- Short-edge two-step walks are closed under chords and all alternative common-neighbor replies. -/
theorem short_twoStep_closed {u v w : V} (huv : G.ShortAdj u v) (hvw : G.ShortAdj v w) (hne : u ≠ w) : (G.adj u w →
    G.ShortAdj u w) ∧ (∀ x, G.adj u x → G.adj x w → G.ShortAdj u x ∧ G.ShortAdj x w) := by sorry
end ZombieDamage.Graph
namespace ZombieDamage.Verified
/-- All port and target choices, with no symmetry or certificate-validity hypothesis and with at most twice the
component order many survivor moves. -/
theorem finite_component_routing (g : Gadget) : (∀ p q : g.Vertex, g.port p = true → g.port q = true → p ≠ q →
    g.RouteExit p q) ∧ (∀ p t : g.Vertex, g.port p = true → g.inside t = true → g.RouteTarget p t) := by sorry
end ZombieDamage.Verified
namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)
/-- Multiplicity of radius r in the distance histogram of a finite population. Order is ignored and repeated vertices
are retained. -/
noncomputable def shellCount (r : Nat) (s : V) (population : List V) : Nat := by
  classical
  exact (population.filter (fun v => decide (G.Distance r s v))).length
/-- Sensor identities are retained; target labels and cross-sensor matching are not. Equality is required at every
nonnegative integral radius. -/
def SameShellData (S : V → Prop) (xs ys : List V) : Prop := ∀ s, S s → ∀ r, G.shellCount r s xs = G.shellCount r s ys
/-- Recovery of all populations of mass at most h, including multiplicities and the empty population. Equality of
populations is list permutation. -/
def Recovers (S : V → Prop) (h : Nat) : Prop := ∀ xs ys : List V, xs.length ≤ h → ys.length ≤ h →
    G.SameShellData S xs ys → xs.Perm ys
end ZombieDamage.Graph
namespace ZombieDamage.DiamondRing
/-- a,b are the adjacent central vertices; c,d are the two nonadjacent ports. -/
inductive Role where
  | a | b | c | d
  deriving DecidableEq, Repr
def Vertex (k : Nat) := Fin (k + 3) × Role
def next {k : Nat} (i : Fin (k + 3)) : Fin (k + 3) := ⟨(i.val + 1) % (k + 3), Nat.mod_lt _ (Nat.zero_lt_succ _)⟩
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
def adjacency {k : Nat} (u v : Vertex k) : Prop := (u.1 = v.1 ∧ internal u.2 v.2 = true) ∨
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
/-- An involution fixing every sensor but exchanging two distinct vertices prevents bounded-population recovery. -/
theorem involution_blocks_recovery (f : V → V) (hinv : ∀ v, f (f v) = v) (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    (S : V → Prop) (hfix : ∀ s, S s → f s = s) (a b : V) (hne : a ≠ b) (hab : f a = b) (h : Nat) (hh : 1 ≤ h) : ¬
    G.Recovers S h := by sorry
end ZombieDamage.Graph
namespace ZombieDamage.DiamondRing
/-- Each diamond requires one of its central pair as a sensor for bounded-population recovery. -/
def _root_.PalomarVerified.diamondVertex (k : Nat) (i : Fin (k + 3)) (r : Role) : Vertex k := (i, r)
theorem _root_.PalomarVerified.central_pair_sensor (k : Nat) (S : Vertex k → Prop) (h : Nat) (hh : 1 ≤ h) (hrec : (graph k).Recovers S h) (i
    : Fin (k + 3)) : S (PalomarVerified.diamondVertex k i .a) ∨ S (PalomarVerified.diamondVertex k i .b) := by sorry
end ZombieDamage.DiamondRing
namespace ZombieDamage.FullGame
inductive Phase where
  | zombie | survivor
  deriving DecidableEq, Repr
structure State (V : Type) where
  zombie : V
  survivor : V
  damaged : V → Prop
variable {V : Type} (G : Graph V)
def State.zombieTo (s : State V) (z : V) : State V := { s with zombie := z }
def State.survivorTo (s : State V) (w : V) : State V := ⟨s.zombie, w, fun v => s.damaged v ∨ v = s.survivor⟩
/-- Passes are allowed; next-turn safety is a strategy obligation. Moving onto the zombie is omitted: a pass credits
the same source before forced capture, so this normalization preserves damage-only objectives
(OccupiedVertexNormalization). -/
def LegalSurvivor (s : State V) (w : V) : Prop := w ≠ s.zombie ∧ (w = s.survivor ∨ G.adj s.survivor w)
def LegalZombie (s : State V) (z : V) : Prop := G.GeodesicReply s.zombie s.survivor z
/-- Nonterminal zombie turns have at least one legal reply, and every reply must avoid capture and meet the
continuation obligation. -/
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
/-- Zombie chooses first; survivor sees that choice and selects a start; then the zombie has the first turn. No
prescribed zombie path is assumed. -/
def FullDamageWithin (budget : Nat) : Prop := ∀ z, ∃ v, z ≠ v ∧
    ForcesWithin G (fun _ => AllDamaged) budget .zombie (initial z v)
def FullDamage : Prop := ∃ budget, FullDamageWithin G budget
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
variable {V : Type} (G : Graph V)
def EventualFullDamage : Prop := ∀ z, ∃ v, z≠v ∧
  ForcesEventually G (fun _ => AllDamaged) .zombie (initial z v)
end ZombieDamage.FullGame
namespace ZombieDamage.Task
variable {N : Nat} (T : Task N)
def BoundaryLeaves : Prop := ∀ v, T.inside v=false →
  ∀ u w, T.adj v u=true → T.adj v w=true → u=w
def FlagComplete (s : Position N) (D : Fin N → Prop) : Prop := ∀ v, T.target=some v → D v → s.seen=true
end ZombieDamage.Task
namespace ZombieDamage.Cyclic
variable {n : Nat}
def shift (hn : 0 < n) (i : Fin n) (a : Nat) : Fin n := ⟨(i.val + a) % n, Nat.mod_lt _ hn⟩
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
def adjacency (hm : 4 ≤ m) (u v : Fin (2*m)) : Prop := v = shift (pos hm) u 1 ∨ v = shift (pos hm) u (2*m-1) ∨
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
def TargetDamaged (D : Fin N → Prop) : Prop := ∀ v, T.target = some v → D v
def FlagSound (s : Position N) (D : Fin N → Prop) : Prop := s.seen = true → T.TargetDamaged D
def fullState (s : Position N) (D : Fin N → Prop) : State (Fin N) := ⟨s.zombie, s.survivor, D⟩
def FullExit (phase : Phase) (s : State (Fin N)) : Prop := phase = .survivor ∧ T.inside s.survivor = false ∧
    T.allowedExit s.survivor = true ∧ T.TargetDamaged s.damaged
end ZombieDamage.Task
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)
def TargetContract (I : State V → Prop) (cost : Nat) : Prop := ∀ s, I s → ∀ v, ForcesWithin G
    (fun p t => p = .survivor ∧ I t ∧ t.damaged v) cost .survivor s
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
def state (s : Position N) (D : V → Prop) : FullGame.State V := ⟨M.map s.zombie,M.map s.survivor,D⟩
def FlagSound (s : Position N) (D : V → Prop) : Prop := s.seen=true → ∀ v, T.target=some v → D (M.map v)
def Exit (phase : FullGame.Phase) (s : FullGame.State V) : Prop := phase = .survivor ∧ G.Clean s.zombie s.survivor ∧
    (∃ w, T.inside w=false ∧ T.allowedExit w=true ∧ s.survivor=M.map w) ∧
    ∀ v, T.target=some v → s.damaged (M.map v)
end ZombieDamage.ShortComponentModel
namespace ZombieDamage.OpenStrip
variable (m : Nat) (left right : Bool)
def Adj (u v : Nat) : Prop := (u<m ∧ v<m ∧ (u+1=v ∨ v+1=u)) ∨
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
open FullGame
/-- A boundary incidence is a side and either its cap or one of its rails. Inactive incidences are excluded by
`Active`; they are never local targets. -/
abbrev Port := Bool × Option Bool
def capOn (left right side : Bool) : Bool := if side then right else left
def Active (left right : Bool) (p : Port) : Prop := capOn left right p.1 = p.2.isNone
def portVertex (m : Nat) (hm : 2≤m) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => cap m p.1
  | some b => rail m b (if p.1 then m-1 else 0) (by split <;> omega)
def portStub (m : Nat) (p : Port) : Fin (2*m+8) :=
  match p.2 with
  | none => capStub m p.1
  | some b => stub m p.1 b
def Internal (m : Nat) (left right : Bool) (x : Fin (2*m+8)) : Prop := (∃ b i, ∃ hi : i<m, x=rail m b i hi) ∨
  (left=true ∧ x=cap m false) ∨ (right=true ∧ x=cap m true)
variable (m : Nat) (hm : 2≤m) (left right : Bool)
def inside (v : Fin (2*m+8)) : Bool := decide (v.val<2*m ∨ (left=true ∧ v.val=2*m) ∨ (right=true ∧ v.val=2*m+1))
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
def Adj (u v : Fin 6) : Prop := (u.val<3 ∧ v.val<3 ∧ u≠v) ∨
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
def Adj (u v : Fin 6) : Prop := (u.val<4 ∧ v.val<4 ∧ u≠v ∧ ¬(u.val=0 ∧ v.val=3) ∧ ¬(u.val=3 ∧ v.val=0)) ∨
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
def _root_.PalomarVerified.portEq (p q : Port) : Bool := decide (p = q)
def _root_.PalomarVerified.portNe (p q : Port) : Bool := decide (p ≠ q)
theorem _root_.PalomarVerified.metric_exit_contract (entry q : Port) (hin : Active left right entry) (hq : Active left right q) (hne :
    q≠entry) : (task m left right none (fun p => PalomarVerified.portEq p q)).MetricForcesWithin (task_good m hm left right none
    (fun p => PalomarVerified.portEq p q)) (2*m) ⟨false,portStub m entry,portVertex m hm entry⟩ := by sorry
open FullGame Cyclic
variable (m : Nat) (hm : 2≤m) (left right : Bool)
/-- All-length open-strip routing through any internal target before a nonentry exit. -/
theorem _root_.PalomarVerified.metric_target_contract (entry : Port) (hin : Active left right entry) (x : Fin (2*m+8)) (hx : Internal m left
    right x) : (task m left right (some x) (fun p => PalomarVerified.portNe p entry)).MetricForcesWithin (task_good m hm left right
    (some x) (fun p => PalomarVerified.portNe p entry)) (2*m) ⟨false,portStub m entry,portVertex m hm entry⟩ := by sorry
end ZombieDamage.OpenStrip
namespace ZombieDamage.TriangleRoute
open FullGame Cyclic
/-- Every ordered pair of distinct triangle ports, in two survivor moves. -/
theorem prescribed_exit (p q : Fin 3) (hne : p≠q) (s : State (Fin 6)) (hz : s.zombie=stub p) (hs : s.survivor=vertex
    p) : ForcesWithin graph (fun phase t => phase=.survivor ∧ t.zombie=vertex q ∧ t.survivor=stub q ∧ t.damaged
    (vertex p) ∧ t.damaged (vertex q)) 2 .survivor s := by sorry
open FullGame Cyclic
/-- Every triangle entry and target, in two survivor moves. -/
theorem target_route (p a : Fin 3) (s : State (Fin 6)) (hz : s.zombie=stub p) (hs : s.survivor=vertex p) :
    ForcesWithin graph (fun phase t => phase=.survivor ∧ ∃ q, q≠p ∧ t.zombie=vertex q ∧ t.survivor=stub q ∧ t.damaged
    (vertex a)) 2 .survivor s := by sorry
end ZombieDamage.TriangleRoute
namespace ZombieDamage.DiamondRoute
open FullGame Cyclic
/-- Every diamond entry and internal target, in three survivor moves. -/
theorem target_route (p : Bool) (a : Fin 6) (ha : a.val<4) (s : State (Fin 6)) (hz : s.zombie=stub p) (hs :
    s.survivor=port p) : ForcesWithin graph (fun phase t => phase=.survivor ∧ t.zombie=port (!p) ∧ t.survivor=stub
    (!p) ∧ t.damaged a) 3 .survivor s := by sorry
end ZombieDamage.DiamondRoute
namespace ZombieDamage.Task
open FullGame Cyclic
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)
/-- Full-game exit forcing implies local metric routing for leaf boundaries. -/
theorem fullGame_metricForcesWithin (hl : T.BoundaryLeaves) (b : Nat) (s : Position N) (D : Fin N → Prop) (hinside :
    T.inside s.survivor=true) (hadj : T.adj s.zombie s.survivor=true) (hflag : T.FlagComplete s D) (h : ForcesWithin
    (T.graph hg) T.FullExit b .survivor (fullState s D)) : T.MetricForcesWithin hg b s := by sorry
end ZombieDamage.Task
namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Bounded and eventual full damage agree on a finite graph. -/
theorem fullDamage_iff_eventual (vs : List V) (hevery : ∀ v, v ∈ vs) : FullDamage G ↔ EventualFullDamage G := by sorry
end ZombieDamage.FullGame
namespace ZombieDamage.Graph.MetricCertificate
open FullGame Cyclic
variable {V : Type} {G : Graph V} (M : G.MetricCertificate)
/-- Actual shortest-walk distance from a validated metric certificate. -/
theorem distance (u v : V) : G.Distance (M.value u v) u v := by sorry
end ZombieDamage.Graph.MetricCertificate
namespace ZombieDamage.Task
open FullGame Cyclic
variable {N : Nat} (T : Task N) (hg : T.GoodGraph)
/-- Finite local routing interpreted in the full game. -/
theorem metricForcesWithin_fullGame {b : Nat} {s : Position N} (h : T.MetricForcesWithin hg b s) (D : Fin N → Prop)
    (hs : T.FlagSound s D) : ForcesWithin (T.graph hg) T.FullExit b .survivor (fullState s D) := by sorry
end ZombieDamage.Task
namespace ZombieDamage.FullGame
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Full-game target scheduling, conditional on explicit routing and initialization contracts. -/
theorem fullDamage_of_contract (I : State V → Prop) (cost startCost : Nat) (targets : List V) (hevery : ∀ v, v ∈
    targets) (hc : TargetContract G I cost) (hinit : ∀ z, ∃ v, z ≠ v ∧ ForcesWithin G (fun p t => p = .survivor ∧ I t)
    startCost .zombie (initial z v)) : FullDamageWithin G (startCost + targets.length * cost) := by sorry
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- Universal starting vertices prevent full damage. -/
theorem universal_vertex_not_fullDamage (u : V) (hu : ∀ v, u ≠ v → G.adj u v) : ¬ FullDamage G := by sorry
open FullGame Cyclic
variable {V : Type} (G : Graph V)
/-- A survivor pass credits its departure source. -/
theorem pass_damages_source (s : State V) (hne : s.zombie ≠ s.survivor) : ForcesWithin G (fun _ t => t.damaged
    s.survivor) 1 .survivor s := by sorry
end ZombieDamage.FullGame
namespace ZombieDamage.CycleGame
open FullGame Cyclic
variable {n : Nat}
/-- Every cycle of order at least five, within n survivor moves. -/
theorem full_damage (hn : 5 ≤ n) : FullDamageWithin (graph hn) n := by sorry
end ZombieDamage.CycleGame
namespace ZombieDamage.MobiusGame
open FullGame Cyclic
variable {m : Nat}
/-- Every Mobius ladder with m at least four, within 2m moves. -/
theorem full_damage (hm : 4 ≤ m) : FullDamageWithin (graph hm) (2*m) := by sorry
end ZombieDamage.MobiusGame
namespace ZombieDamage.PrismGame
open FullGame Cyclic
variable {m : Nat}
/-- Every prism with m at least five, within 2m moves. -/
theorem full_damage (hm : 5 ≤ m) : FullDamageWithin (graph hm) (2*m) := by sorry
end ZombieDamage.PrismGame
namespace ZombieDamage.Exceptions
open FullGame Cyclic
/-- The four explicitly defined exceptions cannot force full damage at any horizon. -/
theorem not_full_damage (g : Kind) : ¬ FullGame.FullDamage (graph g) := by sorry
end ZombieDamage.Exceptions
namespace ZombieDamage.GraphIso
open FullGame Cyclic
variable {V W : Type} {G : Graph V} {H : Graph W} (F : GraphIso G H)
include F
/-- Full-game invariance under graph isomorphism. -/
theorem fullDamage_iff : FullGame.FullDamage G ↔ FullGame.FullDamage H := by sorry
end ZombieDamage.GraphIso
namespace ZombieDamage.ShortComponentModel
open FullGame Cyclic
variable {N : Nat} {V : Type} {T : Task N} {G : Graph V}
variable (M : ShortComponentModel T G) (hg : T.GoodGraph)
/-- Complete strategy transfer for a faithful short-component model, including identified stubs. -/
theorem metricForcesWithin_ambient {b : Nat} {s : Position N} (h : T.MetricForcesWithin hg b s) (D : V → Prop) (hD :
    M.FlagSound s D) : FullGame.ForcesWithin G M.Exit b .survivor (M.state s D) := by sorry
end ZombieDamage.ShortComponentModel
attribute [instance] List.instNeZeroNatLengthCons
namespace ZombieMain
open SimpleGraph ZombieDamage
def gameGraph {V : Type} (G : SimpleGraph V) : ZombieDamage.Graph V where
  adj := G.Adj
  symm := G.adj_symm
  loopless := fun _ => G.irrefl
/-- An actual cycle of length three or four, using Mathlib's simple-cycle predicate. -/
def IsShortCycle {V : Type*} {G : SimpleGraph V} (C : G.Subgraph) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length ≤ 4 ∧ C = p.toSubgraph
open ZombieDamage
/-- The four explicit graph-isomorphism exceptions, without a game premise. -/
def IsException {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ kind : Exceptions.Kind,Nonempty (GraphIso (Exceptions.graph kind) (gameGraph G))
open SimpleGraph
/-- A finite adjacency table or formula. Its graph vertices are precisely the natural-number labels below `order`;
values outside that range have no meaning. -/
structure Diagram where
  order : Nat
  adj : Nat → Nat → Bool
namespace Diagram
/-- An exact copy of a diagram in an ambient subgraph. The internal vertex map is bijective onto the subgraph, and
adjacency is reflected as well as preserved. -/
structure Embedding (D : Diagram) {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) where
  vertices : Fin D.order → V
  injective : Function.Injective vertices
  range_eq : Set.range vertices = H.verts
  adjacency : ∀ u v, D.adj u.val v.val = true ↔ H.Adj (vertices u) (vertices v)
end Diagram
/-- Rail labels are interleaved: `2*i` and `2*i+1` form rung `i`. The optional left and right caps have labels `2*m`
and `2*m+1`. -/
def stripAdj (m caps u v : Nat) : Prop := (u < 2*m ∧ v < 2*m ∧
    ((u/2 = v/2 ∧ u%2 ≠ v%2) ∨
     (u%2 = v%2 ∧ (u/2+1 = v/2 ∨ v/2+1 = u/2)))) ∨
  (1 ≤ caps ∧ ((u = 2*m ∧ (v=0 ∨ v=1)) ∨
               (v = 2*m ∧ (u=0 ∨ u=1)))) ∨
  (2 ≤ caps ∧ ((u = 2*m+1 ∧ (v=2*m-2 ∨ v=2*m-1)) ∨
               (v = 2*m+1 ∧ (u=2*m-2 ∨ u=2*m-1))))
instance (m caps u v : Nat) : Decidable (stripAdj m caps u v) := by
  unfold stripAdj
  infer_instance
def stripDiagram (m caps : Nat) : Diagram where
  order := 2*m+caps
  adj u v := decide (stripAdj m caps u v)
def closedDiagram (m : Nat) (twisted : Bool) : Diagram where
  order := 2*m
  adj u v := decide (stripAdj m 0 u v) ||
    (if twisted then
      (u == 0 && v == 2*m-1) || (v == 0 && u == 2*m-1) ||
      (u == 1 && v == 2*m-2) || (v == 1 && u == 2*m-2)
    else
      (u == 0 && v == 2*m-2) || (v == 0 && u == 2*m-2) ||
      (u == 1 && v == 2*m-1) || (v == 1 && u == 2*m-1))
def literalDiagram (n : Nat) (edges : List (Nat × Nat)) : Diagram where
  order := n
  adj u v := edges.any (fun e => (u == e.1 && v == e.2) || (u == e.2 && v == e.1))
inductive Family where
  | ladder (m : Nat)
  | singleCap (m : Nat)
  | doubleCap (m : Nat)
  | prism (m : Nat)
  | mobius (m : Nat)
  | k23 | k33e | p3e | q3v | q3e | k4 | k33
  deriving DecidableEq, Repr
def Family.diagram : Family → Diagram
  | .ladder m => stripDiagram m 0
  | .singleCap m => stripDiagram m 1
  | .doubleCap m => stripDiagram m 2
  | .prism m => closedDiagram m false
  | .mobius m => closedDiagram m true
  | .k23 => literalDiagram 5 [(0,2),(0,3),(0,4),(1,2),(1,3),(1,4)]
  | .k33e => literalDiagram 6 [(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
  | .p3e => literalDiagram 6 [(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(1,4),(2,5)]
  | .q3v => literalDiagram 7 [(0,1),(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(4,5),(4,6)]
  | .q3e => literalDiagram 8 [(0,2),(0,4),(1,3),(1,5),(2,3),(2,6),(3,7),(4,5),(4,6),(5,7),(6,7)]
  | .k4 => literalDiagram 4 [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
  | .k33 => literalDiagram 6 [(0,3),(0,4),(0,5),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5)]
def Family.Admissible : Family → Prop
  | .ladder m => 2 ≤ m
  | .singleCap m | .doubleCap m => 1 ≤ m
  | .prism m | .mobius m => 3 ≤ m
  | _ => True
instance (f : Family) : Decidable f.Admissible := by
  cases f <;> unfold Family.Admissible <;> infer_instance
variable {V : Type*} {G : SimpleGraph V}
def portVertices (H : G.Subgraph) : Set V := {v | v ∈ H.verts ∧ (H.neighborSet v).ncard = 2}
/-- Either the unclassified one-port case, or an exact labelled catalogue member. The embedding includes bijective
vertex coverage and exact adjacency. -/
def ClassifiedSubgraph (H : G.Subgraph) : Prop := (portVertices H).ncard = 1 ∨
    ∃ f : Family, f.Admissible ∧ Nonempty (f.diagram.Embedding H)
variable {V : Type}
/-- The inside-to-outside orientations of crossing edges count each undirected boundary edge exactly once. -/
def cutPairs (G : SimpleGraph V) (S : Set V) : Set (V×V) := {p | p.1∈S ∧ p.2∉S ∧ G.Adj p.1 p.2}
/-- A lower bound for the usual edge-expansion constant. -/
def HasEdgeExpansion [Fintype V] (G : SimpleGraph V) (η : ℝ) : Prop :=
  ∀ S : Set V, S.Nonempty → 2*S.ncard≤Fintype.card V →
    η*(S.ncard : ℝ) ≤ ((cutPairs G S).ncard : ℝ)
open ZombieDamage ZombieDamage.FullGame
variable {V : Type}
/-- A fixed survivor strategy with private memory, sampled just after each zombie turn. Every legal zombie reply is
admitted, preserves the actual positions, and avoids capture. The reply set is explicitly nonempty. -/
structure SurvivorController (G : Graph V) where
  Memory : Type
  zombie : Memory → V
  survivor : Memory → V
  move : Memory → V
  live : ∀ m, zombie m ≠ survivor m
  legal : ∀ m, LegalSurvivor G (initial (zombie m) (survivor m)) (move m)
  replies : ∀ m, ∃ y, G.GeodesicReply (zombie m) (move m) y
  safe : ∀ m y, G.GeodesicReply (zombie m) (move m) y → y ≠ move m
  next : ∀ m y, G.GeodesicReply (zombie m) (move m) y → Memory
  next_zombie : ∀ m y h, zombie (next m y h) = y
  next_survivor : ∀ m y h, survivor (next m y h) = move m
namespace SurvivorController
variable {G : Graph V}
/-- Infinite plays include every choice of legal geodesic replies. One index is one completed survivor move and its
ensuing safe zombie turn. -/
def Runs (C : SurvivorController G) (m : Nat → C.Memory) : Prop :=
  ∀ t, ∃ y, ∃ h : G.GeodesicReply (C.zombie (m t)) (C.move (m t)) y,
    C.next (m t) y h = m (t+1)
/-- Actual departure sources, rather than a cumulative damage flag, recur beyond every finite time on every play of
the fixed controller. -/
def Recurrent (C : SurvivorController G) : Prop := ∀ m, C.Runs m → ∀ x N, ∃ t, N ≤ t ∧ C.survivor (m t) = x
/-- The zombie chooses first. Finite initialization starts with the zombie's turn and ends at actual positions
represented by the infinite controller. -/
def InitializedWithin (C : SurvivorController G) (budget : Nat) : Prop := ∀ z, ∃ v, z ≠ v ∧ ForcesWithin G
    (fun phase s => phase = .survivor ∧
      ∃ m, C.zombie m = s.zombie ∧ C.survivor m = s.survivor)
    budget .zombie (initial z v)
end SurvivorController
/-- One fixed strategy, valid from every original zombie start, safely departs from every vertex infinitely often
against every legal zombie play. -/
def RecurrentCoverageWithin (G : Graph V) (initialBudget : Nat) : Prop :=
  ∃ C : SurvivorController G, C.Recurrent ∧ C.InitializedWithin initialBudget
end ZombieMain
namespace ZombieDamage.FullGame
variable {V : Type} [Fintype V]
/-- The number of distinct vertices already damaged. -/
noncomputable def damageCount (s : State V) : Nat := by
  classical
  exact (Finset.univ.filter s.damaged).card
/-- The survivor can guarantee at least k damaged vertices against every zombie start and every legal geodesic reply,
with one finite move bound. -/
def CanForceDamage (G : Graph V) (k : Nat) : Prop := k ≤ Fintype.card V ∧ ∃ b, ∀ z, ∃ v, z ≠ v ∧
    ForcesWithin G (fun _ s => k ≤ damageCount s) b .zombie (initial z v)
/-- Feasible scores are bounded by the graph order; zero is always an available payoff, including graphs with no
distinct pair of starting vertices. -/
noncomputable def forceableScores (G : Graph V) : Finset Nat := by
  classical
  exact (Finset.range (Fintype.card V + 1)).filter (fun k => k = 0 ∨ CanForceDamage G k)
/-- Davila's zombie damage number: the largest score the survivor can guarantee against the minimizing zombie, with
zero as the default payoff. -/
noncomputable def zombieDamageNumber (G : Graph V) : Nat := (forceableScores G).sup id
variable {V : Type} (G : Graph V)
/-- The full game with every neighboring survivor destination permitted. At coincident positions only an already
achieved objective can hold: both nonterminal constructors require distinct positions. -/
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
/-- Allowing moves onto the zombie preserves every damage-only objective, at every state, phase and budget. -/
theorem iff_normalized : PermissiveForces G objective b p s ↔ ForcesWithin G (fun _ t => objective t.damaged) b p s :=
    by sorry
end PermissiveForces
/-- The original starting order and full-damage value are invariant under occupied-vertex normalization. -/
theorem fullDamage_iff_permissive : FullDamage G ↔ ∃ b, ∀ z, ∃ v, z ≠ v ∧ PermissiveForces G (fun D => ∀ x, D x) b
    .zombie (initial z v) := by sorry
end ZombieDamage.FullGame
namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
/-- Every connected bridgeless cubic graph has full damage within 2n(n+1) moves exactly when it is not one of the four
literal exceptions (paper Theorem 2). -/
theorem _root_.PalomarVerified.full_damage_within_iff (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v →
    ¬G.IsBridge s(u,v)) : FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) ↔ ¬IsException G := by
    sorry
/-- The complete four-exception characterization of full zombie damage, without a finite-order cutoff (paper Theorem
2). -/
theorem _root_.PalomarVerified.full_damage_iff (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge
    s(u,v)) : FullDamage (gameGraph G) ↔ ¬IsException G := by sorry
/-- Davila Conjecture 24 with an explicit 2n(n+1) survivor-move bound, for every bridgeless cubic graph of order at
least ten (paper Corollary 3). -/
theorem _root_.PalomarVerified.davila_conjecture_24 (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge
    s(u,v)) (hn : 10≤Fintype.card V) : FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) := by
    sorry
/-- A clean edge yields full damage from every zombie start; classification, initialization and routing are proved,
not assumed. -/
theorem _root_.PalomarVerified.full_damage_of_clean_edge (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v →
    ¬G.IsBridge s(u,v)) (hclean : ∃p q,(gameGraph G).Clean p q) : FullDamageWithin (gameGraph G) (2*Fintype.card
    V*(Fintype.card V+1)) := by sorry
/-- One fixed strategy safely departs from every vertex infinitely often against every geodesic zombie play, after at
most 2n initialization moves (paper Theorem 4). -/
theorem _root_.PalomarVerified.recurrent_coverage_of_clean_edge {W : Type} {H : SimpleGraph W} [Fintype W] [DecidableRel H.Adj] (hconn :
    H.Connected) (hcubic : ∀v,PalomarVerified.degree H v=3) (hbridge : ∀u v,H.Adj u v → ¬H.IsBridge s(u,v)) (hclean : ∃p q,(gameGraph
    H).Clean p q) : RecurrentCoverageWithin (gameGraph H) (2*Fintype.card W) := by sorry
/-- Every Mobius ladder on 2m vertices with m at least four admits immediate recurrent coverage. -/
theorem mobius_recurrent_coverage {m : Nat} (hm : 4 ≤ m) : RecurrentCoverageWithin (MobiusGame.graph hm) 0 := by sorry
/-- At most four ambient edges leave a connected subcubic short-cycle subgraph with minimum internal degree two (paper
Theorem 1). -/
theorem _root_.PalomarVerified.four_boundary_edges (H : G.Subgraph) (hconn : H.coe.Connected) (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard)
    (hmax : ∀v,PalomarVerified.degree G v≤3) (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v) :
    (cutPairs G H.verts).ncard≤4 := by sorry
/-- Positive edge expansion bounds the smaller side of a short-cycle component by 4 divided by the expansion constant
(paper Corollary 8). -/
theorem _root_.PalomarVerified.short_component_expansion (H : G.Subgraph) (hconn : H.coe.Connected) (hmin : ∀v∈H.verts,2≤(H.neighborSet
    v).ncard) (hmax : ∀v,PalomarVerified.degree G v≤3) (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v)
    (η : ℝ) (hη : 0<η) (hex : HasEdgeExpansion G η) : ((min H.verts.ncard (Fintype.card V-H.verts.ncard) : Nat) :
    ℝ)≤4/η := by sorry
/-- Recovering all populations of positive bounded mass on a ring of k+3 diamonds needs at least k+3 labelled sensors;
a formalized known lower bound. -/
theorem diamond_ring_sensor_bound (k : Nat) (S : Finset (DiamondRing.Vertex k)) (h : Nat) (hh : 1 ≤ h) (hrec :
    (DiamondRing.graph k).Recovers (fun v => v∈S) h) : k+3 ≤ S.card := by sorry
section Structural
variable {W : Type*} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]
/-- A connected subcubic graph with minimum degree two and every edge on a triangle or quadrilateral has at most four
ports (paper Theorem 1). -/
theorem _root_.PalomarVerified.four_port_principle (hconn : H.Connected) (hmin : ∀v,2≤PalomarVerified.degree H v) (hmax : ∀v,PalomarVerified.degree H v≤3) (hshort : ∀u
    v,H.Adj u v → ∃C : H.Subgraph,IsShortCycle C ∧ C.Adj u v) : (∑v,(3-PalomarVerified.degree H v))≤4 ∧ (Finset.univ.filter (fun v =>
    PalomarVerified.degree H v=2)).card≤4 := by sorry
/-- All orders are classified by explicit exact graph embeddings, with the one-port alternative retained; it is
excluded later by bridgelessness. -/
theorem _root_.PalomarVerified.cycle_union_classification (hconn : H.Connected) (hmin : ∀v,2≤PalomarVerified.degree H v) (hmax : ∀v,PalomarVerified.degree H v≤3) (hshort :
    ∀u v,H.Adj u v → ∃C : H.Subgraph,IsShortCycle C ∧ C.Adj u v) : ClassifiedSubgraph (⊤ : H.Subgraph) := by sorry
end Structural
end ZombieMain
namespace ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : Graph V}
/-- The numerical zombie damage value never exceeds graph order. -/
theorem zombieDamageNumber_le_card : zombieDamageNumber G ≤ Fintype.card V := by sorry
/-- A positive damage threshold is forceable exactly when it is at most the numerical game value. -/
theorem canForceDamage_iff_le_number {k : Nat} (hk : 0 < k) : CanForceDamage G k ↔ k ≤ zombieDamageNumber G := by
    sorry
/-- A uniform bounded damage guarantee is equivalent to eventual forcing on a finite graph, with all original starting
choices. -/
theorem canForceDamage_iff_eventual (k : Nat) : CanForceDamage G k ↔ k ≤ Fintype.card V ∧ ∀ z, ∃ v, z ≠ v ∧
    ForcesEventually G (fun _ s => k ≤ damageCount s) .zombie (initial z v) := by sorry
/-- The numerical value equals the positive graph order exactly when full damage is forceable. -/
theorem zombieDamageNumber_eq_card_iff (hn : 0 < Fintype.card V) : zombieDamageNumber G = Fintype.card V ↔ FullDamage
    G := by sorry
end ZombieDamage.FullGame
namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
/-- The literal numerical conclusion of Davila Conjecture 24: zdmg(G) equals the order of every finite connected
bridgeless cubic graph with at least ten vertices. -/
theorem _root_.PalomarVerified.davila_conjecture_24_damage_number (hconn : G.Connected) (hcubic : ∀ v, PalomarVerified.degree G v = 3) (hbridge : ∀ u v,
    G.Adj u v → ¬G.IsBridge s(u,v)) (hn : 10 ≤ Fintype.card V) : zombieDamageNumber (gameGraph G) = Fintype.card V :=
    by sorry
end ZombieMain
