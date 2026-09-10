import ZombieDamage.Certificates

/-! Mathematical statement surface for the five finite short-cycle components.
The edge lists below are specified independently of the policy JSON.
Auxiliary leaves are only a LOCAL model. No all-orders theorem is claimed here.
-/
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
