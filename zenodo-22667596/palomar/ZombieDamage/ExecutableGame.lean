import ZombieDamage.FiniteMetric

/-!
Executable regression oracle for the SAME move and payoff rules. Its metric
interface is separately connected to shortest walks in FiniteMetric. This
module's native evaluations are regression checks, not kernel proofs of the
computed optimal values. The Python/C++ independent oracle is not imported.
-/
namespace ZombieDamage.ExecutableGame

structure Input where
  name : String
  order : Nat
  adjacent : Array Bool
  distances : Array Nat
  expectedZombie : Nat
  expectedCop : Nat
  deriving Repr

namespace Input

def edge (g : Input) (u v : Nat) : Bool :=
  g.adjacent[u * g.order + v]!
def dist (g : Input) (u v : Nat) : Nat :=
  g.distances[u * g.order + v]!

/-- Exact geodesic decrement; the cop comparison additionally allows passing
and arbitrary neighboring destinations, as in the original paper. -/
def reply (g : Input) (cop : Bool) (z s x : Nat) : Bool :=
  if cop then x == z || g.edge z x
  else g.edge z x && g.dist z s == g.dist x s + 1

def survivor (g : Input) (z s w : Nat) : Bool :=
  w != z && (w == s || g.edge s w)

/-- Checks the whole distance-table certificate using finite loops. -/
def valid (g : Input) : Bool := Id.run do
  let n := g.order
  if n == 0 || g.adjacent.size != n*n || g.distances.size != n*n then return false
  for u in [:n] do
    if g.edge u u || g.dist u u != 0 then return false
    for v in [:n] do
      if g.edge u v != g.edge v u then return false
      if g.dist u v == 0 && u != v then return false
      let mut desc := g.dist u v == 0
      for x in [:n] do
        if g.edge u x then
          if g.dist u v > g.dist x v + 1 then return false
          if g.dist u v == g.dist x v + 1 then desc := true
      if !desc then return false
  return true

def countBits (mask width : Nat) : Nat := Id.run do
  let mut c := 0
  for s in [:width] do
    if (mask >>> s) &&& 1 == 1 then c := c + 1
  return c

/-- Least winning attractor, with source damage, passes, universal pursuer
choices and existential survivor choices. Equal-mask cycles start losing and
are promoted only from existing wins: infinite stalling does not create a
spurious win. Descending masks already contain all larger-mask continuations.
A goal reached after the final survivor move is credited even if the pursuer
could capture on a later turn. -/
def canForce (g : Input) (cop : Bool) (threshold : Nat) : Bool := Id.run do
  let n := g.order
  let nn := n*n
  let masks := 2^n
  let mut wins := Array.replicate (masks * nn) false
  for k in [:masks] do
    let mask := masks - 1 - k
    if countBits mask n >= threshold then
      for p in [:nn] do wins := wins.set! (mask * nn + p) true
    else
      let afterMask := mask -- each survivor position is credited separately below
      let mut changed := true
      let mut fuel := nn + 1
      while changed && fuel > 0 do
        fuel := fuel - 1
        changed := false
        for z in [:n] do
          for s in [:n] do
            let ix := mask * nn + z*n + s
            if wins[ix]! || z == s then continue
            let mut all := true
            let mut nonempty := false
            for x in [:n] do
              if g.reply cop z s x then
                nonempty := true
                if x == s then
                  all := false
                  break
                let nextmask := afterMask ||| (1 <<< s)
                let mut some := false
                for w in [:n] do
                  if g.survivor x s w && wins[nextmask * nn + x*n + w]! then
                    some := true
                    break
                if !some then
                  all := false
                  break
            if nonempty && all then
              wins := wins.set! ix true
              changed := true
  -- Observed zombie start, then survivor start, then first zombie turn.
  for z in [:n] do
    let mut some := false
    for s in [:n] do
      if z != s && wins[z*n+s]! then some := true
    if !some then return false
  return true

def value (g : Input) (cop : Bool) : Nat := Id.run do
  let mut last := 0
  for k in [1:g.order+1] do
    if g.canForce cop k then last := k else return last
  return last

/-- Runtime checks explicitly labelled as such; no native evaluator axiom is
introduced into a proof. -/
def check (g : Input) : IO Unit := do
  if !g.valid then throw (IO.userError ("Invalid graph/metric: " ++ g.name))
  let z := g.value false
  let c := g.value true
  if z != g.expectedZombie || c != g.expectedCop then
    throw (IO.userError s!"Mismatch {g.name}: Lean z={z}, cop={c}; expected z={g.expectedZombie}, cop={g.expectedCop}")
  IO.println s!"{g.name}\t{g.order}\t{z}\t{c}\tPASS"

end Input
end ZombieDamage.ExecutableGame
