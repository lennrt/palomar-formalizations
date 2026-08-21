/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925574
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Init

/-!
# Four-vertex relative-chain certificate

The induced complex on a four-clique has the full tetrahedral 1-skeleton,
an arbitrary subset of the four triangular faces, and possibly the tetrahedron.
The boundary subcomplex is encoded by its vertices and edges.  The predicate
`admissible` enforces the local simplicial-closure and boundary-triangle
conditions.  It is a conservative over-approximation: it does not impose all
global manifold constraints on an induced four-vertex pair.

For each of the 32,768 raw encodings, the definitions below enumerate all
relative 2-chains over F2.  The paper proves that, for these four-vertex
relative chain complexes, the cardinality test in `localH2Bound` is equivalent
to `dim H₂(K,K_boundary) <= 1`.  This file checks the finite Boolean predicate;
it does not formalize that homological equivalence.
-/

namespace K331Tutte.FiniteLocal

structure Config where
  triMask : Nat
  tetra : Bool
  boundaryVertices : Nat
  boundaryEdges : Nat
  deriving Repr, DecidableEq

def bit (mask i : Nat) : Bool := ((mask / (2 ^ i)) % 2) == 1

def maskSubset (width a b : Nat) : Bool :=
  (List.range width).all fun i => !(bit a i) || bit b i

def edgeVertexMask : Nat → Nat
  | 0 => 3   -- 01
  | 1 => 5   -- 02
  | 2 => 9   -- 03
  | 3 => 6   -- 12
  | 4 => 10  -- 13
  | 5 => 12  -- 23
  | _ => 0

def triangleVertexMask : Nat → Nat
  | 0 => 7   -- 012
  | 1 => 11  -- 013
  | 2 => 13  -- 023
  | 3 => 14  -- 123
  | _ => 0

def triangleEdgeMask : Nat → Nat
  | 0 => 11  -- 01, 02, 12
  | 1 => 21  -- 01, 03, 13
  | 2 => 38  -- 02, 03, 23
  | 3 => 56  -- 12, 13, 23
  | _ => 0

def boundaryTriangle (c : Config) (t : Nat) : Bool :=
  bit c.triMask t && maskSubset 4 (triangleVertexMask t) c.boundaryVertices

def admissible (c : Config) : Bool :=
  -- Defensive range guards: `allConfigs` already imposes these bounds, but
  -- keeping them here makes `admissible` safe on an arbitrary input.
  decide (c.triMask < 16) &&
  decide (c.boundaryVertices < 16) &&
  decide (c.boundaryEdges < 64) &&
  (!c.tetra || c.triMask == 15) &&
  (List.range 6).all (fun e =>
    !(bit c.boundaryEdges e) ||
      maskSubset 4 (edgeVertexMask e) c.boundaryVertices) &&
  (List.range 4).all (fun t =>
    !(boundaryTriangle c t) ||
      maskSubset 6 (triangleEdgeMask t) c.boundaryEdges)

def relativeTriangle (c : Config) (t : Nat) : Bool :=
  bit c.triMask t && !(boundaryTriangle c t)

def supportedChain (c : Config) (chain : Nat) : Bool :=
  (List.range 4).all fun t => !(bit chain t) || relativeTriangle c t

def edgeParity (c : Config) (chain edge : Nat) : Bool :=
  (List.range 4).foldl
    (fun parity t =>
      if bit chain t && relativeTriangle c t && bit (triangleEdgeMask t) edge
      then !parity else parity)
    false

def isCycle (c : Config) (chain : Nat) : Bool :=
  supportedChain c chain &&
  (List.range 6).all fun edge =>
    bit c.boundaryEdges edge || !(edgeParity c chain edge)

def cycleCount (c : Config) : Nat :=
  ((List.range 16).filter fun chain => isCycle c chain).length

def d3Nonzero (c : Config) : Bool :=
  c.tetra && (List.range 4).any fun t => relativeTriangle c t

def localH2Bound (c : Config) : Bool :=
  decide (cycleCount c ≤ if d3Nonzero c then 4 else 2)

def bools : List Bool := [false, true]

def allConfigs : List Config :=
  (List.range 16).flatMap fun tm =>
    bools.flatMap fun tet =>
      (List.range 16).flatMap fun bv =>
        (List.range 64).map fun be =>
          { triMask := tm, tetra := tet,
            boundaryVertices := bv, boundaryEdges := be }

theorem raw_configuration_count : allConfigs.length = 32768 := by
  native_decide

theorem admissible_encoding_count :
    (allConfigs.filter admissible).length = 695 := by
  native_decide

theorem every_admissible_encoding_satisfies_cycle_bound :
    allConfigs.all (fun c => !(admissible c) || localH2Bound c) = true := by
  native_decide

#print axioms raw_configuration_count
#print axioms admissible_encoding_count
#print axioms every_admissible_encoding_satisfies_cycle_bound

end K331Tutte.FiniteLocal
