/-
Paper: A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21890733
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Prescribed-cycle obstruction: advertised Lean statements

The first theorem checks the decisive finite fact for the explicit 16-vertex
example: the complementary matching meets every one of the three displayed
edge-color classes. The second theorem is the abstract final implication used
with the paper's external Property 1: if every green edge is forced into an
output cycle but the prescribed cycle omits a green matching edge, the two
cycles cannot be equal.
-/

open Finset SimpleGraph

namespace BarnettePalomar

abbrev Vertex := Fin 16
abbrev Edge := Sym2 Vertex

/-- The eight edges omitted by the displayed prescribed Hamiltonian cycle. -/
def omittedMatching : Finset Edge :=
  {s(0, 15), s(1, 7), s(2, 10), s(3, 9), s(4, 12), s(5, 6),
   s(8, 11), s(13, 14)}

/-- The first displayed edge-color class. -/
def color0 : Finset Edge :=
  {s(0, 15), s(1, 14), s(2, 3), s(4, 12), s(5, 6), s(7, 13),
   s(8, 11), s(9, 10)}

/-- The second displayed edge-color class. -/
def color1 : Finset Edge :=
  {s(0, 4), s(1, 7), s(2, 6), s(3, 5), s(8, 9), s(10, 11),
   s(12, 15), s(13, 14)}

/-- The third displayed edge-color class. -/
def color2 : Finset Edge :=
  {s(0, 8), s(1, 11), s(2, 10), s(3, 9), s(4, 5), s(6, 7),
   s(12, 13), s(14, 15)}

/-- The complementary matching meets all three possible green classes. -/
theorem concrete_matching_meets_every_color :
    (omittedMatching ∩ color0).Nonempty ∧
      (omittedMatching ∩ color1).Nonempty ∧
      (omittedMatching ∩ color2).Nonempty := by
  sorry

/-- A forced green edge omitted by the prescribed cycle separates the output. -/
theorem forced_green_excludes_prescribed_cycle
    {α : Type} {cycle matching green output : Set α}
    (hdisjoint : Disjoint matching cycle)
    (hforced : green ⊆ output)
    (homeets : (matching ∩ green).Nonempty) :
    output ≠ cycle := by
  sorry

end BarnettePalomar
