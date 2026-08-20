/-
Paper: A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs
Author: Lennart Rudolph
DOI: https://doi.org/10.5281/zenodo.21890733
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib

/-!
# Lean certificate for prescribed-cycle recovery in a Barnette graph

The file checks the finite obstruction data, its facial-incidence interfaces,
the displayed Hamiltonian order, deletion connectivity, and the abstract
forced-edge argument. The cited algorithmic Property 1 and the topological
interpretation of the combinatorial sphere certificate remain explicit
external inputs.

There are no `sorry` declarations. Finite certificates use `native_decide`.
-/

open Finset SimpleGraph

namespace BarnettePrescribedCycle

abbrev Vertex := Fin 16
abbrev Face := Fin 10
abbrev Color := Fin 3
abbrev Edge := Sym2 Vertex
abbrev Dart := Vertex × Vertex

def graphEdges : Finset Edge :=
  {s(0, 4), s(0, 8), s(0, 15), s(1, 7), s(1, 11), s(1, 14),
   s(2, 3), s(2, 6), s(2, 10), s(3, 5), s(3, 9), s(4, 5),
   s(4, 12), s(5, 6), s(6, 7), s(7, 13), s(8, 9), s(8, 11),
   s(9, 10), s(10, 11), s(12, 13), s(12, 15), s(13, 14), s(14, 15)}

def G : SimpleGraph Vertex :=
  SimpleGraph.fromEdgeSet (graphEdges : Set Edge)

instance : DecidableRel G.Adj := by
  unfold G
  infer_instance

def cycleVertices : List Vertex :=
  [0, 4, 5, 3, 2, 6, 7, 13, 12, 15, 14, 1, 11, 10, 9, 8]

/-- The sixteen oriented steps in the displayed cyclic order.  The last entry
is the closing step back to vertex `0`. -/
def cycleSteps : List Dart :=
  [(0, 4), (4, 5), (5, 3), (3, 2), (2, 6), (6, 7), (7, 13), (13, 12),
   (12, 15), (15, 14), (14, 1), (1, 11), (11, 10), (10, 9), (9, 8), (8, 0)]

def dartEdge (d : Dart) : Edge := s(d.1, d.2)

def cycleEdges : Finset Edge :=
  {s(0, 4), s(4, 5), s(3, 5), s(2, 3), s(2, 6), s(6, 7),
   s(7, 13), s(12, 13), s(12, 15), s(14, 15), s(1, 14),
   s(1, 11), s(10, 11), s(9, 10), s(8, 9), s(0, 8)}

def omittedMatching : Finset Edge :=
  {s(0, 15), s(1, 7), s(2, 10), s(3, 9), s(4, 12), s(5, 6),
   s(8, 11), s(13, 14)}

def matchingGraph : SimpleGraph Vertex :=
  SimpleGraph.fromEdgeSet (omittedMatching : Set Edge)

instance : DecidableRel matchingGraph.Adj := by
  unfold matchingGraph
  infer_instance

def leftSide : Finset Vertex := {0, 2, 5, 7, 9, 11, 12, 14}

def color0 : Finset Edge :=
  {s(0, 15), s(1, 14), s(2, 3), s(4, 12), s(5, 6), s(7, 13),
   s(8, 11), s(9, 10)}

def color1 : Finset Edge :=
  {s(0, 4), s(1, 7), s(2, 6), s(3, 5), s(8, 9), s(10, 11),
   s(12, 15), s(13, 14)}

def color2 : Finset Edge :=
  {s(0, 8), s(1, 11), s(2, 10), s(3, 9), s(4, 5), s(6, 7),
   s(12, 13), s(14, 15)}

/-- The ten oriented facial boundaries printed in the manuscript. -/
def faceDarts : Face → Finset Dart := ![
  {(0, 8), (8, 9), (9, 3), (3, 5), (5, 4), (4, 0)},
  {(0, 15), (15, 14), (14, 1), (1, 11), (11, 8), (8, 0)},
  {(0, 4), (4, 12), (12, 15), (15, 0)},
  {(1, 14), (14, 13), (13, 7), (7, 1)},
  {(1, 7), (7, 6), (6, 2), (2, 10), (10, 11), (11, 1)},
  {(2, 6), (6, 5), (5, 3), (3, 2)},
  {(2, 3), (3, 9), (9, 10), (10, 2)},
  {(4, 5), (5, 6), (6, 7), (7, 13), (13, 12), (12, 4)},
  {(8, 11), (11, 10), (10, 9), (9, 8)},
  {(12, 13), (13, 14), (14, 15), (15, 12)}
]

def faceBoundary (f : Face) : Finset Edge :=
  (faceDarts f).image dartEdge

def dualEdges : Finset (Sym2 Face) :=
  {s(0, 1), s(0, 2), s(0, 5), s(0, 6), s(0, 7), s(0, 8),
   s(1, 2), s(1, 3), s(1, 4), s(1, 8), s(1, 9), s(2, 7),
   s(2, 9), s(3, 4), s(3, 7), s(3, 9), s(4, 5), s(4, 6),
   s(4, 7), s(4, 8), s(5, 6), s(5, 7), s(6, 8), s(7, 9)}

def dual : SimpleGraph Face :=
  SimpleGraph.fromEdgeSet (dualEdges : Set (Sym2 Face))

instance : DecidableRel dual.Adj := by
  unfold dual
  infer_instance

def baseColor : Face → Color := ![0, 1, 2, 2, 0, 2, 1, 1, 2, 0]

def boundaryColor0 : Finset Edge :=
  univ.biUnion fun f : Face => if baseColor f = 0 then faceBoundary f else ∅

def boundaryColor1 : Finset Edge :=
  univ.biUnion fun f : Face => if baseColor f = 1 then faceBoundary f else ∅

def boundaryColor2 : Finset Edge :=
  univ.biUnion fun f : Face => if baseColor f = 2 then faceBoundary f else ∅

def dualWithoutFaceColor (c : Color) : SimpleGraph {f : Face // baseColor f ≠ c} :=
  dual.induce {f | baseColor f ≠ c}

def smallDeletions : Finset (Finset Vertex) :=
  univ.powersetCard 0 ∪ univ.powersetCard 1 ∪ univ.powersetCard 2

def graphAfterDeleting (deleted : Finset Vertex) :=
  G.induce {v | v ∉ deleted}

instance (c : Color) : DecidableRel (dualWithoutFaceColor c).Adj := by
  unfold dualWithoutFaceColor
  infer_instance

instance (c : Color) : Decidable (dualWithoutFaceColor c).Connected := by
  infer_instance

instance (deleted : Finset Vertex) :
    DecidableRel (graphAfterDeleting deleted).Adj := by
  unfold graphAfterDeleting
  infer_instance

instance (deleted : Finset Vertex) :
    Decidable (graphAfterDeleting deleted).Connected := by
  infer_instance

def ProperFaceColoring (c : Face → Color) : Prop :=
  ∀ u v, dual.Adj u v → c u ≠ c v

instance (c : Face → Color) : Decidable (ProperFaceColoring c) := by
  unfold ProperFaceColoring
  infer_instance

def IsGlobalPermutation (c : Face → Color) : Prop :=
  ∃ p : Equiv.Perm Color, ∀ f, c f = p (baseColor f)

instance (c : Face → Color) : Decidable (IsGlobalPermutation c) := by
  unfold IsGlobalPermutation
  infer_instance

theorem graph_edge_count : #G.edgeFinset = 24 := by native_decide

theorem graph_cubic : ∀ v, G.degree v = 3 := by native_decide

theorem displayed_bipartition :
    ∀ u v, G.Adj u v → (u ∈ leftSide ↔ v ∉ leftSide) := by
  native_decide

theorem cycle_vertices_certificate :
    cycleVertices.length = 16 ∧ cycleVertices.Nodup ∧
      ∀ v : Vertex, v ∈ cycleVertices := by
  native_decide

theorem displayed_order_is_cycle_step_sources :
    cycleSteps.map Prod.fst = cycleVertices := by
  native_decide

theorem displayed_cycle_has_closing_step :
    cycleSteps.getLast? = some (8, 0) := by
  native_decide

theorem every_displayed_cycle_step_is_adjacent :
    ∀ d ∈ cycleSteps, G.Adj d.1 d.2 := by
  native_decide

theorem displayed_order_induces_cycle_edges :
    cycleSteps.toFinset.image dartEdge = cycleEdges := by
  native_decide

theorem cycle_edge_count : #cycleEdges = 16 := by native_decide

theorem cycle_edges_are_graph_edges : cycleEdges ⊆ G.edgeFinset := by
  native_decide

theorem exact_complementary_matching :
    G.edgeFinset \ cycleEdges = omittedMatching := by
  native_decide

theorem exact_cycle_matching_partition :
    cycleEdges ∪ omittedMatching = graphEdges ∧
      Disjoint cycleEdges omittedMatching := by
  native_decide

theorem matching_is_perfect : ∀ v, matchingGraph.degree v = 1 := by
  native_decide

theorem color_classes_partition :
    color0 ∪ color1 ∪ color2 = graphEdges ∧
      Disjoint color0 color1 ∧ Disjoint color0 color2 ∧ Disjoint color1 color2 := by
  native_decide

theorem every_facial_dart_is_a_graph_edge :
    ∀ f d, d ∈ faceDarts f → G.Adj d.1 d.2 := by
  native_decide

theorem face_boundaries_cover_graph :
    univ.biUnion faceBoundary = graphEdges := by
  native_decide

theorem every_edge_is_on_exactly_two_faces :
    ∀ e ∈ graphEdges,
      #(univ.filter fun f : Face => e ∈ faceBoundary f) = 2 := by
  native_decide

/-- Each orientation of every graph edge occurs on exactly one printed facial
boundary.  Together with `every_edge_is_on_exactly_two_faces`, this is the
opposite-orientation incidence certificate. -/
theorem every_edge_occurs_in_opposite_face_orientations :
    ∀ u v, G.Adj u v →
      #(univ.filter fun f : Face => (u, v) ∈ faceDarts f) = 1 ∧
      #(univ.filter fun f : Face => (v, u) ∈ faceDarts f) = 1 := by
  native_decide

theorem displayed_dual_is_induced_by_common_primal_edges :
    ∀ f g, dual.Adj f g ↔
      f ≠ g ∧ (faceBoundary f ∩ faceBoundary g).Nonempty := by
  native_decide

theorem combinatorial_euler_certificate :
    Fintype.card Vertex + Fintype.card Face = #graphEdges + 2 := by
  native_decide

theorem face_color_boundary_unions_cover_graph :
    boundaryColor0 ∪ boundaryColor1 ∪ boundaryColor2 = graphEdges := by
  native_decide

/-- This is the key face-incidence-to-edge-color bridge.  An edge receives the
third color exactly when its two incident face colors are the other two. -/
theorem induced_edge_colors_from_face_incidence :
    color0 = boundaryColor1 ∩ boundaryColor2 ∧
      color1 = boundaryColor0 ∩ boundaryColor2 ∧
      color2 = boundaryColor0 ∩ boundaryColor1 := by
  native_decide

theorem base_coloring_is_proper : ProperFaceColoring baseColor := by
  native_decide

theorem every_two_color_dual_is_connected :
    ∀ c : Color, (dualWithoutFaceColor c).Connected := by
  native_decide

theorem exactly_six_global_permutations :
    ∀ c : Face → Color, ProperFaceColoring c ↔ IsGlobalPermutation c := by
  native_decide

theorem matching_meets_every_color :
    (omittedMatching ∩ color0).Nonempty ∧
      (omittedMatching ∩ color1).Nonempty ∧
      (omittedMatching ∩ color2).Nonempty := by
  decide

theorem deletion_certificate_count : #smallDeletions = 137 := by
  native_decide

theorem small_deletions_are_exactly_cardinality_at_most_two :
    ∀ deleted : Finset Vertex, deleted ∈ smallDeletions ↔ #deleted ≤ 2 := by
  native_decide

theorem every_small_vertex_deletion_leaves_connected :
    ∀ deleted ∈ smallDeletions, (graphAfterDeleting deleted).Connected := by
  native_decide

theorem deletion_at_most_two_leaves_connected
    (deleted : Finset Vertex) (hdeleted : #deleted ≤ 2) :
    (graphAfterDeleting deleted).Connected :=
  every_small_vertex_deletion_leaves_connected deleted
    ((small_deletions_are_exactly_cardinality_at_most_two deleted).2 hdeleted)

def AdmissibleGreenClass (green : Finset Edge) : Prop :=
  green = color0 ∨ green = color1 ∨ green = color2

theorem every_admissible_green_meets_matching
    {green : Finset Edge} (hgreen : AdmissibleGreenClass green) :
    (omittedMatching ∩ green).Nonempty := by
  rcases hgreen with rfl | rfl | rfl
  · native_decide
  · native_decide
  · native_decide

/-- Abstract form of Property 1 plus an omitted green edge. -/
theorem output_ne_prescribed_cycle_of_forced_green
    {α : Type} {cycle matching green output : Set α}
    (hdisjoint : Disjoint matching cycle)
    (hforced : green ⊆ output)
    (homeets : (matching ∩ green).Nonempty) :
    output ≠ cycle := by
  rintro rfl
  obtain ⟨e, hematching, hegreen⟩ := homeets
  exact Set.disjoint_left.mp hdisjoint hematching (hforced hegreen)

#print axioms graph_edge_count
#print axioms graph_cubic
#print axioms displayed_bipartition
#print axioms cycle_vertices_certificate
#print axioms displayed_order_is_cycle_step_sources
#print axioms displayed_cycle_has_closing_step
#print axioms every_displayed_cycle_step_is_adjacent
#print axioms displayed_order_induces_cycle_edges
#print axioms cycle_edge_count
#print axioms cycle_edges_are_graph_edges
#print axioms exact_complementary_matching
#print axioms exact_cycle_matching_partition
#print axioms matching_is_perfect
#print axioms color_classes_partition
#print axioms every_facial_dart_is_a_graph_edge
#print axioms face_boundaries_cover_graph
#print axioms every_edge_is_on_exactly_two_faces
#print axioms every_edge_occurs_in_opposite_face_orientations
#print axioms displayed_dual_is_induced_by_common_primal_edges
#print axioms combinatorial_euler_certificate
#print axioms face_color_boundary_unions_cover_graph
#print axioms induced_edge_colors_from_face_incidence
#print axioms base_coloring_is_proper
#print axioms every_two_color_dual_is_connected
#print axioms exactly_six_global_permutations
#print axioms matching_meets_every_color
#print axioms deletion_certificate_count
#print axioms small_deletions_are_exactly_cardinality_at_most_two
#print axioms every_small_vertex_deletion_leaves_connected
#print axioms deletion_at_most_two_leaves_connected
#print axioms every_admissible_green_meets_matching
#print axioms output_ne_prescribed_cycle_of_forced_green

end BarnettePrescribedCycle
