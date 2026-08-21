/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21925574
Palomar ambient-bridge upgrade: 2026-08-20.
-/
import K331Tutte.AmbientFourClique

set_option autoImplicit true

namespace K331Tutte.FiniteHomology.Ambient

theorem encoded_induced_four_pair_admissible
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    Admissible (encodePair (inducedPair P L)) := by
  exact encoded_induced_four_pair_admissible_source P L hBT

theorem induced_four_coordinate_chain_identification
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    let Q := inducedPair P L
    let c := encodePair Q
    actualRelativeFaces Q = relativeFaces c ∧
      (∀ z, ActualRelativeCycle Q z ↔ RelativeCycle c z) ∧
      actualD3Boundary Q = d3Boundary c ∧
      (∀ x y, ActualHomologous Q x y ↔ Homologous c x y) := by
  exact induced_four_coordinate_chain_identification_source P L hBT

theorem induced_four_clique_relative_homology_bound
    (P : FiniteSimplicialPair n) (L : LabelledFourClique P)
    (hBT : BoundaryTriangleCondition P) :
    ActualHomologyDimensionAtMostOne (inducedPair P L) := by
  exact induced_four_clique_relative_homology_bound_source P L hBT

end K331Tutte.FiniteHomology.Ambient
