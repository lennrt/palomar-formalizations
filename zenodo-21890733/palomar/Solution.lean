/-
Paper: A Counterexample to Prescribed-Cycle Recovery in Barnette Graphs
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21890733
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib

/-!
# Concrete prescribed-cycle obstruction in a Barnette graph

The declarations below expose the finite mathematical core of the paper's
16-vertex counterexample. They certify the concrete cubic bipartite graph and
its deletion connectivity, the displayed Hamiltonian cycle and complementary
perfect matching, the facial-incidence data, the simultaneous coloring and
its uniqueness up to global permutation, and the final obstruction for every
output satisfying the paper's external Property 1.

The topological theorem turning the oriented incidence certificate into a
cellular sphere embedding and Property 1 of the published algorithm remain
external inputs.
-/

open Finset SimpleGraph

namespace BarnettePalomar

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

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

/-- The sixteen oriented steps in the displayed cyclic order, including the
closing step from vertex `8` to vertex `0`. -/
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

/-- The ten oriented facial boundaries printed in the paper. -/
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

def graphAfterDeleting (deleted : Finset Vertex) :=
  G.induce {v | v ∉ deleted}

/-- All vertex-deletion sets of cardinality at most two. -/
def smallDeletions : Finset (Finset Vertex) :=
  univ.powersetCard 0 ∪ univ.powersetCard 1 ∪ univ.powersetCard 2

/-- Explicit 16-vertex adjacency masks.  Keeping the BFS computation on these
masks avoids reducing Mathlib's walk enumerator for all deletion cases. -/
def neighborMask : Vertex → Finset Vertex := ![
  {4, 8, 15}, {7, 11, 14}, {3, 6, 10}, {2, 5, 9},
  {0, 5, 12}, {3, 4, 6}, {2, 5, 7}, {1, 6, 13},
  {0, 9, 11}, {3, 8, 10}, {2, 9, 11}, {1, 8, 10},
  {4, 13, 15}, {7, 12, 14}, {1, 13, 15}, {0, 12, 14}
]

def bfsStep (deleted reached : Finset Vertex) : Finset Vertex :=
  (reached ∪ reached.biUnion neighborMask) \ deleted

def bfsReach (deleted : Finset Vertex) (root : Vertex) : Nat → Finset Vertex
  | 0 => {root} \ deleted
  | n + 1 => bfsStep deleted (bfsReach deleted root n)

/-- A deletion set of size at most two cannot contain all of `0,1,2`, so this
is a surviving root in every certified case. -/
def deletionRoot (deleted : Finset Vertex) : Vertex :=
  if 0 ∉ deleted then 0 else if 1 ∉ deleted then 1 else 2

/-- The 137 deletion masks: empty, singleton, and strictly ordered pairs. -/
def deletionMasks : List (Finset Vertex) :=
  let vertices : List Vertex := List.ofFn id
  [∅] ++ vertices.map ({·}) ++
    vertices.flatMap fun u =>
      (vertices.filter fun v => decide (u < v)).map fun v => {u, v}

/-- Boolean BFS certificate.  `List.all` deliberately traverses only the
137 listed deletion masks rather than the full `Finset Vertex` type. -/
def deletionBfsCheck : Bool :=
  deletionMasks.all fun deleted =>
    decide (deletionRoot deleted ∉ deleted) &&
    decide (bfsReach deleted (deletionRoot deleted) 16 = univ \ deleted)

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

def AdmissibleGreenClass (green : Finset Edge) : Prop :=
  green = color0 ∨ green = color1 ∨ green = color2

private lemma neighborMask_spec :
    ∀ u v, v ∈ neighborMask u ↔ G.Adj u v := by
  decide

private lemma bfsReach_sound (deleted : Finset Vertex) (root : Vertex)
    (hroot : root ∉ deleted) :
    ∀ n v, v ∈ bfsReach deleted root n →
      ∃ hv : v ∉ deleted,
        (graphAfterDeleting deleted).Reachable
          ⟨root, hroot⟩ ⟨v, hv⟩ := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp only [bfsReach, mem_sdiff, mem_singleton] at hv
      rcases hv with ⟨rfl, _⟩
      exact ⟨hroot, .rfl⟩
  | succ n ih =>
      intro v hv
      simp only [bfsReach, bfsStep, mem_sdiff, mem_union, mem_biUnion] at hv
      rcases hv with ⟨hv | ⟨u, hu, huv⟩, hvdel⟩
      · obtain ⟨hv', hreach⟩ := ih v hv
        exact ⟨hvdel, by simpa using hreach⟩
      · obtain ⟨hudel, hreach⟩ := ih u hu
        have hadjG : G.Adj u v := (neighborMask_spec u v).mp huv
        have hadj :
            (graphAfterDeleting deleted).Adj
              (⟨u, hudel⟩ : {x : Vertex // x ∉ deleted})
              (⟨v, hvdel⟩ : {x : Vertex // x ∉ deleted}) := hadjG
        exact ⟨hvdel, hreach.trans hadj.reachable⟩

private lemma connected_of_bfs_full (deleted : Finset Vertex) (root : Vertex)
    (hroot : root ∉ deleted)
    (hfull : bfsReach deleted root 16 = univ \ deleted) :
    (graphAfterDeleting deleted).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨root, hroot⟩, ?_⟩
  intro w
  have hw : w.1 ∈ bfsReach deleted root 16 := by
    rw [hfull]
    simp only [mem_sdiff, mem_univ, true_and]
    exact w.2
  obtain ⟨hwdel, hreach⟩ := bfsReach_sound deleted root hroot 16 w.1 hw
  simpa using hreach

private lemma deletionBfsCheck_spec (hcheck : deletionBfsCheck = true)
    {deleted : Finset Vertex} (hdeleted : deleted ∈ deletionMasks) :
    deletionRoot deleted ∉ deleted ∧
      bfsReach deleted (deletionRoot deleted) 16 = univ \ deleted := by
  rw [deletionBfsCheck, List.all_eq_true] at hcheck
  have hitem := hcheck deleted (by simpa using hdeleted)
  rw [Bool.and_eq_true_iff] at hitem
  exact ⟨of_decide_eq_true hitem.1, of_decide_eq_true hitem.2⟩

private lemma fin3_eq_remaining {a b c x : Color}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hxa : x ≠ a) (hxb : x ≠ b) : x = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases x <;> simp_all

private lemma properFaceColoring_iff_globalPermutation
    (hbase : ProperFaceColoring baseColor) (c : Face → Color) :
    ProperFaceColoring c ↔ IsGlobalPermutation c := by
  constructor
  · intro hc
    have h01 : c 0 ≠ c 1 := hc 0 1 (by decide)
    have h02 : c 0 ≠ c 2 := hc 0 2 (by decide)
    have h12 : c 1 ≠ c 2 := hc 1 2 (by decide)
    have h8 : c 8 = c 2 := fin3_eq_remaining h01 h02 h12
      (hc 8 0 (by decide)) (hc 8 1 (by decide))
    have h6 : c 6 = c 1 := fin3_eq_remaining h02 h01 h12.symm
      (hc 6 0 (by decide)) (by simpa [h8] using hc 6 8 (by decide))
    have h5 : c 5 = c 2 := fin3_eq_remaining h01 h02 h12
      (hc 5 0 (by decide)) (by simpa [h6] using hc 5 6 (by decide))
    have h4 : c 4 = c 0 := fin3_eq_remaining h12.symm h02.symm h01.symm
      (by simpa [h5] using hc 4 5 (by decide))
      (by simpa [h6] using hc 4 6 (by decide))
    have h3 : c 3 = c 2 := fin3_eq_remaining h01.symm h12 h02
      (hc 3 1 (by decide)) (by simpa [h4] using hc 3 4 (by decide))
    have h7 : c 7 = c 1 := fin3_eq_remaining h02 h01 h12.symm
      (hc 7 0 (by decide)) (hc 7 2 (by decide))
    have h9 : c 9 = c 0 := fin3_eq_remaining h12.symm h02.symm h01.symm
      (hc 9 2 (by decide)) (by simpa [h7] using hc 9 7 (by decide))
    let p : Color → Color := ![c 0, c 1, c 2]
    have hpInjective : Function.Injective p := by
      intro x y
      fin_cases x <;> fin_cases y <;> simp_all [p] <;> aesop
    let e : Equiv.Perm Color := Equiv.ofBijective p
      ⟨hpInjective, Finite.surjective_of_injective hpInjective⟩
    refine ⟨e, ?_⟩
    intro f
    fin_cases f <;> simp [e, p, baseColor, h3, h4, h5, h6, h7, h8, h9]
  · rintro ⟨p, hp⟩
    intro u v huv heq
    apply hbase u v huv
    apply p.injective
    simpa only [← hp u, ← hp v] using heq

/-- The displayed graph is cubic and bipartite. -/
theorem concrete_graph_certificate :
    #G.edgeFinset = 24 ∧
    (∀ v, G.degree v = 3) ∧
    (∀ u v, G.Adj u v → (u ∈ leftSide ↔ v ∉ leftSide)) := by
  decide

/-- The explicit 137-case certificate verifies connectivity after every
vertex-deletion set of cardinality zero, one, or two. -/
theorem deletion_connectivity_certificate :
    #smallDeletions = 137 ∧
    deletionMasks.length = 137 ∧
    deletionMasks.toFinset = smallDeletions ∧
    (∀ u v, v ∈ neighborMask u ↔ G.Adj u v) ∧
    deletionBfsCheck = true ∧
    ∀ deleted, #deleted ≤ 2 → (graphAfterDeleting deleted).Connected := by
  have hcount : #smallDeletions = 137 := by decide
  have hlength : deletionMasks.length = 137 := by decide
  have hmasks : deletionMasks.toFinset = smallDeletions := by decide
  have hmask : ∀ u v, v ∈ neighborMask u ↔ G.Adj u v := by decide
  have hcheck : deletionBfsCheck = true := by decide
  refine ⟨hcount, hlength, hmasks, hmask, hcheck, ?_⟩
  intro deleted hcard
  have hdeleted : deleted ∈ smallDeletions := by
    simp only [smallDeletions, mem_union, mem_powersetCard_univ]
    omega
  have hdeletedList : deleted ∈ deletionMasks := by
    simpa only [List.mem_toFinset] using (show deleted ∈ deletionMasks.toFinset by
      rw [hmasks]
      exact hdeleted)
  obtain ⟨hroot, hfull⟩ := deletionBfsCheck_spec hcheck hdeletedList
  exact connected_of_bfs_full deleted (deletionRoot deleted) hroot hfull

/-- The displayed order is Hamiltonian and its omitted edges are exactly a
perfect matching. -/
theorem hamiltonian_cycle_and_matching_certificate :
    cycleVertices.length = 16 ∧ cycleVertices.Nodup ∧
    (∀ v : Vertex, v ∈ cycleVertices) ∧
    cycleSteps.map Prod.fst = cycleVertices ∧
    cycleSteps.getLast? = some (8, 0) ∧
    (∀ d ∈ cycleSteps, G.Adj d.1 d.2) ∧
    cycleSteps.toFinset.image dartEdge = cycleEdges ∧
    cycleEdges ∪ omittedMatching = graphEdges ∧
    Disjoint cycleEdges omittedMatching ∧
    G.edgeFinset \ cycleEdges = omittedMatching ∧
    (∀ v, matchingGraph.degree v = 1) := by
  decide

/-- Auditable oriented-incidence and Euler certificate for the displayed
cellular sphere embedding. -/
theorem plane_embedding_certificate :
    (∀ f d, d ∈ faceDarts f → G.Adj d.1 d.2) ∧
    univ.biUnion faceBoundary = graphEdges ∧
    (∀ e ∈ graphEdges,
      #(univ.filter fun f : Face => e ∈ faceBoundary f) = 2) ∧
    (∀ u v, G.Adj u v →
      #(univ.filter fun f : Face => (u, v) ∈ faceDarts f) = 1 ∧
      #(univ.filter fun f : Face => (v, u) ∈ faceDarts f) = 1) ∧
    (∀ f g, dual.Adj f g ↔
      f ≠ g ∧ (faceBoundary f ∩ faceBoundary g).Nonempty) ∧
    Fintype.card Vertex + Fintype.card Face = #graphEdges + 2 := by
  decide

/-- The displayed simultaneous coloring is proper, is unique up to a global
permutation, induces the three edge classes, and every possible green class
meets the complementary matching. -/
theorem face_coloring_certificate :
    ProperFaceColoring baseColor ∧
    (∀ c : Color, (dualWithoutFaceColor c).Connected) ∧
    (∀ c : Face → Color, ProperFaceColoring c ↔ IsGlobalPermutation c) ∧
    boundaryColor0 ∪ boundaryColor1 ∪ boundaryColor2 = graphEdges ∧
    color0 = boundaryColor1 ∩ boundaryColor2 ∧
    color1 = boundaryColor0 ∩ boundaryColor2 ∧
    color2 = boundaryColor0 ∩ boundaryColor1 ∧
    (∀ green, AdmissibleGreenClass green →
      (omittedMatching ∩ green).Nonempty) := by
  have hbase : ProperFaceColoring baseColor := by decide
  have hgreenMeet : ∀ green, AdmissibleGreenClass green →
      (omittedMatching ∩ green).Nonempty := by
    intro green hgreen
    rcases hgreen with hgreen | hgreen | hgreen
    · rw [hgreen]
      decide
    · rw [hgreen]
      decide
    · rw [hgreen]
      decide
  exact ⟨hbase, by decide, properFaceColoring_iff_globalPermutation hbase,
    by decide, by decide, by decide, by decide, hgreenMeet⟩

/-- Instantiated final step: any output containing every edge of an admissible
green class differs from the displayed prescribed Hamiltonian cycle. -/
theorem property_one_excludes_prescribed_cycle
    {green output : Finset Edge}
    (hgreen : AdmissibleGreenClass green)
    (hforced : green ⊆ output) :
    output ≠ cycleEdges := by
  have hmeet : (omittedMatching ∩ green).Nonempty := by
    rcases hgreen with hgreen | hgreen | hgreen
    · rw [hgreen]
      decide
    · rw [hgreen]
      decide
    · rw [hgreen]
      decide
  have hdisjoint : Disjoint omittedMatching cycleEdges := by decide
  intro hout
  subst output
  exact hmeet.ne_empty <|
    Finset.disjoint_iff_inter_eq_empty.mp (hdisjoint.mono_right hforced)

end BarnettePalomar
