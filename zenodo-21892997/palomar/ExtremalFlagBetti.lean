/-
Paper: An Infinite Dense Counterexample Family for Extremal First Betti Numbers of Flag Complexes
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21892997
Preprint published: 2026-08-11. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Certified graph core for the extremal flag-Betti counterexample

This file deliberately formalizes the finite graph certificates and the two
arithmetic bottlenecks in the paper.  It does **not** claim to formalize the
homotopy equivalence for leaf deletion or the homotopy type of independence
complexes of cycles; those standard topological inputs are not currently
packaged in mathlib in the form used by the paper.

There are no `sorry` declarations or axioms in this file.
-/

open Finset
open SimpleGraph

namespace ExtremalFlagBetti

/-- The complement family used by the all-order theorem. -/
def FamilyH (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v :=
    (u.val = 0 ∧ v.val = 1) ∨ (u.val = 1 ∧ v.val = 0) ∨
    (u.val = 0 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 0) ∨
    (u.val = 1 ∧ v.val = 2) ∨ (u.val = 2 ∧ v.val = 1) ∨
    (u.val = 0 ∧ v.val = 3) ∨ (u.val = 3 ∧ v.val = 0) ∨
    (u.val = 3 ∧ v.val = 4) ∨ (u.val = 4 ∧ v.val = 3) ∨
    (u.val = 4 ∧ 5 ≤ v.val) ∨ (v.val = 4 ∧ 5 ≤ u.val)
  symm := by
    intro u v h
    simpa only [and_comm, or_comm, or_left_comm, or_assoc] using h
  loopless := ⟨by
    intro u
    omega⟩

instance (n : ℕ) : DecidableRel (FamilyH n).Adj := by
  unfold FamilyH
  infer_instance

/-- Every member of the complement family is connected. -/
theorem family_connected {n : ℕ} (hn : 7 ≤ n) : (FamilyH n).Connected := by
  rw [connected_iff_exists_forall_reachable]
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  let v3 : Fin n := ⟨3, by omega⟩
  let v4 : Fin n := ⟨4, by omega⟩
  have h01 : (FamilyH n).Adj v0 v1 := by simp [FamilyH, v0, v1]
  have h02 : (FamilyH n).Adj v0 v2 := by simp [FamilyH, v0, v2]
  have h03 : (FamilyH n).Adj v0 v3 := by simp [FamilyH, v0, v3]
  have h34 : (FamilyH n).Adj v3 v4 := by simp [FamilyH, v3, v4]
  have r0 : (FamilyH n).Reachable v0 v0 := .rfl
  have r1 : (FamilyH n).Reachable v0 v1 := h01.reachable
  have r2 : (FamilyH n).Reachable v0 v2 := h02.reachable
  have r3 : (FamilyH n).Reachable v0 v3 := h03.reachable
  have r4 : (FamilyH n).Reachable v0 v4 := r3.trans h34.reachable
  refine ⟨v0, fun w ↦ ?_⟩
  by_cases hw0 : w.val = 0
  · have : w = v0 := Fin.ext (by simpa [v0] using hw0)
    subst w
    exact r0
  by_cases hw1 : w.val = 1
  · have : w = v1 := Fin.ext (by simpa [v1] using hw1)
    simpa [this] using r1
  by_cases hw2 : w.val = 2
  · have : w = v2 := Fin.ext (by simpa [v2] using hw2)
    simpa [this] using r2
  by_cases hw3 : w.val = 3
  · have : w = v3 := Fin.ext (by simpa [v3] using hw3)
    simpa [this] using r3
  by_cases hw4 : w.val = 4
  · have : w = v4 := Fin.ext (by simpa [v4] using hw4)
    simpa [this] using r4
  have hw5 : 5 ≤ w.val := by omega
  have h4w : (FamilyH n).Adj v4 w := by
    simp [FamilyH, v4, hw5]
  exact r4.trans h4w.reachable

/-- The all-order leaf and triangle-remainder certificate. -/
theorem family_leaf_triangle_certificate {n : ℕ} (hn : 7 ≤ n) :
    let leaf : Fin n := ⟨5, by omega⟩
    let hub : Fin n := ⟨4, by omega⟩
    (∀ v, (FamilyH n).Adj leaf v ↔ v = hub) ∧
      (∀ u, u ≠ hub ∧ ¬(FamilyH n).Adj hub u ↔ u.val < 3) ∧
      (∀ u v, u.val < 3 → v.val < 3 → u ≠ v → (FamilyH n).Adj u v) := by
  dsimp
  constructor
  · intro v
    constructor
    · intro h
      simp only [FamilyH] at h
      apply Fin.ext
      change v.val = 4
      omega
    · rintro rfl
      simp [FamilyH]
  constructor
  · intro u
    change
      (u ≠ (⟨4, by omega⟩ : Fin n) ∧
        ¬(FamilyH n).Adj (⟨4, by omega⟩ : Fin n) u) ↔ u.val < 3
    simp only [FamilyH]
    norm_num at *
    constructor
    · rintro ⟨hne, hadj⟩
      have hu4 : u.val ≠ 4 := by
        intro hu
        exact hne (Fin.ext (by simpa using hu))
      omega
    · intro hu
      constructor
      · intro heq
        have hval : u.val = 4 := by
          simpa using congrArg Fin.val heq
        omega
      · omega
  · intro u v hu hv huv
    simp only [FamilyH]
    have huvVal : u.val ≠ v.val := by
      intro h
      exact huv (Fin.ext h)
    omega

/-- Exact degrees in the all-order complement family.  This ties the symbolic
family definition directly to the edge-count calculation. -/
theorem family_degree_formula {n : ℕ} (hn : 7 ≤ n) (v : Fin n) :
    (FamilyH n).degree v =
      if v.val = 0 then 3
      else if v.val = 1 then 2
      else if v.val = 2 then 2
      else if v.val = 3 then 2
      else if v.val = 4 then n - 4
      else 1 := by
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let v2 : Fin n := ⟨2, by omega⟩
  let v3 : Fin n := ⟨3, by omega⟩
  let v4 : Fin n := ⟨4, by omega⟩
  by_cases h0 : v.val = 0
  · have hv : v = v0 := Fin.ext (by simpa [v0] using h0)
    subst v
    rw [degree, neighborFinset_eq_filter]
    have hneighbors :
        ({w | (FamilyH n).Adj v0 w} : Finset (Fin n)) = {v1, v2, v3} := by
      ext w
      simp [FamilyH, v0, v1, v2, v3, Fin.ext_iff]
    rw [hneighbors]
    simp [v0, v1, v2, v3]
  by_cases h1 : v.val = 1
  · have hv : v = v1 := Fin.ext (by simpa [v1] using h1)
    subst v
    rw [degree, neighborFinset_eq_filter]
    have hneighbors :
        ({w | (FamilyH n).Adj v1 w} : Finset (Fin n)) = {v0, v2} := by
      ext w
      simp [FamilyH, v0, v1, v2, Fin.ext_iff]
    rw [hneighbors]
    simp [v0, v1, v2]
  by_cases h2 : v.val = 2
  · have hv : v = v2 := Fin.ext (by simpa [v2] using h2)
    subst v
    rw [degree, neighborFinset_eq_filter]
    have hneighbors :
        ({w | (FamilyH n).Adj v2 w} : Finset (Fin n)) = {v0, v1} := by
      ext w
      simp [FamilyH, v0, v1, v2, Fin.ext_iff]
    rw [hneighbors]
    simp [v0, v1, v2]
  by_cases h3 : v.val = 3
  · have hv : v = v3 := Fin.ext (by simpa [v3] using h3)
    subst v
    rw [degree, neighborFinset_eq_filter]
    have hneighbors :
        ({w | (FamilyH n).Adj v3 w} : Finset (Fin n)) = {v0, v4} := by
      ext w
      simp [FamilyH, v0, v3, v4, Fin.ext_iff]
    rw [hneighbors]
    simp [v0, v3, v4]
  by_cases h4 : v.val = 4
  · have hv : v = v4 := Fin.ext (by simpa [v4] using h4)
    subst v
    rw [degree, neighborFinset_eq_filter]
    let leaves : Finset (Fin n) := {w | 5 ≤ w.val}
    have hneighbors :
        ({w | (FamilyH n).Adj v4 w} : Finset (Fin n)) = insert v3 leaves := by
      ext w
      simp [FamilyH, v3, v4, leaves, Fin.ext_iff]
    rw [hneighbors]
    have hnot : v3 ∉ leaves := by simp [v3, leaves]
    rw [card_insert_of_notMem hnot]
    let tailEquiv : Fin (n - 5) ≃ {w : Fin n // 5 ≤ w.val} :=
      { toFun := fun i ↦
          ⟨⟨i.val + 5, by omega⟩,
            by change 5 ≤ i.val + 5; omega⟩
        invFun := fun w ↦ ⟨w.val.val - 5, by omega⟩
        left_inv := by
          intro i
          apply Fin.ext
          simp
        right_inv := by
          intro w
          apply Subtype.ext
          apply Fin.ext
          simp
          omega }
    have htail : Fintype.card {w : Fin n // 5 ≤ w.val} = n - 5 := by
      simpa using (Fintype.card_congr tailEquiv).symm
    have hleaves : #leaves = n - 5 := by
      exact (Fintype.card_subtype fun w : Fin n ↦ 5 ≤ w.val).symm.trans htail
    simp [hleaves, v4]
    omega
  rw [degree, neighborFinset_eq_filter]
  have h5 : 5 ≤ v.val := by omega
  have hneighbors :
      ({w | (FamilyH n).Adj v w} : Finset (Fin n)) = {v4} := by
    ext w
    simp [FamilyH, v4, Fin.ext_iff, h0, h1, h2, h3, h4, h5]
  rw [hneighbors]
  simp [h0, h1, h2, h3, h4]

/-- The degree formula sums to `2n`. -/
theorem family_sum_degrees {n : ℕ} (hn : 7 ≤ n) :
    ∑ v : Fin n, (FamilyH n).degree v = 2 * n := by
  obtain ⟨k, hn5⟩ := Nat.exists_eq_add_of_le (show 5 ≤ n by omega)
  rw [Nat.add_comm] at hn5
  subst n
  simp_rw [family_degree_formula (n := k + 5) (by omega)]
  simp_rw [Fin.sum_univ_succ]
  have hmod5 : 2 % (k + 5) = 2 := Nat.mod_eq_of_lt (by omega)
  have hmod3 : 2 % (k + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  simp [hmod5, hmod3]
  omega

/-- The graph defined by `FamilyH` has exactly `n` edges for every `n ≥ 7`. -/
theorem family_edge_count {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyH n).edgeFinset = n := by
  have hhandshake := (FamilyH n).sum_degrees_eq_twice_card_edges
  rw [family_sum_degrees hn] at hhandshake
  omega

/-- The seven-vertex complement in the infinite family. -/
def H7Edges : Finset (Sym2 (Fin 7)) :=
  {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(3, 4), s(4, 5), s(4, 6)}

def H7 : SimpleGraph (Fin 7) := SimpleGraph.fromEdgeSet (H7Edges : Set (Sym2 (Fin 7)))

instance : DecidableRel H7.Adj := by
  unfold H7
  infer_instance

/-- The seven-vertex counterexample graph. -/
def G7 : SimpleGraph (Fin 7) := H7ᶜ

instance : DecidableRel G7.Adj := by
  unfold G7
  infer_instance

/-- The supplied eight-vertex complement, in the labeling from the PDF. -/
def SuppliedH8Edges : Finset (Sym2 (Fin 8)) :=
  {s(0, 2), s(0, 3), s(0, 4), s(1, 2), s(1, 5), s(1, 6), s(1, 7), s(3, 4)}

def SuppliedH8 : SimpleGraph (Fin 8) :=
  SimpleGraph.fromEdgeSet (SuppliedH8Edges : Set (Sym2 (Fin 8)))

instance : DecidableRel SuppliedH8.Adj := by
  unfold SuppliedH8
  infer_instance

def SuppliedG8 : SimpleGraph (Fin 8) := SuppliedH8ᶜ

instance : DecidableRel SuppliedG8.Adj := by
  unfold SuppliedG8
  infer_instance

/-- A direct finite formulation of containing a complete bipartite spanning subgraph. -/
def HasCompleteBipartiteSpanning {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ A : Finset V,
    A.Nonempty ∧ A ≠ univ ∧ ∀ u ∈ A, ∀ v ∈ univ \ A, G.Adj u v

instance {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable (HasCompleteBipartiteSpanning G) :=
by
  unfold HasCompleteBipartiteSpanning
  infer_instance

/-- If the complement is connected, no nontrivial spanning bipartition can
contain every cross edge of the original graph.  This is the general
graph-theoretic obstruction used by the infinite family, rather than a
finite check for the first two witnesses. -/
theorem connected_complement_forbids_complete_bipartite_spanning
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : Gᶜ.Connected) : ¬HasCompleteBipartiteSpanning G := by
  rintro ⟨A, hA, hAne, hcross⟩
  obtain ⟨u, hu⟩ := hA
  have houtside : (univ \ A).Nonempty := by
    rw [sdiff_nonempty]
    intro hsub
    apply hAne
    exact eq_univ_iff_forall.mpr fun v ↦ hsub (mem_univ v)
  obtain ⟨v, hv⟩ := houtside
  have preserve {x y : V} (hxy : Gᶜ.Adj x y) (hx : x ∈ A) : y ∈ A := by
    by_contra hy
    have hyout : y ∈ univ \ A := by simp [hy]
    exact (G.compl_adj x y).mp hxy |>.2 (hcross x hx y hyout)
  obtain ⟨p⟩ := hconn u v
  have walk_preserves {x y : V} (q : Gᶜ.Walk x y) (hx : x ∈ A) : y ∈ A := by
    induction q with
    | nil => exact hx
    | cons h q ih => exact ih (preserve h hx)
  exact (by simpa using hv : v ∉ A) (walk_preserves p hu)

/-- The counterexample graph family, defined as the complement of `FamilyH`. -/
def FamilyG (n : ℕ) : SimpleGraph (Fin n) := (FamilyH n)ᶜ

instance (n : ℕ) : DecidableRel (FamilyG n).Adj := by
  unfold FamilyG
  infer_instance

/-- The connected-complement obstruction holds uniformly for every member of
the family, not only for the finite witnesses checked below. -/
theorem family_no_complete_bipartite_spanning {n : ℕ} (hn : 7 ≤ n) :
    ¬HasCompleteBipartiteSpanning (FamilyG n) := by
  apply connected_complement_forbids_complete_bipartite_spanning
  simpa [FamilyG] using family_connected hn

/-- The complement family has the manuscript's all-order edge count. -/
theorem family_complement_edge_count {n : ℕ} (hn : 7 ≤ n) :
    #(FamilyG n).edgeFinset = n.choose 2 - n := by
  have hedges :
      (FamilyG n).edgeFinset =
        (⊤ : SimpleGraph (Fin n)).edgeFinset \ (FamilyH n).edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | h u v => simp [FamilyG, compl_adj]
  rw [hedges, card_sdiff_of_subset (edgeFinset_mono le_top)]
  have htop : #((⊤ : SimpleGraph (Fin n)).edgeFinset) = n.choose 2 := by
    simpa using (card_edgeFinset_top_eq_card_choose_two (V := Fin n))
  rw [htop, family_edge_count hn]

/-- The symbolic edge decomposition printed in the manuscript has exactly
`n` entries: three triangle edges, two path edges, and `n - 5` leaf edges. -/
theorem family_edge_decomposition_count {n : ℕ} (hn : 7 ≤ n) :
    3 + 2 + (n - 5) = n := by
  omega

theorem H7_edge_count : #H7.edgeFinset = 7 := by native_decide

theorem G7_edge_count : #G7.edgeFinset = 14 := by native_decide

theorem H7_connected : H7.Connected := by native_decide

theorem G7_no_complete_bipartite_spanning : ¬HasCompleteBipartiteSpanning G7 := by
  native_decide

/-- The finite leaf certificate used by the suspension step at order seven. -/
theorem H7_leaf_certificate :
    H7.neighborFinset 5 = {4} ∧
      H7.neighborFinset 4 = {3, 5, 6} ∧
      univ \ insert 4 (H7.neighborFinset 4) = {0, 1, 2} ∧
      H7.Adj 0 1 ∧ H7.Adj 0 2 ∧ H7.Adj 1 2 := by
  native_decide

theorem supplied_H8_edge_count : #SuppliedH8.edgeFinset = 8 := by native_decide

theorem supplied_G8_edge_count : #SuppliedG8.edgeFinset = 20 := by native_decide

theorem supplied_H8_connected : SuppliedH8.Connected := by native_decide

theorem supplied_G8_no_complete_bipartite_spanning :
    ¬HasCompleteBipartiteSpanning SuppliedG8 := by
  native_decide

/-- The exact leaf certificate printed in the supplied manuscript. -/
theorem supplied_H8_leaf_certificate :
    SuppliedH8.neighborFinset 5 = {1} ∧
      SuppliedH8.neighborFinset 1 = {2, 5, 6, 7} ∧
      univ \ insert 1 (SuppliedH8.neighborFinset 1) = {0, 3, 4} ∧
      SuppliedH8.Adj 0 3 ∧ SuppliedH8.Adj 0 4 ∧ SuppliedH8.Adj 3 4 := by
  native_decide

/-- Four components in the leaf remainder would force too many cross edges. -/
theorem four_components_cross_edge_contradiction
    {N e : ℕ} (hN : 4 ≤ N) (upper : e ≤ N + 1) (lower : 3 * N - 6 ≤ e) : False := by
  omega

/-- Algebraic density inequality behind `binom(n,2)-n >= floor(n^2/4)`. -/
theorem dense_gap_nonnegative {n : ℤ} (hn : 7 ≤ n) : 0 ≤ n * (n - 6) := by
  nlinarith

/-- Strict denominator-cleared form of the manuscript's post-Turán inequality.
It proves the stronger rational inequality
`n^2 / 4 < binom(n,2) - n`; hence the same strict inequality holds with
`floor(n^2 / 4)` on the left. -/
theorem dense_range_cleared_strict {n : ℤ} (hn : 7 ≤ n) :
    n * n < 2 * n * (n - 3) := by
  nlinarith

/-- Equivalent denominator-cleared form of the dense-range inequality. -/
theorem dense_range_cleared {n : ℤ} (hn : 7 ≤ n) : n * n ≤ 2 * n * (n - 3) := by
  exact (dense_range_cleared_strict hn).le

#print axioms family_connected
#print axioms family_leaf_triangle_certificate
#print axioms family_degree_formula
#print axioms family_sum_degrees
#print axioms family_edge_count
#print axioms connected_complement_forbids_complete_bipartite_spanning
#print axioms family_no_complete_bipartite_spanning
#print axioms family_complement_edge_count
#print axioms family_edge_decomposition_count
#print axioms H7_edge_count
#print axioms G7_edge_count
#print axioms H7_connected
#print axioms G7_no_complete_bipartite_spanning
#print axioms H7_leaf_certificate
#print axioms supplied_H8_edge_count
#print axioms supplied_G8_edge_count
#print axioms supplied_H8_connected
#print axioms supplied_G8_no_complete_bipartite_spanning
#print axioms supplied_H8_leaf_certificate
#print axioms four_components_cross_edge_contradiction
#print axioms dense_gap_nonnegative
#print axioms dense_range_cleared_strict
#print axioms dense_range_cleared

end ExtremalFlagBetti
