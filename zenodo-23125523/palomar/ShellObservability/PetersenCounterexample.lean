module

public import ShellObservability.ModularObstruction
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! A modular certificate for the generalized Petersen graph P(11,4).
Vertices 0..10 are outer, and 11..21 are inner. -/
namespace ShellObservability.Petersen

abbrev V := Fin 22

def adjacent (a b : V) : Prop :=
  if a.val < 11 then
    if b.val < 11 then b.val = (a.val+1)%11 ∨ a.val = (b.val+1)%11
    else b.val = a.val+11
  else
    if b.val < 11 then a.val = b.val+11
    else b.val-11 = (a.val-11+4)%11 ∨ a.val-11 = (b.val-11+4)%11

instance (a b : V) : Decidable (adjacent a b) := by unfold adjacent; infer_instance

theorem adjacent_symm : ∀ a b, adjacent a b → adjacent b a := by decide

theorem adjacent_irrefl : ∀ a, ¬ adjacent a a := by decide

def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨fun {a b} => adjacent_symm a b⟩
  loopless := ⟨adjacent_irrefl⟩

instance : DecidableRel graph.Adj := fun a b => inferInstanceAs (Decidable (adjacent a b))

def load (c : V → ℕ) (v : V) : ℕ := ∑ u, if adjacent v u then c u else 0

instance : Fact (Nat.Prime 23) := ⟨by norm_num⟩

def A : Matrix V V (ZMod 23) := fun v u => if adjacent v u then 1 else 0

def weights : V → ZMod 23 :=
  ![-22,26,17,-16,2,5,5,2,-16,17,26,17,5,-10,-19,11,-7,-7,11,-19,-10,5]

set_option maxRecDepth 10000 in
theorem weights_kernel : Matrix.vecMul weights A = 0 := by
  decide

set_option maxRecDepth 10000 in
theorem weights_sum : ∑ v, weights v = 0 := by decide

set_option maxRecDepth 10000 in
theorem weights_full : ∀ v, weights v ≠ 0 := by decide

theorem load_cast (c : V → ℕ) (v : V) :
    (load c v : ZMod 23) = A.mulVec (fun u => (c u : ZMod 23)) v := by
  simp only [load, Nat.cast_sum, Matrix.mulVec, dotProduct, A]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : adjacent v u <;> simp [h]

/-- Seven disjoint open neighborhoods would cover every vertex except one.
The field certificate rules out that exact defect for every possible vertex. -/
theorem no_single_uncovered (c : V → ℕ) (r : V) :
    ¬ (∀ v, load c v = if v = r then 0 else 1) := by
  intro h
  apply no_single_defect A weights weights_kernel weights_sum weights_full
    (fun v => (c v : ZMod 23)) r
  funext v
  rw [← load_cast, h]
  split_ifs <;> simp

theorem total_load (c : V → ℕ) : (∑ v, load c v) = 3 * ∑ v, c v := by
  unfold load
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  fin_cases u <;> simp [adjacent, Fin.sum_univ_succ] <;> omega

/-- Every integral open-neighborhood packing has at most six selected vertices. -/
theorem packing_bound (c : V → ℕ) (hc : ∀ v, load c v ≤ 1) :
    (∑ v, c v) ≤ 6 := by
  have htot : (∑ v, load c v) ≤ 22 := by
    calc
      _ ≤ ∑ _v : V, 1 := Finset.sum_le_sum (fun v _ => hc v)
      _ = 22 := by simp [V]
  have he := total_load c
  by_contra hlarge
  have hmass : (∑ v, c v) = 7 := by omega
  have hsum : (∑ v, load c v) + 1 = Fintype.card V := by
    rw [total_load, hmass]
    decide
  obtain ⟨r, hr⟩ := single_defect_of_total (load c) hc hsum
  exact no_single_uncovered c r hr

def indicator (S : Finset V) (v : V) : ℕ := if v ∈ S then 1 else 0

def DoubleTotalDominating (S : Finset V) : Prop :=
  ∀ v, 2 ≤ load (indicator S) v

theorem indicator_sum (S : Finset V) : (∑ v, indicator S v) = S.card := by
  simp [indicator]

theorem complement_load (S : Finset V) (v : V) :
    load (indicator S) v + load (indicator (Finset.univ \ S)) v = 3 := by
  unfold load
  rw [← Finset.sum_add_distrib]
  have hterm (u : V) :
      (if adjacent v u then indicator S u else 0) +
      (if adjacent v u then indicator (Finset.univ \ S) u else 0) =
        if adjacent v u then 1 else 0 := by
    by_cases ha : adjacent v u <;> by_cases hu : u ∈ S <;> simp [ha, hu, indicator]
  simp_rw [hterm]
  fin_cases v <;> decide

/-- The formal load predicate is exactly double total domination in the actual
simple graph, expressed by its induced neighbor subset. -/
theorem domination_iff_graph (S : Finset V) :
    DoubleTotalDominating S ↔ ∀ v, 2 ≤ (S.filter (graph.Adj v)).card := by
  unfold DoubleTotalDominating
  have hl (v : V) : load (indicator S) v = (S.filter (graph.Adj v)).card := by
    unfold load indicator
    have ht (u : V) :
        (if adjacent v u then if u ∈ S then 1 else 0 else 0) =
          if u ∈ S ∧ adjacent v u then 1 else 0 := by
      by_cases ha : adjacent v u <;> by_cases hu : u ∈ S <;> simp [ha, hu]
    simp_rw [ht]
    rw [Finset.sum_boole]
    apply congrArg Finset.card
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  simp only [hl]

/-- Every double total dominating set has at least sixteen vertices. -/
theorem domination_lower_bound (S : Finset V) (hS : DoubleTotalDominating S) :
    16 ≤ S.card := by
  have hc : ∀ v, load (indicator (Finset.univ \ S)) v ≤ 1 := by
    intro v
    have := complement_load S v
    have := hS v
    omega
  have hb := packing_bound (indicator (Finset.univ \ S)) hc
  rw [indicator_sum, Finset.card_sdiff_of_subset (Finset.subset_univ S)] at hb
  have hcard : S.card ≤ 22 := by
    have := Finset.card_le_card (Finset.subset_univ S)
    simpa [V] using this
  simp only [Finset.card_univ, V, Fintype.card_fin] at hb
  omega

/-- An explicit open packing; its complement is the matching upper bound. -/
def packingWitness : Finset V := {0,5,8,13,14,19}

def dominationWitness : Finset V := Finset.univ \ packingWitness

theorem dominationWitness_card : dominationWitness.card = 16 := by decide

theorem dominationWitness_valid : DoubleTotalDominating dominationWitness := by
  unfold DoubleTotalDominating
  decide

/-- Exact minimum and the counterexample value, expressed without an arbitrary
choice of minimizing set. -/
theorem exact_domination :
    (∃ S : Finset V, S.card = 16 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 16 ≤ S.card) := by
  exact ⟨⟨dominationWitness, dominationWitness_card, dominationWitness_valid⟩,
    domination_lower_bound⟩

/-- Conjecture 3.1 of Zhao--Wei predicts fifteen for n=11, k=4. -/
theorem conjectured_value_false :
    ¬ ∃ S : Finset V, S.card = 15 ∧ DoubleTotalDominating S := by
  rintro ⟨S, hcard, hS⟩
  have := domination_lower_bound S hS
  omega

end ShellObservability.Petersen
