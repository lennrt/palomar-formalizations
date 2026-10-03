module

public import ShellObservability.ModularObstruction
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-! Two modular checks per bipartition give the exact double total domination
number of the generalized Petersen graph P(16,5). All finite checks use `decide`.
Vertices 0..15 are outer; vertices 16..31 are inner. -/
namespace ShellObservability.PetersenSecond

open Matrix

abbrev V := Fin 32
abbrev W := Fin 16

def adjacent (a b : V) : Prop :=
  if a.val < 16 then
    if b.val < 16 then b.val = (a.val + 1) % 16 ∨ a.val = (b.val + 1) % 16
    else b.val = a.val + 16
  else
    if b.val < 16 then a.val = b.val + 16
    else b.val - 16 = (a.val - 16 + 5) % 16 ∨
      a.val - 16 = (b.val - 16 + 5) % 16

instance (a b : V) : Decidable (adjacent a b) := by
  unfold adjacent
  infer_instance

theorem adjacent_symm : ∀ a b, adjacent a b → adjacent b a := by decide

theorem adjacent_irrefl : ∀ a, ¬ adjacent a a := by decide

def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨fun {a b} => adjacent_symm a b⟩
  loopless := ⟨adjacent_irrefl⟩

instance : DecidableRel graph.Adj :=
  fun a b => inferInstanceAs (Decidable (adjacent a b))

/-- The two actual graph bipartitions, each with sixteen vertices. -/
def part : Bool → W → V
  | false => ![0,2,4,6,8,10,12,14,17,19,21,23,25,27,29,31]
  | true => ![1,3,5,7,9,11,13,15,16,18,20,22,24,26,28,30]

def between (p : Bool) (r u : W) : Prop := adjacent (part (!p) r) (part p u)

instance (p : Bool) (r u : W) : Decidable (between p r u) := by
  unfold between
  infer_instance

def load (c : V → ℕ) (v : V) : ℕ := ∑ u, if adjacent v u then c u else 0

def partLoad (p : Bool) (c : W → ℕ) (r : W) : ℕ :=
  ∑ u, if between p r u then c u else 0

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩

/-- A 16 by 16 incidence matrix from the chosen part to its opposite part. -/
def B (p : Bool) : Matrix W W (ZMod 3) :=
  fun r u => if between p r u then 1 else 0

def weights0 : Bool → W → ZMod 3
  | false => ![1,2,2,1,1,2,2,1,1,0,2,0,1,0,2,0]
  | true => ![1,1,2,2,1,1,2,2,1,0,2,0,1,0,2,0]

def weights1 : Bool → W → ZMod 3
  | false => ![1,1,2,2,1,1,2,2,0,1,0,2,0,1,0,2]
  | true => ![2,1,1,2,2,1,1,2,0,1,0,2,0,1,0,2]

set_option maxRecDepth 20000 in
theorem weights0_kernel : ∀ p, vecMul (weights0 p) (B p) = 0 := by decide

set_option maxRecDepth 20000 in
theorem weights1_kernel : ∀ p, vecMul (weights1 p) (B p) = 0 := by decide

theorem weights0_sum : ∀ p, ∑ r, weights0 p r = 0 := by decide

theorem weights1_sum : ∀ p, ∑ r, weights1 p r = 0 := by decide

/-- Neither individual vector needs full support: their supports cover the part. -/
theorem weights_joint_full : ∀ p r, weights0 p r ≠ 0 ∨ weights1 p r ≠ 0 := by
  decide

/-- The single-defect argument only requires the chosen missing row to carry a
nonzero check weight. This permits a family of checks with jointly full support. -/
theorem no_single_defect_at {X F : Type*} [Fintype X] [DecidableEq X] [Field F]
    (A : Matrix X X F) (w : X → F)
    (hker : vecMul w A = 0) (hsum : ∑ v, w v = 0)
    (c : X → F) (r : X) (hr : w r ≠ 0) :
    A.mulVec c ≠ fun v => if v = r then 0 else 1 := by
  intro he
  have hz : dotProduct w (A.mulVec c) = 0 := by
    rw [dotProduct_mulVec, hker]
    simp
  rw [he] at hz
  have hid (v : X) : w v * (if v = r then (0 : F) else 1) =
      w v - if v = r then w v else 0 := by split_ifs <;> simp
  simp only [dotProduct, hid, Finset.sum_sub_distrib] at hz
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hz
  rw [hsum] at hz
  exact hr (by simpa using hz)

theorem partLoad_cast (p : Bool) (c : W → ℕ) (r : W) :
    (partLoad p c r : ZMod 3) = (B p).mulVec (fun u => (c u : ZMod 3)) r := by
  simp only [partLoad, Nat.cast_sum, Matrix.mulVec, dotProduct, B]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : between p r u <;> simp [h]

theorem no_single_uncovered (p : Bool) (c : W → ℕ) (r : W) :
    ¬ (∀ v, partLoad p c v = if v = r then 0 else 1) := by
  intro h
  have he : (B p).mulVec (fun v => (c v : ZMod 3)) =
      fun v => if v = r then 0 else 1 := by
    funext v
    rw [← partLoad_cast, h]
    split_ifs <;> simp
  rcases weights_joint_full p r with h0 | h1
  · exact no_single_defect_at (B p) (weights0 p) (weights0_kernel p)
      (weights0_sum p) _ r h0 he
  · exact no_single_defect_at (B p) (weights1 p) (weights1_kernel p)
      (weights1_sum p) _ r h1 he

theorem part_total_load (p : Bool) (c : W → ℕ) :
    (∑ r, partLoad p c r) = 3 * ∑ u, c u := by
  unfold partLoad
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  cases p <;> fin_cases u <;>
    simp [between, part, adjacent, Fin.sum_univ_succ] <;> omega

/-- Five disjoint open triples would leave one missing vertex in a part. -/
theorem part_packing_bound (p : Bool) (c : W → ℕ)
    (hc : ∀ r, partLoad p c r ≤ 1) : (∑ u, c u) ≤ 4 := by
  have htot : (∑ r, partLoad p c r) ≤ 16 := by
    calc
      _ ≤ ∑ _r : W, 1 := Finset.sum_le_sum (fun r _ => hc r)
      _ = 16 := by simp [W]
  have he := part_total_load p c
  by_contra hlarge
  have hmass : (∑ u, c u) = 5 := by omega
  have hsum : (∑ r, partLoad p c r) + 1 = Fintype.card W := by
    rw [part_total_load, hmass]
    decide
  obtain ⟨r, hr⟩ := single_defect_of_total (partLoad p c) hc hsum
  exact no_single_uncovered p c r hr

set_option maxHeartbeats 2000000 in
/-- The part matrix is the actual graph neighborhood load at its row vertex. -/
theorem partLoad_eq_load (p : Bool) (c : V → ℕ) (r : W) :
    partLoad p (fun u => c (part p u)) r = load c (part (!p) r) := by
  cases p <;> fin_cases r <;>
    simp [partLoad, load, between, part, adjacent, Fin.sum_univ_succ]

theorem part_bijective : Function.Bijective (fun x : Bool × W => part x.1 x.2) := by
  decide

theorem sum_parts (c : V → ℕ) :
    (∑ v, c v) = (∑ u, c (part false u)) + ∑ u, c (part true u) := by
  have h := Fintype.sum_bijective (fun x : Bool × W => part x.1 x.2)
    part_bijective (fun x => c (part x.1 x.2)) c (fun _ => rfl)
  rw [Fintype.sum_prod_type] at h
  simpa [add_comm] using h.symm

/-- Every integral open-neighborhood packing in P(16,5) has mass at most eight. -/
theorem packing_bound (c : V → ℕ) (hc : ∀ v, load c v ≤ 1) :
    (∑ v, c v) ≤ 8 := by
  have hb (p : Bool) : (∑ u, c (part p u)) ≤ 4 := by
    apply part_packing_bound p
    intro r
    rw [partLoad_eq_load]
    exact hc _
  rw [sum_parts]
  have := hb false
  have := hb true
  omega

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

theorem domination_lower_bound (S : Finset V) (hS : DoubleTotalDominating S) :
    24 ≤ S.card := by
  have hc : ∀ v, load (indicator (Finset.univ \ S)) v ≤ 1 := by
    intro v
    have := complement_load S v
    have := hS v
    omega
  have hb := packing_bound (indicator (Finset.univ \ S)) hc
  rw [indicator_sum, Finset.card_sdiff_of_subset (Finset.subset_univ S)] at hb
  have hcard : S.card ≤ 32 := by
    have := Finset.card_le_card (Finset.subset_univ S)
    simpa [V] using this
  simp only [Finset.card_univ, V, Fintype.card_fin] at hb
  omega

/-- The outer pattern 1100, repeated four times, is an open packing of size8. -/
def packingWitness : Finset V := {0,1,4,5,8,9,12,13}

def dominationWitness : Finset V := Finset.univ \ packingWitness

theorem dominationWitness_card : dominationWitness.card = 24 := by decide

theorem dominationWitness_valid : DoubleTotalDominating dominationWitness := by
  unfold DoubleTotalDominating
  decide

theorem exact_domination :
    (∃ S : Finset V, S.card = 24 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 24 ≤ S.card) := by
  exact ⟨⟨dominationWitness, dominationWitness_card, dominationWitness_valid⟩,
    domination_lower_bound⟩

/-- Conjecture3.2 of Zhao--Wei predicts22 when n16 and k5. -/
theorem conjectured_value_false :
    ¬ ∃ S : Finset V, S.card = 22 ∧ DoubleTotalDominating S := by
  rintro ⟨S, hcard, hS⟩
  have := domination_lower_bound S hS
  omega

end ShellObservability.PetersenSecond
