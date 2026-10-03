module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic

@[expose] public section

/-! A connected six-vertex counterexample to Rubalcaba (2005), Conjecture 5.2.5.
The graph is a diamond with an attached path of length two. We use the actual
real-valued fractional domination and packing faces, not just integral solutions.
Four small integral vectors certify all claims over these continuous faces. -/
namespace ShellObservability.FractionalCounterexample

abbrev V := Fin 6

def adjacent (a b : V) : Prop :=
  (a.val, b.val) ∈ ({(0,4),(4,0),(0,5),(5,0),(1,3),(3,1),(1,4),(4,1),
    (2,3),(3,2),(2,4),(4,2),(3,4),(4,3)} : Finset (ℕ × ℕ))

instance (a b : V) : Decidable (adjacent a b) := by
  unfold adjacent
  infer_instance

def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (adjacent a b))

theorem graph_connected : graph.Connected := by decide

def load (f : V → ℝ) (v : V) : ℝ :=
  ∑ u, if u.val = v.val ∨ graph.Adj v u then f u else 0

/-- The finite-index implementation is exactly the closed-neighborhood sum. -/
theorem load_eq_closed_sum (f : V → ℝ) (v : V) :
    load f v = ∑ u, if u = v ∨ graph.Adj v u then f u else 0 := by
  simp only [load, Fin.val_inj]

def mass (f : V → ℝ) : ℝ := ∑ v, f v

def FractionalDominating (f : V → ℝ) : Prop :=
  (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ ∀ v, 1 ≤ load f v

def FractionalPacking (f : V → ℝ) : Prop :=
  (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ ∀ v, load f v ≤ 1

def minimumFace : Set (V → ℝ) := {f | FractionalDominating f ∧
  ∀ g, FractionalDominating g → mass f ≤ mass g}

def maximumFace : Set (V → ℝ) := {f | FractionalPacking f ∧
  ∀ g, FractionalPacking g → mass g ≤ mass f}

/-- Exactly the intersection class of the published conjecture. -/
def ClassI : Prop := (minimumFace ∩ maximumFace).Nonempty ∧
  ¬ minimumFace ⊆ maximumFace ∧ ¬ maximumFace ⊆ minimumFace

def DominationNull (v : V) : Prop := ∀ f ∈ minimumFace, f v = 0
def PackingNull (v : V) : Prop := ∀ f ∈ maximumFace, f v = 0

/-- Vertices 3 and 5 have closed neighborhoods partitioning the vertex set. -/
theorem load_partition (f : V → ℝ) : load f 3 + load f 5 = mass f := by
  simp [load, mass, graph, adjacent, Fin.sum_univ_succ]
  ring

theorem domination_bound (f : V → ℝ) (hf : FractionalDominating f) :
    2 ≤ mass f := by
  have h3 := hf.2 3
  have h5 := hf.2 5
  rw [← load_partition]
  linarith

theorem packing_bound (f : V → ℝ) (hf : FractionalPacking f) :
    mass f ≤ 2 := by
  have h3 := hf.2 3
  have h5 := hf.2 5
  rw [← load_partition]
  linarith

def efficient : V → ℝ := ![0,0,0,1,0,1]
def domOnly : V → ℝ := ![1,0,0,0,1,0]
def packOnly : V → ℝ := ![0,1,0,0,0,1]
def packOther : V → ℝ := ![0,0,1,0,0,1]

theorem efficient_dom : FractionalDominating efficient := by
  constructor <;> intro v <;> fin_cases v <;>
    norm_num [efficient, load, graph, adjacent, Fin.sum_univ_succ]

theorem efficient_pack : FractionalPacking efficient := by
  constructor <;> intro v <;> fin_cases v <;>
    norm_num [efficient, load, graph, adjacent, Fin.sum_univ_succ]

theorem domOnly_dom : FractionalDominating domOnly := by
  constructor <;> intro v <;> fin_cases v <;>
    norm_num [domOnly, load, graph, adjacent, Fin.sum_univ_succ]

theorem packOnly_pack : FractionalPacking packOnly := by
  constructor <;> intro v <;> fin_cases v <;>
    norm_num [packOnly, load, graph, adjacent, Fin.sum_univ_succ]

theorem packOther_pack : FractionalPacking packOther := by
  constructor <;> intro v <;> fin_cases v <;>
    norm_num [packOther, load, graph, adjacent, Fin.sum_univ_succ]

theorem mass_efficient : mass efficient = 2 := by
  norm_num [mass, efficient, Fin.sum_univ_succ]
theorem mass_domOnly : mass domOnly = 2 := by
  norm_num [mass, domOnly, Fin.sum_univ_succ]
theorem mass_packOnly : mass packOnly = 2 := by
  norm_num [mass, packOnly, Fin.sum_univ_succ]
theorem mass_packOther : mass packOther = 2 := by
  norm_num [mass, packOther, Fin.sum_univ_succ]

theorem efficient_min : efficient ∈ minimumFace := by
  refine ⟨efficient_dom, ?_⟩
  intro g hg
  rw [mass_efficient]
  exact domination_bound g hg

theorem efficient_max : efficient ∈ maximumFace := by
  refine ⟨efficient_pack, ?_⟩
  intro g hg
  rw [mass_efficient]
  exact packing_bound g hg

theorem domOnly_min : domOnly ∈ minimumFace := by
  refine ⟨domOnly_dom, ?_⟩
  intro g hg
  rw [mass_domOnly]
  exact domination_bound g hg

theorem packOnly_max : packOnly ∈ maximumFace := by
  refine ⟨packOnly_pack, ?_⟩
  intro g hg
  rw [mass_packOnly]
  exact packing_bound g hg

theorem packOther_max : packOther ∈ maximumFace := by
  refine ⟨packOther_pack, ?_⟩
  intro g hg
  rw [mass_packOther]
  exact packing_bound g hg

theorem domOnly_not_pack : ¬ FractionalPacking domOnly := by
  intro h
  have h4 := h.2 4
  norm_num [load, domOnly, graph, adjacent, Fin.sum_univ_succ] at h4

theorem packOnly_not_dom : ¬ FractionalDominating packOnly := by
  intro h
  have h2 := h.2 2
  norm_num [load, packOnly, graph, adjacent, Fin.sum_univ_succ] at h2

theorem graph_classI : ClassI := by
  refine ⟨⟨efficient, efficient_min, efficient_max⟩, ?_, ?_⟩
  · intro h
    exact domOnly_not_pack (h domOnly_min).1
  · intro h
    exact packOnly_not_dom (h packOnly_max).1

/-- Each vertex has positive weight in a member of at least one optimal face. -/
theorem no_joint_null (v : V) : ¬ (DominationNull v ∧ PackingNull v) := by
  rintro ⟨hd, hp⟩
  have hd0 := hd domOnly domOnly_min
  have hp0 := hp efficient efficient_max
  have hp1 := hp packOnly packOnly_max
  have hp2 := hp packOther packOther_max
  fin_cases v <;> norm_num [domOnly, efficient, packOnly, packOther] at *

/-- Negation of the conclusion in Rubalcaba's Conjecture 5.2.5. -/
theorem conjectured_conclusion_false : ¬ ∃ v, DominationNull v ∧ PackingNull v := by
  rintro ⟨v, hv⟩
  exact no_joint_null v hv

theorem counterexample : ClassI ∧ ¬ ∃ v, DominationNull v ∧ PackingNull v :=
  ⟨graph_classI, conjectured_conclusion_false⟩

end ShellObservability.FractionalCounterexample
