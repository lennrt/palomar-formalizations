/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
Preprint published: 2026-08-14. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import K331Tutte.FiniteHomologyDefs

/-!
# Proved four-vertex relative-homology calculation

The solution proves the explicit F₂ local calculation behind Lemma 4.3 and
the cycle-count implication in Remark 7.2. Its proof cone does not import the
legacy native finite-enumeration module.
-/

set_option maxHeartbeats 4000000

namespace K331Tutte.FiniteHomology

private theorem f2add_eq_true {a b : Bool} (h : f2add a b = true) :
    a = true ∨ b = true := by
  cases a <;> cases b <;> simp_all [f2add]

private theorem supported2_add {available x y : Chain2}
    (hx : Supported2 available x) (hy : Supported2 available y) :
    Supported2 available (add2 x y) := by
  rcases hx with ⟨hx₀, hx₁, hx₂, hx₃⟩
  rcases hy with ⟨hy₀, hy₁, hy₂, hy₃⟩
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₀ h
    · exact hy₀ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₁ h
    · exact hy₁ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₂ h
    · exact hy₂ h
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₃ h
    · exact hy₃ h

private theorem supportedBoundary_add {boundary x y : Chain1}
    (hx : SupportedOnBoundaryEdges boundary x)
    (hy : SupportedOnBoundaryEdges boundary y) :
    SupportedOnBoundaryEdges boundary (add1 x y) := by
  rcases hx with ⟨hx₀, hx₁, hx₂, hx₃, hx₄, hx₅⟩
  rcases hy with ⟨hy₀, hy₁, hy₂, hy₃, hy₄, hy₅⟩
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₀ h
    · exact hy₀ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₁ h
    · exact hy₁ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₂ h
    · exact hy₂ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₃ h
    · exact hy₃ h
  constructor
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₄ h
    · exact hy₄ h
  · intro h
    rcases f2add_eq_true h with h | h
    · exact hx₅ h
    · exact hy₅ h

private theorem relativeCycle_add {c : FourVertexPair} {x y : Chain2}
    (hx : RelativeCycle c x) (hy : RelativeCycle c y) :
    RelativeCycle c (add2 x y) := by
  rcases hx with ⟨hxs, hxb⟩
  rcases hy with ⟨hys, hyb⟩
  exact ⟨supported2_add hxs hys, by
    rw [d2_add]
    exact supportedBoundary_add hxb hyb⟩

private theorem zero_is_relative_cycle (c : FourVertexPair) :
    RelativeCycle c zero2 := by
  simp [RelativeCycle, Supported2, SupportedOnBoundaryEdges, zero2, d2, f2add]

theorem d3_boundary_is_cycle (c : FourVertexPair) (h : Admissible c) :
    RelativeCycle c (d3Boundary c) := by
  rcases c with ⟨⟨f₀, f₁, f₂, f₃⟩, tet, ⟨v₀, v₁, v₂, v₃⟩,
    ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩⟩
  cases tet
  · exact zero_is_relative_cycle _
  · cases v₀ <;> cases v₁ <;> cases v₂ <;> cases v₃ <;>
      simp_all [Admissible, d3Boundary, RelativeCycle, Supported2,
        SupportedOnBoundaryEdges, relativeFaces, allBoundaryFaceFlags,
        d2, f2add]

private theorem add2_right_cancel {x y b : Chain2}
    (h : add2 x b = add2 y b) : x = y := by
  have h' := congrArg (fun q => add2 q b) h
  simpa [add2_assoc] using h'

private theorem orbit_no_fixed {x b : Chain2} (hb : b ≠ zero2) :
    x ≠ add2 x b := by
  intro h
  apply hb
  apply add2_left_cancel (x := x)
  simpa using h.symm

private theorem orbit_disjoint {x y b : Chain2}
    (hxy : ¬ (x = y ∨ x = add2 y b)) :
    x ≠ y ∧ x ≠ add2 y b ∧
      add2 x b ≠ y ∧ add2 x b ≠ add2 y b := by
  constructor
  · intro h
    exact hxy (Or.inl h)
  constructor
  · intro h
    exact hxy (Or.inr h)
  constructor
  · intro h
    apply hxy
    right
    calc
      x = add2 (add2 x b) b := by simp [add2_assoc]
      _ = add2 y b := by rw [h]
  · intro h
    apply hxy
    left
    exact add2_right_cancel h

private theorem six_orbit_chains_nodup {x y z b : Chain2}
    (hb : b ≠ zero2)
    (hxy : ¬ (x = y ∨ x = add2 y b))
    (hxz : ¬ (x = z ∨ x = add2 z b))
    (hyz : ¬ (y = z ∨ y = add2 z b)) :
    [x, add2 x b, y, add2 y b, z, add2 z b].Nodup := by
  have hxx := orbit_no_fixed (x := x) hb
  have hyy := orbit_no_fixed (x := y) hb
  have hzz := orbit_no_fixed (x := z) hb
  have hxy' := orbit_disjoint hxy
  have hxz' := orbit_disjoint hxz
  have hyz' := orbit_disjoint hyz
  simp [List.nodup_cons, hxx, hyy, hzz,
    hxy'.1, hxy'.2.1, hxy'.2.2.1, hxy'.2.2.2,
    hxz'.1, hxz'.2.1, hxz'.2.2.1, hxz'.2.2.2,
    hyz'.1, hyz'.2.1, hyz'.2.2.1, hyz'.2.2.2]

/-- Remark 7.2: the `2/4` cycle-count certificate gives at most two H₂ classes. -/
theorem cycle_count_criterion_implies_homology_bound
    (c : FourVertexPair) (hadm : Admissible c)
    (hcount : CycleCountCriterion c) :
    HomologyDimensionAtMostOne c := by
  intro q₀ q₁ q₂
  refine Quotient.inductionOn₃ q₀ q₁ q₂ ?_
  intro x y z
  by_cases hxy : Homologous c x.1 y.1
  · exact Or.inl (Quotient.sound hxy)
  by_cases hxz : Homologous c x.1 z.1
  · exact Or.inr (Or.inl (Quotient.sound hxz))
  by_cases hyz : Homologous c y.1 z.1
  · exact Or.inr (Or.inr (Quotient.sound hyz))
  exfalso
  rcases hcount with ⟨hb, htwo⟩ | ⟨hb, hfour⟩
  · have hxy' : x.1 ≠ y.1 := by
      intro h
      exact hxy (Or.inl h)
    have hxz' : x.1 ≠ z.1 := by
      intro h
      exact hxz (Or.inl h)
    have hyz' : y.1 ≠ z.1 := by
      intro h
      exact hyz (Or.inl h)
    have hn : [x.1, y.1, z.1].Nodup := by
      simp [hxy', hxz', hyz']
    have hc := htwo [x.1, y.1, z.1] hn (by
      intro w hw
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact x.2
      · exact y.2
      · exact z.2)
    simp only [List.length_cons, List.length_nil] at hc
    omega
  · let b := d3Boundary c
    have hbcycle : RelativeCycle c b := d3_boundary_is_cycle c hadm
    have hxy' : ¬ (x.1 = y.1 ∨ x.1 = add2 y.1 b) := hxy
    have hxz' : ¬ (x.1 = z.1 ∨ x.1 = add2 z.1 b) := hxz
    have hyz' : ¬ (y.1 = z.1 ∨ y.1 = add2 z.1 b) := hyz
    have hn := six_orbit_chains_nodup hb hxy' hxz' hyz'
    have hc := hfour
      [x.1, add2 x.1 b, y.1, add2 y.1 b, z.1, add2 z.1 b] hn (by
        intro w hw
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hw
        rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
        · exact x.2
        · exact relativeCycle_add x.2 hbcycle
        · exact y.2
        · exact relativeCycle_add y.2 hbcycle
        · exact z.2
        · exact relativeCycle_add z.2 hbcycle)
    simp only [List.length_cons, List.length_nil] at hc
    omega

/-- Coordinate classification behind Lemma 4.3: there are at most two relative cycles. -/
theorem admissible_relative_cycles_classified
    (c : FourVertexPair) (hadm : Admissible c)
    (z : Chain2) (hz : RelativeCycle c z) :
    z = zero2 ∨ z = nonBoundaryFaceSum c := by
  rcases c with ⟨⟨f₀, f₁, f₂, f₃⟩, tet, ⟨v₀, v₁, v₂, v₃⟩,
    ⟨e₀, e₁, e₂, e₃, e₄, e₅⟩⟩
  rcases z with ⟨z₀, z₁, z₂, z₃⟩
  cases v₀ <;> cases v₁ <;> cases v₂ <;> cases v₃ <;>
    cases z₀ <;> cases z₁ <;> cases z₂ <;> cases z₃ <;>
    simp_all [Admissible, RelativeCycle, Supported2, SupportedOnBoundaryEdges,
      relativeFaces, allBoundaryFaceFlags, nonBoundaryFaceSum, d2, zero2, f2add]

/-- The hand classification gives a direct at-most-two cycle certificate. -/
theorem admissible_cycle_count_at_most_two
    (c : FourVertexPair) (hadm : Admissible c) :
    CycleCountAtMost c 2 := by
  intro chains hn hcycles
  cases chains with
  | nil => simp
  | cons a tail =>
    cases tail with
    | nil => simp
    | cons b tail =>
      cases tail with
      | nil => simp
      | cons d rest =>
        have ha := admissible_relative_cycles_classified c hadm a
          (hcycles a (by simp))
        have hb := admissible_relative_cycles_classified c hadm b
          (hcycles b (by simp))
        have hd := admissible_relative_cycles_classified c hadm d
          (hcycles d (by simp))
        rcases ha with ha | ha <;> rcases hb with hb | hb <;>
          rcases hd with hd | hd <;> subst_vars <;>
          simp_all [List.nodup_cons]

/-- Every admissible four-vertex pair satisfies Remark 7.2's cycle threshold. -/
theorem admissible_cycle_count_criterion
    (c : FourVertexPair) (hadm : Admissible c) :
    CycleCountCriterion c := by
  have htwo := admissible_cycle_count_at_most_two c hadm
  by_cases hb : d3Boundary c = zero2
  · exact Or.inl ⟨hb, htwo⟩
  · right
    refine ⟨hb, ?_⟩
    intro chains hn hcycles
    exact Nat.le_trans (htwo chains hn hcycles) (by omega)

/-- Lemma 4.3: an admissible induced four-vertex pair has `dim_F₂ H₂ ≤ 1`. -/
theorem admissible_four_vertex_relative_homology_bound
    (c : FourVertexPair) (hadm : Admissible c) :
    HomologyDimensionAtMostOne c := by
  exact cycle_count_criterion_implies_homology_bound c hadm
    (admissible_cycle_count_criterion c hadm)

#print axioms d3_boundary_is_cycle
#print axioms cycle_count_criterion_implies_homology_bound
#print axioms admissible_relative_cycles_classified
#print axioms admissible_cycle_count_at_most_two
#print axioms admissible_cycle_count_criterion
#print axioms admissible_four_vertex_relative_homology_bound

end K331Tutte.FiniteHomology
