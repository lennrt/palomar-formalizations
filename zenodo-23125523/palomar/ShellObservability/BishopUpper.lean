module

public import ShellObservability.BishopParity

@[expose] public section

/-! A literal two-column 2-dominating set for every bishop board with at least
 two columns. The domination requirement applies only outside the selected set. -/
namespace ShellObservability.BishopParity
open Finset

def outerColumns (N : ℕ) : Finset (Square N) :=
  {⟨0, by omega⟩, ⟨N, by omega⟩} ×ˢ univ

@[simp] theorem mem_outerColumns {N : ℕ} (v : Square N) :
    v ∈ outerColumns N ↔ v.1.val = 0 ∨ v.1.val = N := by
  simp only [outerColumns, mem_product, mem_insert, mem_singleton, mem_univ, and_true, Fin.ext_iff]

theorem outerColumns_card {N : ℕ} (hN : 0 < N) :
    (outerColumns N).card = 2*(N+1) := by
  have hne : (⟨0, by omega⟩ : Fin (N+1)) ≠ ⟨N, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp only at this; omega
  rw [outerColumns, card_product, card_pair hne]
  simp

/-- Every sum diagonal reaches one of the two outer columns. -/
theorem exists_outer_plus {N : ℕ} (v : Square N) :
    ∃ u ∈ outerColumns N, plus u = plus v := by
  have hx := v.1.isLt
  have hy := v.2.isLt
  by_cases h : v.1.val + v.2.val ≤ N
  · refine ⟨(⟨0, by omega⟩, ⟨v.1.val + v.2.val, by omega⟩), ?_, ?_⟩
    · simp
    · simp [plus]
  · refine ⟨(⟨N, by omega⟩, ⟨v.1.val + v.2.val-N, by omega⟩), ?_, ?_⟩
    · simp
    · simp only [plus]; omega

/-- Reflection gives the corresponding endpoint of the other diagonal. -/
theorem exists_outer_minus {N : ℕ} (v : Square N) :
    ∃ u ∈ outerColumns N, minus u = minus v := by
  obtain ⟨u,hu,he⟩ := exists_outer_plus (flip v)
  refine ⟨flip u, ?_, ?_⟩
  · simpa only [mem_outerColumns, flip] using hu
  · simpa using he

theorem outerColumns_twoDominates (N : ℕ) : TwoDominates (outerColumns N) := by
  intro v hv
  obtain ⟨u,hu,hup⟩ := exists_outer_plus v
  obtain ⟨w,hw,hwm⟩ := exists_outer_minus v
  have huv : u ≠ v := by intro h; subst u; exact hv hu
  have hwv : w ≠ v := by intro h; subst w; exact hv hw
  have huw : u ≠ w := by
    intro h
    subst w
    exact huv (diagonal_intersection u v hup hwm)
  have hsubset : {u,w} ⊆ (outerColumns N).filter (fun x => (graph N).Adj v x) := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact mem_filter.mpr ⟨hu, ⟨Ne.symm huv, Or.inl hup.symm⟩⟩
    · exact mem_filter.mpr ⟨hw, ⟨Ne.symm hwv, Or.inr hwm.symm⟩⟩
  have hc := card_le_card hsubset
  simpa [huw] using hc

theorem two_domination_upper {N : ℕ} (hN : 0 < N) :
    ∃ S : Finset (Square N), TwoDominates S ∧ S.card = 2*(N+1) :=
  ⟨outerColumns N, outerColumns_twoDominates N, outerColumns_card hN⟩

/-- Exact ordinary 2-domination optimum on every positive even board. -/
theorem exact_two_domination {N : ℕ} (hN : N % 2 = 1) :
    (∃ S : Finset (Square N), TwoDominates S ∧ S.card = 2*(N+1)) ∧
    (∀ S : Finset (Square N), TwoDominates S → 2*(N+1) ≤ S.card) := by
  exact ⟨two_domination_upper (by omega), fun S hS => two_domination_lower hN S hS⟩

end ShellObservability.BishopParity
