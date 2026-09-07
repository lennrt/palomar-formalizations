import ShellTomography.Grid
import Mathlib.Order.Interval.Finset.Nat

namespace ShellTomography

/-- A set of fewer than n-2 sensors misses an interior first coordinate. -/
theorem missing_interior_coordinate {n : ℕ} (S : Finset (Grid n))
    (hS : S.card < n - 2) (coord : Grid n → Fin n) :
    ∃ a : ℕ, 1 ≤ a ∧ a + 1 < n ∧ ∀ s ∈ S, (coord s).val ≠ a := by
  classical
  have hcard : (S.image (fun s => (coord s).val)).card < (Finset.Icc 1 (n-2)).card := by
    simpa using (Finset.card_image_le.trans_lt hS)
  have hnot : ¬ Finset.Icc 1 (n-2) ⊆ S.image (fun s => (coord s).val) := by
    intro h
    exact (not_lt_of_ge (Finset.card_le_card h)) hcard
  obtain ⟨a, ha, hmiss⟩ := Finset.not_subset.mp hnot
  have ha' := Finset.mem_Icc.mp ha
  refine ⟨a, ha'.1, by omega, ?_⟩
  intro s hs he
  exact hmiss (Finset.mem_image.mpr ⟨s, hs, he⟩)

/-- The horizontal and vertical pairs around an interior centre look identical
from every sensor outside its row and column. -/
theorem diamond_off_cross {n : ℕ} (a b : ℕ) (ha : 1 ≤ a) (han : a+1 < n)
    (hb : 1 ≤ b) (hbn : b+1 < n) (s : Grid n)
    (hsa : s.1.val ≠ a) (hsb : s.2.val ≠ b) :
    bag manhattan (pairConfig (⟨a-1,by omega⟩,⟨b,by omega⟩)
      (⟨a+1,han⟩,⟨b,by omega⟩)) s =
    bag manhattan (pairConfig (⟨a,by omega⟩,⟨b-1,by omega⟩)
      (⟨a,by omega⟩,⟨b+1,hbn⟩)) s := by
  rw [bag_pairConfig, bag_pairConfig]
  by_cases hu : s.1.val < a <;> by_cases hv : s.2.val < b
  · apply congrArg₂ (fun u v : ℕ => ({u, v} : Multiset ℕ)) <;> dsimp [manhattan, natAbsDiff] <;> omega
  · rw [Multiset.pair_comm]
    apply congrArg₂ (fun u v : ℕ => ({u, v} : Multiset ℕ)) <;> dsimp [manhattan, natAbsDiff] <;> omega
  · rw [Multiset.pair_comm]
    apply congrArg₂ (fun u v : ℕ => ({u, v} : Multiset ℕ)) <;> dsimp [manhattan, natAbsDiff] <;> omega
  · apply congrArg₂ (fun u v : ℕ => ({u, v} : Multiset ℕ)) <;> dsimp [manhattan, natAbsDiff] <;> omega

/-- The diamond obstruction proves the all-order n-2 lower bound for arbitrary
sensor placements, with multiplicities and unknown population size allowed. -/
theorem grid_two_target_lower_bound {n : ℕ} (S : Finset (Grid n))
    (hS : S.card < n - 2) :
    ¬ ResolvesUpTo (fun (s : S) v => (gridGraph n).dist s.val v) 2 := by
  classical
  obtain ⟨a,ha,han,has⟩ := missing_interior_coordinate S hS Prod.fst
  obtain ⟨b,hb,hbn,hbs⟩ := missing_interior_coordinate S hS Prod.snd
  let l : Grid n := (⟨a-1,by omega⟩,⟨b,by omega⟩)
  let r : Grid n := (⟨a+1,han⟩,⟨b,by omega⟩)
  let d : Grid n := (⟨a,by omega⟩,⟨b-1,by omega⟩)
  let u : Grid n := (⟨a,by omega⟩,⟨b+1,hbn⟩)
  intro hresolve
  have he : pairConfig l r = pairConfig d u := by
    apply hresolve _ _ (by simp) (by simp)
    intro s
    simpa only [grid_dist_eq_manhattan, bag] using
      diamond_off_cross a b ha han hb hbn s.val (has s.val s.property) (hbs s.val s.property)
  have hlr : l ≠ r := by intro h; have := congrArg (fun v : Grid n => v.1.val) h; dsimp [l,r] at this; omega
  have hld : l ≠ d := by intro h; have := congrArg (fun v : Grid n => v.1.val) h; dsimp [l,d] at this; omega
  have hlu : l ≠ u := by intro h; have := congrArg (fun v : Grid n => v.1.val) h; dsimp [l,u] at this; omega
  have h := congrFun he l
  simp [pairConfig, pointConfig, hlr, hld, hlu] at h

end ShellTomography
