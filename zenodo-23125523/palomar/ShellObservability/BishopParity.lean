module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic
public import ShellObservability.BishopReflection
public import ShellObservability.BishopBoundaryCount

@[expose] public section

/-! Boundary coverage for the actual finite bishop graph. -/
namespace ShellObservability.BishopParity
open Finset

abbrev Square (N : ℕ) := Fin (N+1) × Fin (N+1)
def plus {N : ℕ} (v : Square N) : ℕ := v.1.val + v.2.val
def minus {N : ℕ} (v : Square N) : ℕ := v.1.val + (N-v.2.val)
def Adj {N : ℕ} (u v : Square N) : Prop :=
  u ≠ v ∧ (plus u = plus v ∨ minus u = minus v)
instance {N : ℕ} : DecidableRel (@Adj N) := fun _ _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

def graph (N : ℕ) : SimpleGraph (Square N) where
  Adj := Adj
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance {N : ℕ} : DecidableRel (graph N).Adj := inferInstanceAs (DecidableRel Adj)

def boundary {N : ℕ} (v : Square N) : Prop :=
  v.1.val = 0 ∨ v.2.val = 0 ∨ v.1.val = N ∨ v.2.val = N
instance {N : ℕ} (v : Square N) : Decidable (boundary v) := inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
def evenColor {N : ℕ} (v : Square N) : Prop := plus v % 2 = 0
instance {N : ℕ} (v : Square N) : Decidable (evenColor v) := inferInstanceAs (Decidable (_ = _))
def border (N : ℕ) : Finset (Square N) := univ.filter (fun v => boundary v ∧ evenColor v)

def coverage {N : ℕ} (S : Finset (Square N)) (v : Square N) : ℕ :=
  ∑ u ∈ S, ((if plus u = plus v then 1 else 0) + (if minus u = minus v then 1 else 0))
def TwoDominates {N : ℕ} (S : Finset (Square N)) : Prop :=
  ∀ v, v ∉ S → 2 ≤ (S.filter (fun u => (graph N).Adj v u)).card

theorem diagonal_intersection {N : ℕ} (u v : Square N)
    (hp : plus u = plus v) (hm : minus u = minus v) : u = v := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [plus, minus] at hp hm
  all_goals have hu := u.2.isLt; have hv := v.2.isLt; omega

theorem coverage_eq {N : ℕ} (S : Finset (Square N)) (v : Square N) :
    coverage S v = (if v ∈ S then 2 else 0) + (S.filter (fun u => (graph N).Adj v u)).card := by
  simp only [coverage, Finset.card_filter]
  have ht (u : Square N) :
      (if plus u = plus v then 1 else 0) + (if minus u = minus v then 1 else 0) =
      (if u = v then 2 else 0) + (if (graph N).Adj v u then 1 else 0) := by
    by_cases huv : u = v
    · subst u; simp [graph, Adj]
    · have hd := diagonal_intersection u v
      by_cases hp : plus u = plus v <;> by_cases hm : minus u = minus v
      all_goals simp_all [graph, Adj, eq_comm]
  simp_rw [ht]
  rw [Finset.sum_add_distrib]
  simp

theorem coverage_ge_two {N : ℕ} (S : Finset (Square N)) (hS : TwoDominates S)
    (v : Square N) : 2 ≤ coverage S v := by
  rw [coverage_eq]
  by_cases hv : v ∈ S
  · simp [hv]
  · simpa [hv] using hS v hv

/-- A diagonal meets the boundary in at most two squares. -/
theorem plus_boundary_card_le {N : ℕ} (v : Square N) :
    ((univ : Finset (Square N)).filter (fun u => boundary u ∧ plus u = plus v)).card ≤ 2 := by
  let t := plus v
  let a : Fin (N+1) := ⟨min t N, by omega⟩
  let b : Fin (N+1) := ⟨t - min t N, by
    have hv1 := v.1.isLt; have hv2 := v.2.isLt
    dsimp [t, plus]; omega⟩
  apply le_trans (Finset.card_le_card (t := {(a,b),(b,a)}) ?_)
    (Finset.card_insert_le _ _ |>.trans (by simp))
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  have hu1 := u.1.isLt; have hu2 := u.2.isLt
  have he : u.1.val + u.2.val = t := hu.2
  have ha : a.val = min t N := rfl
  have hb : b.val = t-min t N := rfl
  have hc : (u.1.val = a.val ∧ u.2.val = b.val) ∨
      (u.1.val = b.val ∧ u.2.val = a.val) := by
    rcases hu.1 with h | h | h | h <;> omega
  simp only [Finset.mem_insert, Finset.mem_singleton]
  rcases hc with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inl (Prod.ext (Fin.ext h1) (Fin.ext h2))
  · exact Or.inr (Prod.ext (Fin.ext h1) (Fin.ext h2))

def flip {N : ℕ} (v : Square N) : Square N := (v.1, ⟨N-v.2.val, by omega⟩)
@[simp] theorem flip_plus {N : ℕ} (v : Square N) : plus (flip v) = minus v := rfl
@[simp] theorem flip_minus {N : ℕ} (v : Square N) : minus (flip v) = plus v := by
  have := v.2.isLt
  simp only [minus, plus, flip]; omega
@[simp] theorem flip_flip {N : ℕ} (v : Square N) : flip (flip v) = v := by
  apply Prod.ext
  · rfl
  · apply Fin.ext; have := v.2.isLt; simp only [flip]; omega
@[simp] theorem boundary_flip {N : ℕ} (v : Square N) : boundary (flip v) ↔ boundary v := by
  have := v.2.isLt
  simp only [boundary, flip]; omega

theorem minus_boundary_card_le {N : ℕ} (v : Square N) :
    ((univ : Finset (Square N)).filter (fun u => boundary u ∧ minus u = minus v)).card ≤ 2 := by
  apply le_trans (Finset.card_le_card_of_injOn flip (t :=
    univ.filter (fun u => boundary u ∧ plus u = plus (flip v))) ?_ ?_)
    (plus_boundary_card_le (flip v))
  · intro u hu
    obtain ⟨_, hb, hm⟩ := Finset.mem_filter.mp hu
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, (boundary_flip u).mpr hb, by simpa using hm⟩
  · intro u hu w hw he
    have := congrArg flip he
    simpa using this

theorem contribution_le_four {N : ℕ} (u : Square N) :
    (∑ v ∈ border N, ((if plus u = plus v then 1 else 0) +
      (if minus u = minus v then 1 else 0))) ≤ 4 := by
  have hp : ((border N).filter (fun v => plus u = plus v)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (t := univ.filter (fun v => boundary v ∧ plus v = plus u)) ?_)
      (plus_boundary_card_le u)
    intro v hv
    simp only [Finset.mem_filter, border, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hv.1.1, hv.2.symm⟩
  have hm : ((border N).filter (fun v => minus u = minus v)).card ≤ 2 := by
    apply le_trans (Finset.card_le_card (t := univ.filter (fun v => boundary v ∧ minus v = minus u)) ?_)
      (minus_boundary_card_le u)
    intro v hv
    simp only [Finset.mem_filter, border, Finset.mem_univ, true_and] at hv ⊢
    exact ⟨hv.1.1, hv.2.symm⟩
  rw [Finset.sum_add_distrib]
  simp only [← Finset.card_filter]
  omega

theorem boundary_coverage_le {N : ℕ} (S : Finset (Square N)) :
    (∑ v ∈ border N, coverage S v) ≤ 4*S.card := by
  simp only [coverage]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ u ∈ S, 4 := Finset.sum_le_sum (fun u _ => contribution_le_four u)
    _ = _ := by simp; omega

def plusLoad {N : ℕ} (S : Finset (Square N)) (s : ℕ) : ℕ :=
  (S.filter (fun u => plus u = s)).card
def minusLoad {N : ℕ} (S : Finset (Square N)) (s : ℕ) : ℕ :=
  (S.filter (fun u => minus u = s)).card

theorem coverage_diagonals {N : ℕ} (S : Finset (Square N)) (v : Square N) :
    coverage S v = plusLoad S (plus v) + minusLoad S (minus v) := by
  simp only [coverage, plusLoad, minusLoad, Finset.card_filter, Finset.sum_add_distrib]

theorem plus_load_total {N : ℕ} (S : Finset (Square N)) :
    (∑ s ∈ range (2*N+1), plusLoad S s) = S.card := by
  simp only [plusLoad, Finset.card_filter]
  rw [Finset.sum_comm]
  have he (u : Square N) : (∑ s ∈ range (2*N+1), if plus u = s then 1 else 0) = 1 := by
    have hmem : plus u ∈ range (2*N+1) := by
      have h1 := u.1.isLt; have h2 := u.2.isLt
      simp only [Finset.mem_range, plus]; omega
    simp [hmem]
  simp_rw [he]
  simp

/-- A board-geometric lemma: equality in the boundary bound forces even mass. -/
theorem even_mass_of_small {N : ℕ} (hN : N % 2 = 1)
    (hborder : (border N).card = 2*N)
    (S : Finset (Square N)) (hcolor : ∀ u ∈ S, evenColor u)
    (hcover : ∀ v ∈ border N, 2 ≤ coverage S v) (hsmall : S.card ≤ N) :
    S.card % 2 = 0 := by
  have hlow : (∑ v ∈ border N, 2) ≤ ∑ v ∈ border N, coverage S v :=
    Finset.sum_le_sum hcover
  have hupper := boundary_coverage_le S
  have hsum : (∑ v ∈ border N, 2) = ∑ v ∈ border N, coverage S v := by
    have hc : (∑ v ∈ border N, 2) = 4*N := by simp [hborder]; omega
    omega
  have heq : ∀ v ∈ border N, coverage S v = 2 := by
    intro v hv
    exact ((Finset.sum_eq_sum_iff_of_le hcover).mp hsum v hv).symm
  rw [← plus_load_total S]
  apply BishopReflection.reflected_sum_even N (plusLoad S) hN
  · intro s hs ho
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro u hu hp
    have hc := hcolor u hu
    dsimp [evenColor] at hc
    omega
  · intro s hs he
    let a : Square N := (⟨s,by omega⟩,⟨0,by omega⟩)
    let b : Square N := (⟨N,by omega⟩,⟨N-s,by omega⟩)
    have ha : a ∈ border N := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (s=0 ∨ 0=0 ∨ s=N ∨ 0=N) ∧ (s+0)%2=0
      exact ⟨Or.inr (Or.inl rfl), by omega⟩
    have hb : b ∈ border N := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      change (N=0 ∨ N-s=0 ∨ N=N ∨ N-s=N) ∧ (N+(N-s))%2=0
      exact ⟨Or.inr (Or.inr (Or.inl rfl)), by omega⟩
    have hea := heq a ha
    have heb := heq b hb
    rw [coverage_diagonals] at hea heb
    have pa : plus a = s := by simp [plus,a]
    have pb : plus b = 2*N-s := by simp only [plus,b]; omega
    have ma : minus a = N+s := by simp [minus,a]; omega
    have mb : minus b = N+s := by simp only [minus,b]; omega
    rw [pa,ma] at hea
    rw [pb,mb] at heb
    omega

theorem color_lower_bound {N : ℕ} (hN : N % 2 = 1)
    (hborder : (border N).card = 2*N)
    (S : Finset (Square N)) (hcolor : ∀ u ∈ S, evenColor u)
    (hcover : ∀ v ∈ border N, 2 ≤ coverage S v) : N+1 ≤ S.card := by
  have hlow : (∑ v ∈ border N, 2) ≤ ∑ v ∈ border N, coverage S v :=
    Finset.sum_le_sum hcover
  have hc : (∑ v ∈ border N, 2) = 4*N := by simp [hborder]; omega
  have hupper := boundary_coverage_le S
  have hbound : N ≤ S.card := by omega
  by_contra h
  have he := even_mass_of_small hN hborder S hcolor hcover (by omega)
  omega

theorem diagonal_color {N : ℕ} (u v : Square N)
    (h : plus u = plus v ∨ minus u = minus v) : evenColor u ↔ evenColor v := by
  have hu := u.2.isLt; have hv := v.2.isLt
  simp only [evenColor, plus, minus] at *
  rcases h with h | h <;> omega

/-- Restricting to a union of bishop components preserves coverage there. -/
theorem coverage_filter {N : ℕ} (S : Finset (Square N))
    (p : Square N → Prop) [DecidablePred p]
    (hp : ∀ u v, (plus u = plus v ∨ minus u = minus v) → (p u ↔ p v))
    (v : Square N) (hv : p v) : coverage (S.filter p) v = coverage S v := by
  simp only [coverage, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hpu : p u
  · simp [hpu]
  · have hplus : plus u ≠ plus v := by
      intro he; exact hpu ((hp u v (Or.inl he)).mpr hv)
    have hminus : minus u ≠ minus v := by
      intro he; exact hpu ((hp u v (Or.inr he)).mpr hv)
    simp [hpu,hplus,hminus]

theorem flip_injective {N : ℕ} : Function.Injective (@flip N) := by
  intro u v h
  have := congrArg flip h
  simpa using this

theorem flip_color {N : ℕ} (hN : N % 2 = 1) (v : Square N) :
    evenColor (flip v) ↔ ¬ evenColor v := by
  have h := v.2.isLt
  simp only [evenColor]
  rw [flip_plus]
  simp only [minus, plus]
  omega

theorem coverage_flip {N : ℕ} (S : Finset (Square N)) (v : Square N) :
    coverage (S.image flip) v = coverage S (flip v) := by
  simp only [coverage]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro u hu
    simp only [flip_plus, flip_minus]
    exact Nat.add_comm _ _
  · intro u hu w hw he
    exact flip_injective he

/-- Concrete all-even-board lower bound, before importing the independent
boundary-cardinality arithmetic. -/
theorem two_domination_lower_of_border {N : ℕ} (hN : N % 2 = 1)
    (hborder : (border N).card = 2*N)
    (S : Finset (Square N)) (hS : TwoDominates S) : 2*(N+1) ≤ S.card := by
  let E := S.filter evenColor
  let O := S.filter (fun v => ¬evenColor v)
  have hE : N+1 ≤ E.card := by
    apply color_lower_bound hN hborder E
    · intro u hu; exact (Finset.mem_filter.mp hu).2
    · intro v hv
      have hc : evenColor v := (Finset.mem_filter.mp hv).2.2
      rw [show E = S.filter evenColor from rfl, coverage_filter S evenColor diagonal_color v hc]
      exact coverage_ge_two S hS v
  have hO : N+1 ≤ (O.image flip).card := by
    apply color_lower_bound hN hborder (O.image flip)
    · intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      exact (flip_color hN v).mpr (Finset.mem_filter.mp hv).2
    · intro v hv
      have hc : evenColor v := (Finset.mem_filter.mp hv).2.2
      have hc' : ¬evenColor (flip v) := by rw [flip_color hN]; exact not_not_intro hc
      rw [coverage_flip]
      rw [show O = S.filter (fun u => ¬evenColor u) from rfl]
      rw [coverage_filter S (fun u => ¬evenColor u)
        (fun u v h => not_congr (diagonal_color u v h)) (flip v) hc']
      exact coverage_ge_two S hS (flip v)
  have himage : (O.image flip).card = O.card := Finset.card_image_of_injective O flip_injective
  have hsum : E.card + O.card = S.card := Finset.card_filter_add_card_filter_not
    (s := S) (p := evenColor)
  omega

/-- Every two-dominating set on an even-sided bishop board has at least twice
its side length many squares. No geometric or counting premises are assumed. -/
theorem two_domination_lower {N : ℕ} (hN : N % 2 = 1)
    (S : Finset (Square N)) (hS : TwoDominates S) : 2*(N+1) ≤ S.card := by
  apply two_domination_lower_of_border hN _ S hS
  have hs : border N = (Finset.univ : Finset (Square N)).filter
      (fun v => BishopBoundaryCount.boundary v ∧ (v.1.val+v.2.val)%2=0) := by
    ext v
    simp [border, boundary, evenColor, plus, BishopBoundaryCount.boundary]
  rw [hs]
  exact BishopBoundaryCount.even_boundary_card N hN

end ShellObservability.BishopParity
