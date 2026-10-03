module

public import ShellTomography.Foundations
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Tactic

@[expose] public section

/-!
# Robustness of labelled observation blocks

Each sensor supplies one block, possibly an entire distance multiset. Hamming
distance counts corrupt sensor blocks, rather than entries inside the blocks.
The coding criteria below are generic; they are not claimed as new coding
bounds. Their role is to turn graph-specific separation bounds into guarantees
against erased or adversarial sensor reports.
-/

namespace ShellObservability

section BlockCodes

variable {X S A : Type*} [Fintype S] [DecidableEq A]

/-- Unique decoding after at most `t` arbitrarily corrupted labelled blocks,
restricted to the specified admissible configurations. -/
def CorrectsBlocks (code : X → S → A) (admissible : X → Prop) (t : ℕ) : Prop :=
  ∀ x y received, admissible x → admissible y →
    hammingDist (code x) received ≤ t → hammingDist (code y) received ≤ t → x = y

/-- Unique recovery after any set of at most `e` labelled blocks is erased. -/
def ToleratesErasures (code : X → S → A) (admissible : X → Prop) (e : ℕ) : Prop :=
  ∀ erased : Finset S, erased.card ≤ e →
    ∀ x y, admissible x → admissible y →
      (∀ s, s ∉ erased → code x s = code y s) → x = y

/-- Two words at distance at most `2t` have a common radius-`t` received word. -/
theorem exists_common_received (a b : S → A) (t : ℕ)
    (h : hammingDist a b ≤ 2 * t) :
    ∃ received, hammingDist a received ≤ t ∧ hammingDist b received ≤ t := by
  classical
  let D := Finset.univ.filter (fun s => a s ≠ b s)
  obtain ⟨F, hFD, hFcard⟩ := Finset.exists_subset_card_eq (Nat.min_le_right t D.card)
  let received : S → A := fun s => if s ∈ F then a s else b s
  have ha : hammingDist a received ≤ (D \ F).card := by
    apply Finset.card_le_card
    intro s hs
    have hs' : a s ≠ received s := (Finset.mem_filter.mp hs).2
    have hnF : s ∉ F := by
      intro hm
      exact hs' (by simp [received, hm])
    have hneq : a s ≠ b s := by simpa [received, hnF] using hs'
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩, hnF⟩
  have hb : hammingDist b received ≤ F.card := by
    apply Finset.card_le_card
    intro s hs
    have hs' : b s ≠ received s := (Finset.mem_filter.mp hs).2
    by_contra hnF
    exact hs' (by simp [received, hnF])
  have hcard : (D \ F).card = D.card - F.card := Finset.card_sdiff_of_subset hFD
  have hD : D.card ≤ 2 * t := h
  refine ⟨received, ?_, ?_⟩ <;> omega

/-- The exact block-error criterion, including its converse. -/
theorem correctsBlocks_iff (code : X → S → A) (admissible : X → Prop) (t : ℕ) :
    CorrectsBlocks code admissible t ↔
      ∀ x y, admissible x → admissible y → x ≠ y →
        2 * t < hammingDist (code x) (code y) := by
  constructor
  · intro hc x y hx hy hxy
    by_contra hd
    have hle : hammingDist (code x) (code y) ≤ 2 * t := by omega
    obtain ⟨received, hxr, hyr⟩ := exists_common_received (code x) (code y) t hle
    exact hxy (hc x y received hx hy hxr hyr)
  · intro hd x y received hx hy hxr hyr
    by_contra hxy
    have hsep := hd x y hx hy hxy
    have htri := hammingDist_triangle_right (code x) (code y) received
    omega

/-- The exact block-erasure criterion, including its converse. -/
theorem toleratesErasures_iff (code : X → S → A) (admissible : X → Prop) (e : ℕ) :
    ToleratesErasures code admissible e ↔
      ∀ x y, admissible x → admissible y → x ≠ y →
        e < hammingDist (code x) (code y) := by
  classical
  constructor
  · intro he x y hx hy hxy
    by_contra hd
    let D := Finset.univ.filter (fun s => code x s ≠ code y s)
    have hD : D.card ≤ e := by change hammingDist (code x) (code y) ≤ e; omega
    apply hxy (he D hD x y hx hy ?_)
    intro s hs
    by_contra hneq
    exact hs (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩)
  · intro hd erased herased x y hx hy hagree
    by_contra hxy
    have hsep := hd x y hx hy hxy
    have hle : hammingDist (code x) (code y) ≤ erased.card := by
      apply Finset.card_le_card
      intro s hs
      have hneq := (Finset.mem_filter.mp hs).2
      by_contra hnot
      exact hneq (hagree s hnot)
    omega

end BlockCodes

end ShellObservability

namespace ShellObservability

open ShellTomography

section ShellBlocks

variable {V S R : Type*} [Fintype V] [Fintype S] [DecidableEq R]

/-- Number of labelled sensors that detect an integer occupancy change. -/
noncomputable def tradeWeight (δ : S → V → R) (z : SignedConfiguration V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s => ∃ r, shellZ δ z s r ≠ 0)).card

omit [Fintype S] in
/-- A sensor's whole distance bag changes exactly when some signed shell sum
is nonzero. -/
theorem bag_ne_iff_detects (δ : S → V → R) (x y : Configuration V) (s : S) :
    bag δ x s ≠ bag δ y s ↔ ∃ r, shellZ δ (difference x y) s r ≠ 0 := by
  classical
  have heq : bag δ x s = bag δ y s ↔ ∀ r, shellZ δ (difference x y) s r = 0 := by
    constructor
    · intro hb r
      have hc := congrArg (Multiset.count r) hb
      rw [count_bag, count_bag] at hc
      rw [shell_difference, hc, sub_self]
    · intro hs
      apply Multiset.ext.mpr
      intro r
      rw [count_bag, count_bag]
      have hz := hs r
      rw [shell_difference] at hz
      omega
  simpa only [not_forall] using not_congr heq

/-- Sensor-block Hamming distance is exactly the support size of the signed
shell response of the configuration difference. -/
theorem bag_hamming_eq_tradeWeight (δ : S → V → R) (x y : Configuration V) :
    hammingDist (bag δ x) (bag δ y) = tradeWeight δ (difference x y) := by
  classical
  unfold hammingDist tradeWeight
  congr 1
  apply Finset.ext
  intro s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, bag_ne_iff_detects]

/-- Graph-specific trade separation gives the exact adversarial report criterion. -/
theorem correctsBags_iff_tradeWeight (δ : S → V → R) (h t : ℕ) :
    CorrectsBlocks (bag δ) (fun x => mass x ≤ h) t ↔
      ∀ x y, mass x ≤ h → mass y ≤ h → x ≠ y →
        2 * t < tradeWeight δ (difference x y) := by
  rw [correctsBlocks_iff]
  simp only [bag_hamming_eq_tradeWeight]

/-- Graph-specific trade separation gives the exact report-erasure criterion. -/
theorem erasureBags_iff_tradeWeight (δ : S → V → R) (h e : ℕ) :
    ToleratesErasures (bag δ) (fun x => mass x ≤ h) e ↔
      ∀ x y, mass x ≤ h → mass y ≤ h → x ≠ y →
        e < tradeWeight δ (difference x y) := by
  rw [toleratesErasures_iff]
  simp only [bag_hamming_eq_tradeWeight]

end ShellBlocks

end ShellObservability
