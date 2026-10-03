module

public import Mathlib

@[expose] public section

/-!
# Ordered star sensing and balanced interval cuts

Interior line coordinates are numbered from zero. The graph consists of `q`
three-leaf row-centered stars followed, in the opposite order, by `q`
three-leaf column-centered stars. Reversing the second family prevents a
proper pair of equally long intervals from containing whole components only.
-/
namespace ShellObservability.OrderedStars

open Finset

/-- The characteristic function of the interval `[a,a+k)`. -/
def bit (a k x : ℕ) : ℕ := if a ≤ x ∧ x < a + k then 1 else 0

@[simp] theorem bit_eq_one {a k x : ℕ} : bit a k x = 1 ↔ a ≤ x ∧ x < a + k := by
  simp [bit]

@[simp] theorem bit_le_one (a k x : ℕ) : bit a k x ≤ 1 := by
  unfold bit; split_ifs <;> omega

/-- A sensor contributes one precisely when its two line memberships differ. -/
def mismatch (a b : ℕ) : ℕ := if a = b then 0 else 1

@[simp] theorem mismatch_eq_zero {a b : ℕ} : mismatch a b = 0 ↔ a = b := by
  simp [mismatch]

/-- Actual edge-cut size of the two indexed families of three-leaf stars. -/
def cut (q a b k : ℕ) : ℕ :=
  (∑ i ∈ range q, ∑ t ∈ range 3, mismatch (bit a k i) (bit b k (3*i+t))) +
  (∑ j ∈ range q, ∑ t ∈ range 3,
    mismatch (bit a k (q+3*(q-1-j)+t)) (bit b k (3*q+j)))

theorem sum_triples {M : Type*} [AddCommMonoid M] (f : ℕ → M) (q : ℕ) :
    (∑ i ∈ range q, ∑ t ∈ range 3, f (3*i+t)) = ∑ x ∈ range (3*q), f x := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [sum_range_succ, ih]
    rw [show 3*(q+1) = 3*q+3 by omega, sum_range_add]

theorem sum_triples_reverse {M : Type*} [AddCommMonoid M] (f : ℕ → M) (q : ℕ) :
    (∑ i ∈ range q, ∑ t ∈ range 3, f (3*(q-1-i)+t)) =
      ∑ x ∈ range (3*q), f x := by
  rw [sum_range_reflect (fun i => ∑ t ∈ range 3, f (3*i+t)), sum_triples]

theorem sum_bit (a k N : ℕ) (h : a+k ≤ N) :
    (∑ x ∈ range N, bit a k x) = k := by
  simp only [bit, sum_boole]
  have heq : (range N).filter (fun x => a ≤ x ∧ x < a+k) = Ico a (a+k) := by
    ext x
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [heq, Nat.card_Ico]
  simp

/-- No crossing edge means each star is wholly selected or wholly unselected. -/
theorem cut_zero_membership {q a b k : ℕ} (h : cut q a b k = 0) :
    (∀ i < q, ∀ t < 3, bit a k i = bit b k (3*i+t)) ∧
    (∀ j < q, ∀ t < 3,
      bit a k (q+3*(q-1-j)+t) = bit b k (3*q+j)) := by
  unfold cut at h
  have hA := (Nat.add_eq_zero_iff.mp h).1
  have hB := (Nat.add_eq_zero_iff.mp h).2
  constructor
  · intro i hi t ht
    have hh := sum_eq_zero_iff.mp (sum_eq_zero_iff.mp hA i (mem_range.mpr hi)) t
      (mem_range.mpr ht)
    exact mismatch_eq_zero.mp hh
  · intro j hj t ht
    have hh := sum_eq_zero_iff.mp (sum_eq_zero_iff.mp hB j (mem_range.mpr hj)) t
      (mem_range.mpr ht)
    exact mismatch_eq_zero.mp hh

/-- Cardinalities of the selected row and column lines in a zero cut. -/
theorem zero_cut_counts {q a b k : ℕ} (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q)
    (hz : cut q a b k = 0) :
    k = (∑ i ∈ range q, bit a k i) + 3 * (∑ j ∈ range q, bit b k (3*q+j)) ∧
    k = 3 * (∑ i ∈ range q, bit a k i) + (∑ j ∈ range q, bit b k (3*q+j)) := by
  obtain ⟨hA, hB⟩ := cut_zero_membership hz
  have hr := sum_bit a k (4*q) ha
  have hc := sum_bit b k (4*q) hb
  have hrr : (∑ x ∈ range (3*q), bit a k (q+x)) =
      3 * (∑ j ∈ range q, bit b k (3*q+j)) := by
    rw [← sum_triples_reverse]
    have hh : (∑ i ∈ range q, ∑ t ∈ range 3, bit a k (q+(3*(q-1-i)+t))) =
        ∑ i ∈ range q, ∑ t ∈ range 3, bit b k (3*q+i) := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro t ht
      simpa [Nat.add_assoc] using hB i (mem_range.mp hi) t (mem_range.mp ht)
    rw [hh]
    simp [mul_sum]
  have hcc : (∑ x ∈ range (3*q), bit b k x) = 3 * (∑ i ∈ range q, bit a k i) := by
    rw [← sum_triples]
    have hh : (∑ i ∈ range q, ∑ t ∈ range 3, bit b k (3*i+t)) =
        ∑ i ∈ range q, ∑ t ∈ range 3, bit a k i := by
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro t ht
      exact (hA i (mem_range.mp hi) t (mem_range.mp ht)).symm
    rw [hh]
    simp [mul_sum]
  constructor
  · rw [show 4*q = q+3*q by omega, sum_range_add] at hr
    rw [hrr] at hr
    exact hr.symm
  · rw [show 4*q = 3*q+q by omega, sum_range_add] at hc
    rw [hcc] at hc
    exact hc.symm

/-- A nonempty zero balanced interval cut must contain every interior line. -/
theorem zero_cut_full {q a b k : ℕ} (hk : 0 < k)
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) (hz : cut q a b k = 0) :
    k = 4*q := by
  obtain ⟨hA, hB⟩ := cut_zero_membership hz
  obtain ⟨hr, hc⟩ := zero_cut_counts ha hb hz
  have hAB : (∑ i ∈ range q, bit a k i) = (∑ j ∈ range q, bit b k (3*q+j)) := by
    omega
  have hposA : 0 < ∑ i ∈ range q, bit a k i := by omega
  have hposB : 0 < ∑ j ∈ range q, bit b k (3*q+j) := by omega
  obtain ⟨i, hi, hip⟩ := sum_pos_iff.mp hposA
  obtain ⟨j, hj, hjp⟩ := sum_pos_iff.mp hposB
  have hiq := mem_range.mp hi
  have hjq := mem_range.mp hj
  have hiOne : bit a k i = 1 := by have := bit_le_one a k i; omega
  have hjOne : bit b k (3*q+j) = 1 := by have := bit_le_one b k (3*q+j); omega
  have hiInt := bit_eq_one.mp hiOne
  have hjInt := bit_eq_one.mp hjOne
  have hiCol : bit b k (3*i) = 1 := by simpa using (hA i hiq 0 (by omega)).symm.trans hiOne
  have hiColInt := bit_eq_one.mp hiCol
  have hjRow : bit a k (q+3*(q-1-j)) = 1 := by simpa using (hB j hjq 0 (by omega)).trans hjOne
  have hjRowInt := bit_eq_one.mp hjRow
  have hfullB : ∀ l < q, bit b k (3*q+l) = 1 := by
    intro l hlq
    by_cases hlj : l ≤ j
    · apply bit_eq_one.mpr
      constructor <;> omega
    · have hlRow : bit a k (q+3*(q-1-l)) = 1 := by
        apply bit_eq_one.mpr
        constructor <;> omega
      simpa using (hB l hlq 0 (by omega)).symm.trans hlRow
  have hBcount : (∑ j ∈ range q, bit b k (3*q+j)) = q := by
    calc
      _ = ∑ _j ∈ range q, 1 := sum_congr rfl (fun j hj => hfullB j (mem_range.mp hj))
      _ = q := by simp
  omega

theorem mismatch_identity {u v : ℕ} (hu : u ≤ 1) (hv : v ≤ 1) :
    mismatch u v + 2*(u*v) = u+v := by
  interval_cases u <;> interval_cases v <;> decide

theorem sum_mismatch_identity (f g : ℕ → ℕ → ℕ) (q : ℕ)
    (hf : ∀ i t, f i t ≤ 1) (hg : ∀ i t, g i t ≤ 1) :
    (∑ i ∈ range q, ∑ t ∈ range 3, mismatch (f i t) (g i t)) +
      2*(∑ i ∈ range q, ∑ t ∈ range 3, f i t*g i t) =
    (∑ i ∈ range q, ∑ t ∈ range 3, f i t) +
      (∑ i ∈ range q, ∑ t ∈ range 3, g i t) := by
  have hh : (∑ i ∈ range q, ∑ t ∈ range 3,
      (mismatch (f i t) (g i t) + 2*(f i t*g i t))) =
      ∑ i ∈ range q, ∑ t ∈ range 3, (f i t+g i t) := by
    apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro t ht
    exact mismatch_identity (hf i t) (hg i t)
  simpa only [sum_add_distrib, mul_sum] using hh

/-- Every balanced interval cut is even, because every line has odd degree. -/
theorem cut_even {q a b k : ℕ} (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) :
    cut q a b k % 2 = 0 := by
  have hA := sum_mismatch_identity (fun i _t => bit a k i)
    (fun i t => bit b k (3*i+t)) q
    (fun i _t => bit_le_one a k i) (fun i t => bit_le_one b k (3*i+t))
  have hB := sum_mismatch_identity (fun j t => bit a k (q+3*(q-1-j)+t))
    (fun j _t => bit b k (3*q+j)) q
    (fun j t => bit_le_one a k (q+3*(q-1-j)+t))
    (fun j _t => bit_le_one b k (3*q+j))
  have hr := sum_bit a k (4*q) ha
  have hc := sum_bit b k (4*q) hb
  rw [show 4*q = q+3*q by omega, sum_range_add] at hr
  rw [show 4*q = 3*q+q by omega, sum_range_add] at hc
  have hAA : (∑ i ∈ range q, ∑ _t ∈ range 3, bit a k i) =
      3*(∑ i ∈ range q, bit a k i) := by simp [mul_sum]
  have hBB : (∑ j ∈ range q, ∑ _t ∈ range 3, bit b k (3*q+j)) =
      3*(∑ j ∈ range q, bit b k (3*q+j)) := by simp [mul_sum]
  have hBA : (∑ j ∈ range q, ∑ t ∈ range 3, bit a k (q+3*(q-1-j)+t)) =
      ∑ x ∈ range (3*q), bit a k (q+x) := by
    simpa [Nat.add_assoc] using sum_triples_reverse (fun x => bit a k (q+x)) q
  rw [hAA, sum_triples] at hA
  rw [hBA, hBB] at hB
  unfold cut
  omega

/-- The concrete ordered-star construction detects every nonempty proper pair
of equally long interior intervals at least twice. -/
theorem proper_interval_cut_ge_two {q a b k : ℕ} (hk : 0 < k)
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) (hproper : k < 4*q) :
    2 ≤ cut q a b k := by
  have he := cut_even ha hb
  have hn : cut q a b k ≠ 0 := by
    intro hz
    have := zero_cut_full hk ha hb hz
    omega
  omega

/-- The coordinates of the distinct row-centered sensors. -/
def aPoint (p : ℕ × ℕ) : ℕ × ℕ := (p.1,3*p.1+p.2)

/-- The coordinates of the distinct column-centered sensors. -/
def bPoint (q : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (q+3*(q-1-p.1)+p.2,3*q+p.1)

def aEdges (q : ℕ) : Finset (ℕ × ℕ) := ((range q) ×ˢ (range 3)).image aPoint

def bEdges (q : ℕ) : Finset (ℕ × ℕ) := ((range q) ×ˢ (range 3)).image (bPoint q)

/-- The actual finite set of interior sensors, with no repetitions. -/
def core (q : ℕ) : Finset (ℕ × ℕ) := aEdges q ∪ bEdges q

theorem aPoint_injective : Function.Injective aPoint := by
  intro ⟨i,t⟩ ⟨j,u⟩ h
  simp only [aPoint, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem bPoint_injective (q : ℕ) : Function.Injective (bPoint q) := by
  intro ⟨i,t⟩ ⟨j,u⟩ h
  simp only [bPoint, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem edges_disjoint (q : ℕ) : Disjoint (aEdges q) (bEdges q) := by
  apply disjoint_left.mpr
  intro p hpA hpB
  obtain ⟨⟨i,t⟩, hi, heA⟩ := mem_image.mp hpA
  obtain ⟨⟨j,u⟩, hj, heB⟩ := mem_image.mp hpB
  have hiq : i < q := mem_range.mp (mem_product.mp hi).1
  have he := congrArg Prod.fst (heA.trans heB.symm)
  simp only [aPoint, bPoint] at he
  omega

theorem core_card (q : ℕ) : (core q).card = 6*q := by
  rw [core, card_union_of_disjoint (edges_disjoint q)]
  rw [aEdges, bEdges, card_image_of_injective _ aPoint_injective,
    card_image_of_injective _ (bPoint_injective q)]
  simp [card_product]
  omega

theorem core_bounds {q : ℕ} {p : ℕ × ℕ} (hp : p ∈ core q) :
    p.1 < 4*q ∧ p.2 < 4*q := by
  rcases mem_union.mp hp with hp | hp
  · obtain ⟨⟨i,t⟩, hi, rfl⟩ := mem_image.mp hp
    obtain ⟨hiq, ht⟩ := mem_product.mp hi
    have hiq := mem_range.mp hiq
    have ht := mem_range.mp ht
    simp only [aPoint]
    constructor <;> omega
  · obtain ⟨⟨j,t⟩, hj, rfl⟩ := mem_image.mp hp
    obtain ⟨hjq, ht⟩ := mem_product.mp hj
    have hjq := mem_range.mp hjq
    have ht := mem_range.mp ht
    simp only [bPoint]
    constructor <;> omega

/-- The indexed sum defining `cut` is exactly the number of distinct sensors
in the symmetric difference of the two line intervals. -/
theorem cut_eq_card (q a b k : ℕ) :
    cut q a b k = ((core q).filter (fun p => bit a k p.1 ≠ bit b k p.2)).card := by
  have hsum := sum_boole (R := ℕ) (fun p : ℕ × ℕ => bit a k p.1 ≠ bit b k p.2) (core q)
  simp only [Nat.cast_id] at hsum
  rw [← hsum]
  unfold core
  rw [sum_union (edges_disjoint q)]
  unfold aEdges bEdges
  rw [sum_image (fun x _ y _ h => aPoint_injective h),
    sum_image (fun x _ y _ h => bPoint_injective q h)]
  rw [sum_product, sum_product]
  unfold cut mismatch aPoint bPoint
  congr 1 <;> apply sum_congr rfl <;> intro i hi <;> apply sum_congr rfl <;> intro t ht <;>
    split_ifs <;> simp_all

/-- The all-order proper-interval guarantee for the actual sensor set. -/
theorem core_proper_interval_cut_ge_two {q a b k : ℕ} (hk : 0 < k)
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) (hproper : k < 4*q) :
    2 ≤ ((core q).filter (fun p => bit a k p.1 ≠ bit b k p.2)).card := by
  rw [← cut_eq_card]
  exact proper_interval_cut_ge_two hk ha hb hproper

def shift (p : ℕ × ℕ) : ℕ × ℕ := (p.1+1,p.2+1)

def boundary (q : ℕ) : Finset (ℕ × ℕ) :=
  {(0,0),(0,4*q+1),(4*q+1,0),(4*q+1,4*q+1),(1,0),(4*q,0)}

/-- The placement on the `(4q+2)` by `(4q+2)` grid. -/
def placement (q : ℕ) : Finset (ℕ × ℕ) := (core q).image shift ∪ boundary q

theorem shift_injective : Function.Injective shift := by
  intro ⟨x,y⟩ ⟨u,v⟩ h
  simp only [shift, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

@[simp] theorem bit_shift (a k x : ℕ) : bit (a+1) k (x+1) = bit a k x := by
  unfold bit
  split_ifs <;> omega

theorem boundary_card {q : ℕ} (hq : 0 < q) : (boundary q).card = 6 := by
  have h0 : 4*q ≠ 0 := by omega
  have h1 : 4*q ≠ 1 := by omega
  simp [boundary, h0, Ne.symm h0, Ne.symm h1]

theorem placement_parts_disjoint (q : ℕ) : Disjoint ((core q).image shift) (boundary q) := by
  apply disjoint_left.mpr
  intro p hp hb
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hp
  obtain ⟨hx,hy⟩ := core_bounds hxy
  simp only [boundary, mem_insert, mem_singleton, Prod.mk.injEq, shift] at hb
  rcases hb with h | h | h | h | h | h <;> omega

/-- Exact sensor count, with repetitions explicitly excluded. -/
theorem placement_card {q : ℕ} (hq : 0 < q) : (placement q).card = 6*q+6 := by
  rw [placement, card_union_of_disjoint (placement_parts_disjoint q),
    card_image_of_injective _ shift_injective, core_card, boundary_card hq]

theorem placement_bounds {q : ℕ} {p : ℕ × ℕ} (hp : p ∈ placement q) :
    p.1 < 4*q+2 ∧ p.2 < 4*q+2 := by
  rcases mem_union.mp hp with hc | hb
  · obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hc
    obtain ⟨hx,hy⟩ := core_bounds hxy
    simp only [shift]
    constructor <;> omega
  · simp only [boundary, mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega

/-- The full concrete placement meets every equal-length interior interval
symmetric difference at least twice, including the full interior intervals. -/
theorem placement_interval_cut_ge_two {q a b k : ℕ} (hq : 0 < q) (hk : 0 < k)
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) :
    2 ≤ ((placement q).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  by_cases hproper : k < 4*q
  · have hbase := core_proper_interval_cut_ge_two hk ha hb hproper
    have himage : (((core q).filter (fun p => bit a k p.1 ≠ bit b k p.2)).image shift).card =
        ((core q).filter (fun p => bit a k p.1 ≠ bit b k p.2)).card :=
      card_image_of_injective _ shift_injective
    rw [← himage] at hbase
    apply le_trans hbase (card_le_card ?_)
    intro p hp
    obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hp
    obtain ⟨hm, hd⟩ := mem_filter.mp hxy
    apply mem_filter.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨(x,y),hm,rfl⟩)
    · simpa [shift] using hd
  · have hkfull : k = 4*q := by omega
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst k; subst a; subst b
    have hpair : ({(1,0),(4*q,0)} : Finset (ℕ × ℕ)).card = 2 := by
      have hne : (1,0) ≠ (4*q,0) := by intro hh; have := congrArg Prod.fst hh; simp only at this; omega
      simp [hne]
    rw [← hpair]
    apply card_le_card
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl
    · apply mem_filter.mpr
      constructor
      · apply mem_union_right
        simp [boundary]
      · simp [bit]; omega
    · apply mem_filter.mpr
      constructor
      · apply mem_union_right
        simp [boundary]
      · simp [bit]; omega

/-! ## Replacing one star edge by two boundary incidences

The replacement preserves every proper interval-cut lower bound and supplies
exactly two detectors to the full cut. It saves one sensor compared with adding
two anchors without removing an edge.
-/

def splitBoundary (q : ℕ) : Finset (ℕ × ℕ) :=
  {(0,0),(0,4*q+1),(4*q+1,0),(4*q+1,4*q+1),(1,0),(0,1)}

/-- The improved placement: split the core edge `(0,0)` into two boundary
incidences, and retain all four corners. -/
def splitPlacement (q : ℕ) : Finset (ℕ × ℕ) :=
  ((core q).erase (0,0)).image shift ∪ splitBoundary q

theorem zero_mem_core {q : ℕ} (hq : 0 < q) : (0,0) ∈ core q := by
  apply mem_union_left
  apply mem_image.mpr
  refine ⟨(0,0), ?_, rfl⟩
  simp [hq]

theorem splitBoundary_card {q : ℕ} (hq : 0 < q) : (splitBoundary q).card = 6 := by
  unfold splitBoundary
  repeat rw [card_insert_of_notMem]
  all_goals simp only [card_singleton, mem_insert, mem_singleton, Prod.mk.injEq]
  all_goals omega

theorem splitPlacement_parts_disjoint (q : ℕ) :
    Disjoint (((core q).erase (0,0)).image shift) (splitBoundary q) := by
  apply disjoint_left.mpr
  intro p hp hb
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hp
  obtain ⟨hx,hy⟩ := core_bounds (mem_of_mem_erase hxy)
  simp only [splitBoundary, mem_insert, mem_singleton, Prod.mk.injEq, shift] at hb
  rcases hb with h | h | h | h | h | h <;> omega

/-- The improved placement uses exactly `6q+5` distinct sensors. -/
theorem splitPlacement_card {q : ℕ} (hq : 0 < q) :
    (splitPlacement q).card = 6*q+5 := by
  rw [splitPlacement, card_union_of_disjoint (splitPlacement_parts_disjoint q),
    card_image_of_injective _ shift_injective, card_erase_of_mem (zero_mem_core hq),
    core_card, splitBoundary_card hq]
  omega

theorem splitPlacement_bounds {q : ℕ} {p : ℕ × ℕ} (hp : p ∈ splitPlacement q) :
    p.1 < 4*q+2 ∧ p.2 < 4*q+2 := by
  rcases mem_union.mp hp with hc | hb
  · obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hc
    obtain ⟨hx,hy⟩ := core_bounds (mem_of_mem_erase hxy)
    simp only [shift]
    constructor <;> omega
  · simp only [splitBoundary, mem_insert, mem_singleton] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega

/-- Route a detector on the split edge to the appropriate boundary endpoint. -/
def reroute (a k : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  if p = (0,0) then (if bit a k 0 = 1 then (1,0) else (0,1)) else shift p

theorem reroute_injective (a k : ℕ) : Function.Injective (reroute a k) := by
  intro x y h
  by_cases hx : x = (0,0) <;> by_cases hy : y = (0,0)
  · exact hx.trans hy.symm
  · subst x
    simp [reroute, hy] at h
    split_ifs at h
    · have hh := congrArg Prod.snd h
      simp only [shift] at hh
      omega
    · have hh := congrArg Prod.fst h
      simp only [shift] at hh
      omega
  · subst y
    simp [reroute, hx] at h
    split_ifs at h
    · have hh := congrArg Prod.snd h
      simp only [shift] at hh
      omega
    · have hh := congrArg Prod.fst h
      simp only [shift] at hh
      omega
  · simp only [reroute, if_neg hx, if_neg hy] at h
    exact shift_injective h

/-- Splitting the edge never decreases an interval detector count. -/
theorem core_cut_le_splitPlacement_cut (q a b k : ℕ) :
    ((core q).filter (fun p => bit a k p.1 ≠ bit b k p.2)).card ≤
      ((splitPlacement q).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  rw [← card_image_of_injective _ (reroute_injective a k)]
  apply card_le_card
  intro p hp
  obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hp
  obtain ⟨hc, hd⟩ := mem_filter.mp hxy
  by_cases hz : (x,y) = (0,0)
  · have hx : x = 0 := congrArg Prod.fst hz
    have hy : y = 0 := congrArg Prod.snd hz
    subst x; subst y
    simp only [reroute, if_true]
    dsimp only at hd
    by_cases hbit : bit a k 0 = 1
    · rw [if_pos hbit]
      apply mem_filter.mpr
      constructor
      · exact mem_union_right _ (by simp [splitBoundary])
      · change bit (a+1) k (0+1) ≠ bit (b+1) k 0
        rw [bit_shift, hbit]
        simp [bit]
    · rw [if_neg hbit]
      have hzero : bit a k 0 = 0 := by have := bit_le_one a k 0; omega
      have hone : bit b k 0 = 1 := by have := bit_le_one b k 0; omega
      apply mem_filter.mpr
      constructor
      · exact mem_union_right _ (by simp [splitBoundary])
      · change bit (a+1) k 0 ≠ bit (b+1) k (0+1)
        rw [bit_shift, hone]
        simp [bit]
  · simp only [reroute, if_neg hz]
    apply mem_filter.mpr
    constructor
    · exact mem_union_left _ (mem_image.mpr ⟨(x,y),mem_erase.mpr ⟨hz,hc⟩,rfl⟩)
    · simpa [shift] using hd

/-- Every nonempty balanced interior interval cut has at least two sensors
in the improved, concrete `6q+5` placement. -/
theorem splitPlacement_interval_cut_ge_two {q a b k : ℕ} (hq : 0 < q) (hk : 0 < k)
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) :
    2 ≤ ((splitPlacement q).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  by_cases hproper : k < 4*q
  · exact le_trans (core_proper_interval_cut_ge_two hk ha hb hproper)
      (core_cut_le_splitPlacement_cut q a b k)
  · have hkfull : k = 4*q := by omega
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    subst k; subst a; subst b
    have hpair : ({(1,0),(0,1)} : Finset (ℕ × ℕ)).card = 2 := by decide
    rw [← hpair]
    apply card_le_card
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> apply mem_filter.mpr
    · constructor
      · exact mem_union_right _ (by simp [splitBoundary])
      · simp [bit]; omega
    · constructor
      · exact mem_union_right _ (by simp [splitBoundary])
      · simp [bit]; omega

@[simp] theorem splitPlacement_corner00 (q : ℕ) : (0,0) ∈ splitPlacement q := by
  simp [splitPlacement, splitBoundary]
@[simp] theorem splitPlacement_corner0N (q : ℕ) : (0,4*q+1) ∈ splitPlacement q := by
  simp [splitPlacement, splitBoundary]
@[simp] theorem splitPlacement_cornerN0 (q : ℕ) : (4*q+1,0) ∈ splitPlacement q := by
  simp [splitPlacement, splitBoundary]
@[simp] theorem splitPlacement_cornerNN (q : ℕ) : (4*q+1,4*q+1) ∈ splitPlacement q := by
  simp [splitPlacement, splitBoundary]

/-! ## Padding to every grid order -/

def padBoundary (q r : ℕ) : Finset (ℕ × ℕ) :=
  {(0,0),(0,4*q+r+1),(4*q+r+1,0),(4*q+r+1,4*q+r+1),(1,0),(0,1)}

def extra (q r : ℕ) : Finset (ℕ × ℕ) :=
  (range r).image (fun i => (4*q+i+1,0)) ∪
  (range r).image (fun i => (4*q+i+1,4*q+r+1)) ∪
  (range r).image (fun i => (0,4*q+i+1)) ∪
  (range r).image (fun i => (4*q+r+1,4*q+i+1))

/-- Keep the split-edge endpoints fixed while extending the outer boundary and
putting two boundary sensors on each additional row and column. -/
def paddedPlacement (q r : ℕ) : Finset (ℕ × ℕ) :=
  ((core q).erase (0,0)).image shift ∪ padBoundary q r ∪ extra q r

theorem padBoundary_card_le (q r : ℕ) : (padBoundary q r).card ≤ 6 := by
  unfold padBoundary
  have h := card_insert_le (0,0)
    ({(0,4*q+r+1),(4*q+r+1,0),(4*q+r+1,4*q+r+1),(1,0),(0,1)} : Finset (ℕ × ℕ))
  repeat first | apply le_trans (card_insert_le _ _)
               | apply Nat.succ_le_succ
  simp

theorem extra_card_le (q r : ℕ) : (extra q r).card ≤ 4*r := by
  unfold extra
  have h1 := card_union_le
    ((range r).image (fun i => (4*q+i+1,0)))
    ((range r).image (fun i => (4*q+i+1,4*q+r+1)))
  have h2 := card_union_le
    ((range r).image (fun i => (4*q+i+1,0)) ∪
      (range r).image (fun i => (4*q+i+1,4*q+r+1)))
    ((range r).image (fun i => (0,4*q+i+1)))
  have h3 := card_union_le
    ((range r).image (fun i => (4*q+i+1,0)) ∪
      (range r).image (fun i => (4*q+i+1,4*q+r+1)) ∪
      (range r).image (fun i => (0,4*q+i+1)))
    ((range r).image (fun i => (4*q+r+1,4*q+i+1)))
  have hA := card_image_le (s := range r) (f := fun i => (4*q+i+1,0))
  have hB := card_image_le (s := range r) (f := fun i => (4*q+i+1,4*q+r+1))
  have hC := card_image_le (s := range r) (f := fun i => (0,4*q+i+1))
  have hD := card_image_le (s := range r) (f := fun i => (4*q+r+1,4*q+i+1))
  simp only [card_range] at hA hB hC hD
  omega

/-- Uniform sensor budget; taking q=m/4 and r=m%4 gives bounded overhead. -/
theorem paddedPlacement_card_le {q r : ℕ} (hq : 0 < q) :
    (paddedPlacement q r).card ≤ 6*q+5+4*r := by
  have h1 := card_union_le (((core q).erase (0,0)).image shift) (padBoundary q r)
  have h2 := card_union_le
    (((core q).erase (0,0)).image shift ∪ padBoundary q r) (extra q r)
  have hc : (((core q).erase (0,0)).image shift).card = 6*q-1 := by
    rw [card_image_of_injective _ shift_injective, card_erase_of_mem (zero_mem_core hq), core_card]
  have hb := padBoundary_card_le q r
  have he := extra_card_le q r
  unfold paddedPlacement
  omega

@[simp] theorem bit_at_zero (a k : ℕ) : bit (a+1) k 0 = 0 := by simp [bit]

theorem bit_above {a k m : ℕ} (h : a+k ≤ m) : bit (a+1) k (m+1) = 0 := by
  unfold bit
  split_ifs <;> omega

theorem bit_at_last {a k : ℕ} (hk : 0 < k) : bit (a+1) k (a+k) = 1 := by
  apply bit_eq_one.mpr
  constructor <;> omega

/-- Detectors for intervals in the original prefix survive moving the corners. -/
theorem split_cut_le_padded_cut {q r a b k : ℕ}
    (ha : a+k ≤ 4*q) (hb : b+k ≤ 4*q) :
    ((splitPlacement q).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card ≤
      ((paddedPlacement q r).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  apply card_le_card
  intro p hp
  obtain ⟨hs,hd⟩ := mem_filter.mp hp
  apply mem_filter.mpr
  refine ⟨?_,hd⟩
  rcases mem_union.mp hs with hc | hh
  · exact mem_union_left _ (mem_union_left _ hc)
  · simp only [splitBoundary, mem_insert, mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl
    · simp at hd
    · exact False.elim (hd (by simp only [bit_at_zero, bit_above hb]))
    · exact False.elim (hd (by simp only [bit_at_zero, bit_above ha]))
    · exact False.elim (hd (by simp only [bit_above ha, bit_above hb]))
    · exact mem_union_left _ (mem_union_right _ (by simp [padBoundary]))
    · exact mem_union_left _ (mem_union_right _ (by simp [padBoundary]))

theorem extra_row_mem {q r x : ℕ} (hlo : 4*q < x) (hhi : x ≤ 4*q+r) :
    (x,0) ∈ extra q r ∧ (x,4*q+r+1) ∈ extra q r := by
  have hi : x-(4*q+1) < r := by omega
  have heq : 4*q+(x-(4*q+1))+1 = x := by omega
  have hL : (x,0) ∈ (range r).image (fun i => (4*q+i+1,0)) := by
    exact mem_image.mpr ⟨x-(4*q+1),mem_range.mpr hi,by simp [heq]⟩
  have hR : (x,4*q+r+1) ∈ (range r).image (fun i => (4*q+i+1,4*q+r+1)) := by
    exact mem_image.mpr ⟨x-(4*q+1),mem_range.mpr hi,by simp [heq]⟩
  constructor
  · exact mem_union_left _ (mem_union_left _ (mem_union_left _ hL))
  · exact mem_union_left _ (mem_union_left _ (mem_union_right _ hR))

theorem extra_col_mem {q r x : ℕ} (hlo : 4*q < x) (hhi : x ≤ 4*q+r) :
    (0,x) ∈ extra q r ∧ (4*q+r+1,x) ∈ extra q r := by
  have hi : x-(4*q+1) < r := by omega
  have heq : 4*q+(x-(4*q+1))+1 = x := by omega
  have hT : (0,x) ∈ (range r).image (fun i => (0,4*q+i+1)) := by
    exact mem_image.mpr ⟨x-(4*q+1),mem_range.mpr hi,by simp [heq]⟩
  have hB : (4*q+r+1,x) ∈ (range r).image (fun i => (4*q+r+1,4*q+i+1)) := by
    exact mem_image.mpr ⟨x-(4*q+1),mem_range.mpr hi,by simp [heq]⟩
  constructor
  · exact mem_union_left _ (mem_union_right _ hT)
  · exact mem_union_right _ hB

/-- The padding construction retains every two-detector interval guarantee. -/
theorem paddedPlacement_interval_cut_ge_two {q r a b k : ℕ}
    (hq : 0 < q) (hk : 0 < k) (ha : a+k ≤ 4*q+r) (hb : b+k ≤ 4*q+r) :
    2 ≤ ((paddedPlacement q r).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  by_cases har : a+k ≤ 4*q
  · by_cases hbr : b+k ≤ 4*q
    · exact le_trans (splitPlacement_interval_cut_ge_two hq hk har hbr)
        (split_cut_le_padded_cut har hbr)
    · obtain ⟨ht,hbt⟩ := extra_col_mem (by omega : 4*q < b+k) hb
      have hpair : ({(0,b+k),(4*q+r+1,b+k)} : Finset (ℕ × ℕ)).card = 2 := by simp
      rw [← hpair]
      apply card_le_card
      intro p hp
      simp only [mem_insert, mem_singleton] at hp
      rcases hp with rfl | rfl <;> apply mem_filter.mpr
      · exact ⟨mem_union_right _ ht, by simp [bit_at_last hk]⟩
      · exact ⟨mem_union_right _ hbt, by simp only [bit_above ha, bit_at_last hk]; omega⟩
  · obtain ⟨hl,hr⟩ := extra_row_mem (by omega : 4*q < a+k) ha
    have hpair : ({(a+k,0),(a+k,4*q+r+1)} : Finset (ℕ × ℕ)).card = 2 := by simp
    rw [← hpair]
    apply card_le_card
    intro p hp
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl <;> apply mem_filter.mpr
    · exact ⟨mem_union_right _ hl, by simp [bit_at_last hk]⟩
    · exact ⟨mem_union_right _ hr, by simp only [bit_above hb, bit_at_last hk]; omega⟩

theorem extra_bounds {q r : ℕ} {p : ℕ × ℕ} (hp : p ∈ extra q r) :
    p.1 < 4*q+r+2 ∧ p.2 < 4*q+r+2 := by
  simp only [extra, mem_union] at hp
  rcases hp with ((hp | hp) | hp) | hp <;>
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp <;>
    have hi := mem_range.mp hi <;> constructor <;> simp only <;> omega

theorem paddedPlacement_bounds {q r : ℕ} {p : ℕ × ℕ} (hp : p ∈ paddedPlacement q r) :
    p.1 < 4*q+r+2 ∧ p.2 < 4*q+r+2 := by
  rcases mem_union.mp hp with hc | he
  · rcases mem_union.mp hc with hc | hb
    · obtain ⟨⟨x,y⟩, hxy, rfl⟩ := mem_image.mp hc
      obtain ⟨hx,hy⟩ := core_bounds (mem_of_mem_erase hxy)
      simp only [shift]
      constructor <;> omega
    · simp only [padBoundary, mem_insert, mem_singleton] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega
  · exact extra_bounds he

@[simp] theorem paddedPlacement_corner00 (q r : ℕ) : (0,0) ∈ paddedPlacement q r := by
  simp [paddedPlacement, padBoundary]
@[simp] theorem paddedPlacement_corner0N (q r : ℕ) : (0,4*q+r+1) ∈ paddedPlacement q r := by
  simp [paddedPlacement, padBoundary]
@[simp] theorem paddedPlacement_cornerN0 (q r : ℕ) : (4*q+r+1,0) ∈ paddedPlacement q r := by
  simp [paddedPlacement, padBoundary]
@[simp] theorem paddedPlacement_cornerNN (q r : ℕ) : (4*q+r+1,4*q+r+1) ∈ paddedPlacement q r := by
  simp [paddedPlacement, padBoundary]

/-- A concrete construction at every interior order at least four, with the
sharp leading coefficient 3/2 and a uniform additive constant. -/
theorem all_orders_interval_placement (m : ℕ) (hm : 4 ≤ m) :
    ∃ S : Finset (ℕ × ℕ),
      2*S.card ≤ 3*m+25 ∧
      (∀ p ∈ S, p.1 < m+2 ∧ p.2 < m+2) ∧
      (0,0) ∈ S ∧ (0,m+1) ∈ S ∧ (m+1,0) ∈ S ∧ (m+1,m+1) ∈ S ∧
      (∀ a b k : ℕ, 0 < k → a+k ≤ m → b+k ≤ m →
        2 ≤ (S.filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card) := by
  have hq : 0 < m/4 := by omega
  have hr : m%4 < 4 := Nat.mod_lt _ (by omega)
  have hdecomp : 4*(m/4)+m%4 = m := by omega
  refine ⟨paddedPlacement (m/4) (m%4), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hc := paddedPlacement_card_le (r := m%4) hq
    omega
  · intro p hp
    simpa only [hdecomp] using paddedPlacement_bounds hp
  · exact paddedPlacement_corner00 _ _
  · simpa only [hdecomp] using paddedPlacement_corner0N (m/4) (m%4)
  · simpa only [hdecomp] using paddedPlacement_cornerN0 (m/4) (m%4)
  · simpa only [hdecomp] using paddedPlacement_cornerNN (m/4) (m%4)
  · intro a b k hk ha hb
    apply paddedPlacement_interval_cut_ge_two hq hk <;> omega

end ShellObservability.OrderedStars
