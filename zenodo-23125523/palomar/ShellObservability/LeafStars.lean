module

public import Mathlib
public import ShellObservability.OrderedStars

@[expose] public section

/-!
# Leaf stars: an optimal four-corner placement at every grid order

Fix `A`, `B`, `ρ`, `κ` with `m = A + 3*B + ρ = 3*A + B + κ` and `0 < ρ`.
On the `(m+2)` by `(m+2)` grid we place

* the four corners;
* `A` row-centred three-leaf stars: row line `1+i` is joined to the column
  lines `1+3*i`, `2+3*i`, `3+3*i`;
* `ρ` half rows: row line `A+1+i` carries the single boundary sensor `(A+1+i,0)`;
* `B` column-centred three-leaf stars: column line `3*A+κ+1+j` is joined to the
  row lines `A+ρ+1+3*j`, `A+ρ+2+3*j`, `A+ρ+3+3*j`;
* `κ` half columns: column line `3*A+1+j` carries the single boundary sensor
  `(0,3*A+1+j)`.

Every interior line has odd degree (three or one), so every balanced interval
cut is even; a block of half rows separating the star centres from the star
leaves prevents any balanced interval cut from vanishing. Hence all balanced
interval cuts are at least two, with `3*A + 3*B + ρ + κ + 4` sensors.
-/
namespace ShellObservability.LeafStars

open Finset OrderedStars

theorem bit_eq_zero {a k x : ℕ} : bit a k x = 0 ↔ ¬ (a ≤ x ∧ x < a + k) := by
  simp [bit]

/-- Equality of two interval bits is equivalence of the two memberships. -/
theorem bit_eq_bit_iff {a k x b l y : ℕ} :
    bit a k x = bit b l y ↔ ((a ≤ x ∧ x < a + k) ↔ (b ≤ y ∧ y < b + l)) := by
  unfold bit
  split_ifs <;> simp_all
  omega

/-- Indexed interval-cut size in zero-based interior coordinates: the two
families of three-leaf stars, then the half rows, then the half columns. -/
def leafCut (A B ρ κ a b k : ℕ) : ℕ :=
  (∑ i ∈ range A, ∑ t ∈ range 3, mismatch (bit a k i) (bit b k (3*i+t))) +
  (∑ j ∈ range B, ∑ t ∈ range 3,
    mismatch (bit a k (A+ρ+(3*j+t))) (bit b k (3*A+κ+j))) +
  (∑ i ∈ range ρ, bit a k (A+i)) +
  (∑ j ∈ range κ, bit b k (3*A+j))

/-- A vanishing cut selects whole stars only and avoids every half line. -/
theorem leafCut_zero_membership {A B ρ κ a b k : ℕ} (h : leafCut A B ρ κ a b k = 0) :
    (∀ i < A, ∀ t < 3, bit a k i = bit b k (3*i+t)) ∧
    (∀ j < B, ∀ t < 3, bit a k (A+ρ+(3*j+t)) = bit b k (3*A+κ+j)) ∧
    (∀ i < ρ, bit a k (A+i) = 0) ∧
    (∀ j < κ, bit b k (3*A+j) = 0) := by
  unfold leafCut at h
  obtain ⟨h123, hK⟩ := Nat.add_eq_zero_iff.mp h
  obtain ⟨h12, hR⟩ := Nat.add_eq_zero_iff.mp h123
  obtain ⟨hA, hB⟩ := Nat.add_eq_zero_iff.mp h12
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi t ht
    exact mismatch_eq_zero.mp (sum_eq_zero_iff.mp
      (sum_eq_zero_iff.mp hA i (mem_range.mpr hi)) t (mem_range.mpr ht))
  · intro j hj t ht
    exact mismatch_eq_zero.mp (sum_eq_zero_iff.mp
      (sum_eq_zero_iff.mp hB j (mem_range.mpr hj)) t (mem_range.mpr ht))
  · intro i hi
    exact sum_eq_zero_iff.mp hR i (mem_range.mpr hi)
  · intro j hj
    exact sum_eq_zero_iff.mp hK j (mem_range.mpr hj)

/-- No nonempty balanced interval cut vanishes. The interval of rows avoids the
half rows, so it lies among the row centres or among the row leaves; in either
case whole stars force one side to be three times as long as the other. -/
theorem leafCut_ne_zero {m A B ρ κ a b k : ℕ} (hρ : 0 < ρ)
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    (hk : 0 < k) (hb : b+k ≤ m) :
    leafCut A B ρ κ a b k ≠ 0 := by
  intro hz
  obtain ⟨hA, hB, hR, hK⟩ := leafCut_zero_membership hz
  by_cases hcase : a+k ≤ A
  · -- the row interval consists of centres of row stars
    have h1 := bit_eq_bit_iff.mp (hA a (by omega) 0 (by omega))
    have h2 := bit_eq_bit_iff.mp (hA (a+k-1) (by omega) 2 (by omega))
    omega
  · -- the row interval lies beyond every half row
    have haA : A+ρ ≤ a := by
      by_contra hlt
      have h0 := bit_eq_zero.mp (hR 0 hρ)
      have h1 := bit_eq_zero.mp (hR (a-A) (by omega))
      omega
    -- hence the column interval avoids the leaves of the row stars
    have hb3 : 3*A ≤ b := by
      by_contra hlt
      have h1 := bit_eq_bit_iff.mp (hA (b/3) (by omega) (b%3) (by omega))
      omega
    -- and it avoids the half columns
    have hbK : 3*A+κ ≤ b := by
      by_contra hlt
      have h1 := bit_eq_zero.mp (hK (b-3*A) (by omega))
      omega
    -- so it consists of centres of column stars
    have h1 := bit_eq_bit_iff.mp (hB (b-(3*A+κ)) (by omega) 0 (by omega))
    have h2 := bit_eq_bit_iff.mp (hB (b-(3*A+κ)+k-1) (by omega) 2 (by omega))
    omega

/-- Every balanced interval cut is even, because every interior line has odd
degree: three at a star centre, one at a star leaf or a half line. -/
theorem leafCut_even {m A B ρ κ a b k : ℕ}
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m) (ha : a+k ≤ m) (hb : b+k ≤ m) :
    leafCut A B ρ κ a b k % 2 = 0 := by
  have hA := sum_mismatch_identity (fun i _t => bit a k i)
    (fun i t => bit b k (3*i+t)) A
    (fun i _t => bit_le_one a k i) (fun i t => bit_le_one b k (3*i+t))
  have hB := sum_mismatch_identity (fun j t => bit a k (A+ρ+(3*j+t)))
    (fun j _t => bit b k (3*A+κ+j)) B
    (fun j t => bit_le_one a k (A+ρ+(3*j+t)))
    (fun j _t => bit_le_one b k (3*A+κ+j))
  have hr := sum_bit a k (A+ρ+3*B) (by omega)
  have hc := sum_bit b k (3*A+κ+B) (by omega)
  rw [sum_range_add, sum_range_add] at hr hc
  have hAA : (∑ i ∈ range A, ∑ _t ∈ range 3, bit a k i) =
      3*(∑ i ∈ range A, bit a k i) := by simp [mul_sum]
  have hBB : (∑ j ∈ range B, ∑ _t ∈ range 3, bit b k (3*A+κ+j)) =
      3*(∑ j ∈ range B, bit b k (3*A+κ+j)) := by simp [mul_sum]
  have hAB : (∑ i ∈ range A, ∑ t ∈ range 3, bit b k (3*i+t)) =
      ∑ x ∈ range (3*A), bit b k x := sum_triples (fun x => bit b k x) A
  have hBA : (∑ j ∈ range B, ∑ t ∈ range 3, bit a k (A+ρ+(3*j+t))) =
      ∑ x ∈ range (3*B), bit a k (A+ρ+x) := sum_triples (fun x => bit a k (A+ρ+x)) B
  rw [hAA, hAB] at hA
  rw [hBA, hBB] at hB
  unfold leafCut
  omega

/-- Every nonempty balanced interval cut of the indexed leaf-star families is
at least two. -/
theorem leafCut_ge_two {m A B ρ κ a b k : ℕ} (hρ : 0 < ρ)
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    (hk : 0 < k) (ha : a+k ≤ m) (hb : b+k ≤ m) :
    2 ≤ leafCut A B ρ κ a b k := by
  have he := leafCut_even (ρ := ρ) (κ := κ) hrow hcol ha hb
  have hn := leafCut_ne_zero (a := a) hρ hrow hcol hk hb
  omega

/-! ## The actual sensor set -/

/-- Sensor `(1+i,1+3*i+t)` of the `i`-th row-centred star. -/
def rowStarPoint (p : ℕ × ℕ) : ℕ × ℕ := (p.1+1,3*p.1+p.2+1)

/-- Sensor `(A+ρ+1+3*j+t,3*A+κ+1+j)` of the `j`-th column-centred star. -/
def colStarPoint (A ρ κ : ℕ) (p : ℕ × ℕ) : ℕ × ℕ :=
  (A+ρ+(3*p.1+p.2)+1,3*A+κ+p.1+1)

/-- Boundary sensor of the `i`-th half row. -/
def halfRowPoint (A i : ℕ) : ℕ × ℕ := (A+i+1,0)

/-- Boundary sensor of the `j`-th half column. -/
def halfColPoint (A j : ℕ) : ℕ × ℕ := (0,3*A+j+1)

def rowStars (A : ℕ) : Finset (ℕ × ℕ) := ((range A) ×ˢ (range 3)).image rowStarPoint

def colStars (A B ρ κ : ℕ) : Finset (ℕ × ℕ) :=
  ((range B) ×ˢ (range 3)).image (colStarPoint A ρ κ)

def halfRows (A ρ : ℕ) : Finset (ℕ × ℕ) := (range ρ).image (halfRowPoint A)

def halfCols (A κ : ℕ) : Finset (ℕ × ℕ) := (range κ).image (halfColPoint A)

/-- All sensors other than the four corners. -/
def leafCore (A B ρ κ : ℕ) : Finset (ℕ × ℕ) :=
  rowStars A ∪ colStars A B ρ κ ∪ halfRows A ρ ∪ halfCols A κ

/-- The four corners of the `(m+2)` by `(m+2)` grid. -/
def cornerSet (m : ℕ) : Finset (ℕ × ℕ) := {(0,0),(0,m+1),(m+1,0),(m+1,m+1)}

/-- The leaf-star placement on the `(m+2)` by `(m+2)` grid. -/
def leafPlacement (m A B ρ κ : ℕ) : Finset (ℕ × ℕ) := leafCore A B ρ κ ∪ cornerSet m

theorem rowStarPoint_injective : Function.Injective rowStarPoint := by
  intro ⟨i,t⟩ ⟨j,u⟩ h
  simp only [rowStarPoint, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem colStarPoint_injective (A ρ κ : ℕ) : Function.Injective (colStarPoint A ρ κ) := by
  intro ⟨i,t⟩ ⟨j,u⟩ h
  simp only [colStarPoint, Prod.mk.injEq] at h
  ext <;> simp only <;> omega

theorem halfRowPoint_injective (A : ℕ) : Function.Injective (halfRowPoint A) := by
  intro i j h
  simp only [halfRowPoint, Prod.mk.injEq] at h
  omega

theorem halfColPoint_injective (A : ℕ) : Function.Injective (halfColPoint A) := by
  intro i j h
  simp only [halfColPoint, Prod.mk.injEq] at h
  omega

theorem rowStars_range {A : ℕ} {p : ℕ × ℕ} (hp : p ∈ rowStars A) :
    1 ≤ p.1 ∧ p.1 ≤ A ∧ 1 ≤ p.2 ∧ p.2 ≤ 3*A := by
  obtain ⟨⟨i,t⟩, hi, rfl⟩ := mem_image.mp hp
  obtain ⟨hiA, ht⟩ := mem_product.mp hi
  have hiA := mem_range.mp hiA
  have ht := mem_range.mp ht
  simp only [rowStarPoint]
  omega

theorem colStars_range {A B ρ κ : ℕ} {p : ℕ × ℕ} (hp : p ∈ colStars A B ρ κ) :
    A+ρ+1 ≤ p.1 ∧ p.1 ≤ A+ρ+3*B ∧ 3*A+κ+1 ≤ p.2 ∧ p.2 ≤ 3*A+κ+B := by
  obtain ⟨⟨j,t⟩, hj, rfl⟩ := mem_image.mp hp
  obtain ⟨hjB, ht⟩ := mem_product.mp hj
  have hjB := mem_range.mp hjB
  have ht := mem_range.mp ht
  simp only [colStarPoint]
  omega

theorem halfRows_range {A ρ : ℕ} {p : ℕ × ℕ} (hp : p ∈ halfRows A ρ) :
    A+1 ≤ p.1 ∧ p.1 ≤ A+ρ ∧ p.2 = 0 := by
  obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
  have hi := mem_range.mp hi
  refine ⟨?_, ?_, rfl⟩ <;> simp only [halfRowPoint] <;> omega

theorem halfCols_range {A κ : ℕ} {p : ℕ × ℕ} (hp : p ∈ halfCols A κ) :
    p.1 = 0 ∧ 3*A+1 ≤ p.2 ∧ p.2 ≤ 3*A+κ := by
  obtain ⟨j, hj, rfl⟩ := mem_image.mp hp
  have hj := mem_range.mp hj
  refine ⟨rfl, ?_, ?_⟩ <;> simp only [halfColPoint] <;> omega

theorem stars_disjoint (A B ρ κ : ℕ) : Disjoint (rowStars A) (colStars A B ρ κ) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h1 := rowStars_range hp
  have h2 := colStars_range hq
  omega

theorem stars_halfRows_disjoint (A B ρ κ : ℕ) :
    Disjoint (rowStars A ∪ colStars A B ρ κ) (halfRows A ρ) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h3 := halfRows_range hq
  rcases mem_union.mp hp with hp | hp
  · have h1 := rowStars_range hp
    omega
  · have h2 := colStars_range hp
    omega

theorem stars_halfRows_halfCols_disjoint (A B ρ κ : ℕ) :
    Disjoint (rowStars A ∪ colStars A B ρ κ ∪ halfRows A ρ) (halfCols A κ) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h4 := halfCols_range hq
  rcases mem_union.mp hp with hp | hp
  · rcases mem_union.mp hp with hp | hp
    · have h1 := rowStars_range hp
      omega
    · have h2 := colStars_range hp
      omega
  · have h3 := halfRows_range hp
    omega

theorem rowStars_card (A : ℕ) : (rowStars A).card = 3*A := by
  rw [rowStars, card_image_of_injective _ rowStarPoint_injective]
  simp [card_product]
  omega

theorem colStars_card (A B ρ κ : ℕ) : (colStars A B ρ κ).card = 3*B := by
  rw [colStars, card_image_of_injective _ (colStarPoint_injective A ρ κ)]
  simp [card_product]
  omega

theorem halfRows_card (A ρ : ℕ) : (halfRows A ρ).card = ρ := by
  rw [halfRows, card_image_of_injective _ (halfRowPoint_injective A), card_range]

theorem halfCols_card (A κ : ℕ) : (halfCols A κ).card = κ := by
  rw [halfCols, card_image_of_injective _ (halfColPoint_injective A), card_range]

theorem leafCore_card (A B ρ κ : ℕ) : (leafCore A B ρ κ).card = 3*A+3*B+ρ+κ := by
  rw [leafCore, card_union_of_disjoint (stars_halfRows_halfCols_disjoint A B ρ κ),
    card_union_of_disjoint (stars_halfRows_disjoint A B ρ κ),
    card_union_of_disjoint (stars_disjoint A B ρ κ),
    rowStars_card, colStars_card, halfRows_card, halfCols_card]

/-- Location of every non-corner sensor: it lies on at least one interior line
and never on the far boundary lines. -/
theorem leafCore_range {m A B ρ κ : ℕ} (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    {p : ℕ × ℕ} (hp : p ∈ leafCore A B ρ κ) :
    p.1 ≤ m ∧ p.2 ≤ m ∧ (1 ≤ p.1 ∨ 1 ≤ p.2) := by
  rcases mem_union.mp hp with hp | hp
  · rcases mem_union.mp hp with hp | hp
    · rcases mem_union.mp hp with hp | hp
      · have h := rowStars_range hp
        omega
      · have h := colStars_range hp
        omega
    · have h := halfRows_range hp
      omega
  · have h := halfCols_range hp
    omega

theorem cornerSet_card (m : ℕ) : (cornerSet m).card = 4 := by
  unfold cornerSet
  repeat rw [card_insert_of_notMem]
  all_goals simp only [card_singleton, mem_insert, mem_singleton, Prod.mk.injEq]
  all_goals omega

theorem leafCore_cornerSet_disjoint {m A B ρ κ : ℕ}
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m) :
    Disjoint (leafCore A B ρ κ) (cornerSet m) := by
  apply disjoint_left.mpr
  intro p hp hq
  have h := leafCore_range hrow hcol hp
  simp only [cornerSet, mem_insert, mem_singleton] at hq
  rcases hq with rfl | rfl | rfl | rfl <;> simp only at h <;> omega

/-- Exact sensor count, with repetitions explicitly excluded. -/
theorem leafPlacement_card {m A B ρ κ : ℕ} (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m) :
    (leafPlacement m A B ρ κ).card = 3*A+3*B+ρ+κ+4 := by
  rw [leafPlacement, card_union_of_disjoint (leafCore_cornerSet_disjoint hrow hcol),
    leafCore_card, cornerSet_card]

theorem leafPlacement_bounds {m A B ρ κ : ℕ} (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    {p : ℕ × ℕ} (hp : p ∈ leafPlacement m A B ρ κ) : p.1 < m+2 ∧ p.2 < m+2 := by
  rcases mem_union.mp hp with hp | hp
  · have h := leafCore_range hrow hcol hp
    omega
  · simp only [cornerSet, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> constructor <;> simp only <;> omega

@[simp] theorem leafPlacement_corner00 (m A B ρ κ : ℕ) :
    (0,0) ∈ leafPlacement m A B ρ κ := by
  simp [leafPlacement, cornerSet]
@[simp] theorem leafPlacement_corner0N (m A B ρ κ : ℕ) :
    (0,m+1) ∈ leafPlacement m A B ρ κ := by
  simp [leafPlacement, cornerSet]
@[simp] theorem leafPlacement_cornerN0 (m A B ρ κ : ℕ) :
    (m+1,0) ∈ leafPlacement m A B ρ κ := by
  simp [leafPlacement, cornerSet]
@[simp] theorem leafPlacement_cornerNN (m A B ρ κ : ℕ) :
    (m+1,m+1) ∈ leafPlacement m A B ρ κ := by
  simp [leafPlacement, cornerSet]

/-! ## The indexed cut counts the actual detectors -/

theorem sum_rowStars (A a b k : ℕ) :
    (∑ p ∈ rowStars A, if bit (a+1) k p.1 ≠ bit (b+1) k p.2 then 1 else 0) =
      ∑ i ∈ range A, ∑ t ∈ range 3, mismatch (bit a k i) (bit b k (3*i+t)) := by
  unfold rowStars
  rw [sum_image (fun x _ y _ h => rowStarPoint_injective h), sum_product]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro t _
  simp only [rowStarPoint, bit_shift, mismatch]
  split_ifs <;> simp_all

theorem sum_colStars (A B ρ κ a b k : ℕ) :
    (∑ p ∈ colStars A B ρ κ, if bit (a+1) k p.1 ≠ bit (b+1) k p.2 then 1 else 0) =
      ∑ j ∈ range B, ∑ t ∈ range 3,
        mismatch (bit a k (A+ρ+(3*j+t))) (bit b k (3*A+κ+j)) := by
  unfold colStars
  rw [sum_image (fun x _ y _ h => colStarPoint_injective A ρ κ h), sum_product]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro t _
  simp only [colStarPoint, bit_shift, mismatch]
  split_ifs <;> simp_all

theorem sum_halfRows (A ρ a b k : ℕ) :
    (∑ p ∈ halfRows A ρ, if bit (a+1) k p.1 ≠ bit (b+1) k p.2 then 1 else 0) =
      ∑ i ∈ range ρ, bit a k (A+i) := by
  unfold halfRows
  rw [sum_image (fun x _ y _ h => halfRowPoint_injective A h)]
  apply sum_congr rfl
  intro i _
  simp only [halfRowPoint, bit_shift, bit_at_zero]
  have := bit_le_one a k (A+i)
  split_ifs <;> omega

theorem sum_halfCols (A κ a b k : ℕ) :
    (∑ p ∈ halfCols A κ, if bit (a+1) k p.1 ≠ bit (b+1) k p.2 then 1 else 0) =
      ∑ j ∈ range κ, bit b k (3*A+j) := by
  unfold halfCols
  rw [sum_image (fun x _ y _ h => halfColPoint_injective A h)]
  apply sum_congr rfl
  intro j _
  simp only [halfColPoint, bit_shift, bit_at_zero]
  have := bit_le_one b k (3*A+j)
  split_ifs <;> omega

/-- The indexed sum `leafCut` is exactly the number of distinct non-corner
sensors in the symmetric difference of the two line intervals. -/
theorem leafCut_eq_card (A B ρ κ a b k : ℕ) :
    leafCut A B ρ κ a b k =
      ((leafCore A B ρ κ).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  have hsum := sum_boole (R := ℕ) (fun p : ℕ × ℕ => bit (a+1) k p.1 ≠ bit (b+1) k p.2)
    (leafCore A B ρ κ)
  simp only [Nat.cast_id] at hsum
  rw [← hsum]
  unfold leafCore
  rw [sum_union (stars_halfRows_halfCols_disjoint A B ρ κ),
    sum_union (stars_halfRows_disjoint A B ρ κ),
    sum_union (stars_disjoint A B ρ κ),
    sum_rowStars, sum_colStars, sum_halfRows, sum_halfCols]
  rfl

/-- The non-corner sensors already detect every nonempty balanced pair of
interior intervals at least twice. -/
theorem leafCore_interval_cut_ge_two {m A B ρ κ a b k : ℕ} (hρ : 0 < ρ)
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    (hk : 0 < k) (ha : a+k ≤ m) (hb : b+k ≤ m) :
    2 ≤ ((leafCore A B ρ κ).filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  rw [← leafCut_eq_card]
  exact leafCut_ge_two hρ hrow hcol hk ha hb

/-- Every nonempty balanced interior interval cut has at least two sensors in
the leaf-star placement. -/
theorem leafPlacement_interval_cut_ge_two {m A B ρ κ a b k : ℕ} (hρ : 0 < ρ)
    (hrow : A+3*B+ρ = m) (hcol : 3*A+B+κ = m)
    (hk : 0 < k) (ha : a+k ≤ m) (hb : b+k ≤ m) :
    2 ≤ ((leafPlacement m A B ρ κ).filter
      (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card := by
  apply le_trans (leafCore_interval_cut_ge_two hρ hrow hcol hk ha hb)
  apply card_le_card
  apply filter_subset_filter
  exact subset_union_left

/-! ## Parameters for every interior size -/

/-- Admissible parameters realising `⌈(3m+9)/2⌉` sensors for every `m ≥ 1`:
with `m = 4q+r`, take `(A,B,ρ,κ) = (q,q-1,3,1)`, `(q,q,1,1)`, `(q,q,2,2)`,
`(q+1,q,2,0)` for `r = 0,1,2,3` respectively. -/
theorem exists_parameters (m : ℕ) (hm : 0 < m) :
    ∃ A B ρ κ : ℕ, 0 < ρ ∧ A+3*B+ρ = m ∧ 3*A+B+κ = m ∧
      3*A+3*B+ρ+κ+4 = (3*m+10)/2 := by
  have hr : m%4 < 4 := Nat.mod_lt _ (by omega)
  have hdecomp : 4*(m/4)+m%4 = m := by omega
  rcases (by omega : m%4 = 0 ∨ m%4 = 1 ∨ m%4 = 2 ∨ m%4 = 3) with h | h | h | h
  · exact ⟨m/4, m/4-1, 3, 1, by omega, by omega, by omega, by omega⟩
  · exact ⟨m/4, m/4, 1, 1, by omega, by omega, by omega, by omega⟩
  · exact ⟨m/4, m/4, 2, 2, by omega, by omega, by omega, by omega⟩
  · exact ⟨m/4+1, m/4, 2, 0, by omega, by omega, by omega, by omega⟩

/-- A concrete four-corner placement with exactly `⌈(3m+9)/2⌉` sensors and all
balanced interval cuts at least two, at every interior order `m ≥ 1`. -/
theorem all_orders_optimal_interval_placement (m : ℕ) (hm : 0 < m) :
    ∃ S : Finset (ℕ × ℕ),
      S.card = (3*m+10)/2 ∧
      (∀ p ∈ S, p.1 < m+2 ∧ p.2 < m+2) ∧
      (0,0) ∈ S ∧ (0,m+1) ∈ S ∧ (m+1,0) ∈ S ∧ (m+1,m+1) ∈ S ∧
      (∀ a b k : ℕ, 0 < k → a+k ≤ m → b+k ≤ m →
        2 ≤ (S.filter (fun p => bit (a+1) k p.1 ≠ bit (b+1) k p.2)).card) := by
  obtain ⟨A, B, ρ, κ, hρ, hrow, hcol, hcard⟩ := exists_parameters m hm
  refine ⟨leafPlacement m A B ρ κ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [leafPlacement_card hrow hcol, hcard]
  · exact fun p hp => leafPlacement_bounds hrow hcol hp
  · exact leafPlacement_corner00 _ _ _ _ _
  · exact leafPlacement_corner0N _ _ _ _ _
  · exact leafPlacement_cornerN0 _ _ _ _ _
  · exact leafPlacement_cornerNN _ _ _ _ _
  · exact fun a b k hk ha hb => leafPlacement_interval_cut_ge_two hρ hrow hcol hk ha hb

end ShellObservability.LeafStars
