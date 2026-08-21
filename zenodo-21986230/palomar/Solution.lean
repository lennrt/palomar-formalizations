/-
Paper: An Explicit Obstruction to Uniform Two-Word π-Representability
Authors: Lennart Rudolph, Sol, Fable
DOI: https://doi.org/10.5281/zenodo.21986230
Preprint published: 2026-08-18. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import G2Companion
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

namespace PalomarG2

def twoLetterProjection {V : Type*} [DecidableEq V]
    (w : List V) (x y : V) : List V :=
  w.filter (fun z => z = x ∨ z = y)

def KUniform {V : Type*} [DecidableEq V] (k : Nat) (w : List V) : Prop :=
  ∀ x, w.count x = k

structure TwoWordPiRepresentation {V : Type*} [DecidableEq V]
    (k : Nat) (G : SimpleGraph V) where
  word₁ : List V
  word₂ : List V
  uniform₁ : KUniform k word₁
  uniform₂ : KUniform k word₂
  adj_iff_projection_eq : ∀ {x y : V}, x ≠ y →
    (G.Adj x y ↔
      twoLetterProjection word₁ x y = twoLetterProjection word₂ x y)

def TwoWordPiRepresentable {V : Type*} [DecidableEq V]
    (k : Nat) (G : SimpleGraph V) : Prop :=
  Nonempty (TwoWordPiRepresentation k G)

noncomputable def neighborhoodTrace {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A : Finset V) (x : V) : Finset V := by
  classical
  exact A.filter (fun a => G.Adj x a)

private abbrev PositionCode (n k : Nat) :=
  {s : Finset (Fin n) // s.card = k}

private def maskedRestriction {V : Type*} [DecidableEq V]
    (A : Finset V) (x : V) : List V → List (Option V)
  | [] => []
  | z :: w =>
      if z = x then none :: maskedRestriction A x w
      else if z ∈ A then some z :: maskedRestriction A x w
      else maskedRestriction A x w

private def canonicalProjection {V : Type*} [DecidableEq V]
    (a x : V) : List V → List (Option V)
  | [] => []
  | z :: w =>
      if z = x then none :: canonicalProjection a x w
      else if z = a then some z :: canonicalProjection a x w
      else canonicalProjection a x w

private lemma canonicalProjection_eq_map {V : Type*} [DecidableEq V]
    (w : List V) {a x : V} (hax : a ≠ x) :
    canonicalProjection a x w =
      (twoLetterProjection w a x).map
        (fun z => if z = x then none else some z) := by
  induction w with
  | nil => simp [canonicalProjection, twoLetterProjection]
  | cons z w ih =>
      by_cases hzx : z = x
      · simp [canonicalProjection, twoLetterProjection, hzx, ih]
      · by_cases hza : z = a
        · subst z
          simp [canonicalProjection, twoLetterProjection, hax, ih]
        · simp [canonicalProjection, twoLetterProjection, hzx, hza, ih]

private lemma canonicalProjection_map_getD {V : Type*} [DecidableEq V]
    (w : List V) {a x : V} (hax : a ≠ x) :
    (canonicalProjection a x w).map (fun o => o.getD x) =
      twoLetterProjection w a x := by
  induction w with
  | nil => simp [canonicalProjection, twoLetterProjection]
  | cons z w ih =>
      by_cases hzx : z = x
      · simp [canonicalProjection, twoLetterProjection, hzx, ih]
      · by_cases hza : z = a
        · subst z
          simp [canonicalProjection, twoLetterProjection, hax, ih]
        · simp [canonicalProjection, twoLetterProjection, hzx, hza, ih]

private lemma projection_eq_iff_canonicalProjection_eq
    {V : Type*} [DecidableEq V] {w v : List V} {a x : V} (hax : a ≠ x) :
    twoLetterProjection w a x = twoLetterProjection v a x ↔
      canonicalProjection a x w = canonicalProjection a x v := by
  constructor
  · intro h
    rw [canonicalProjection_eq_map w hax, canonicalProjection_eq_map v hax, h]
  · intro h
    have := congrArg (List.map fun o => o.getD x) h
    simpa only [canonicalProjection_map_getD w hax,
      canonicalProjection_map_getD v hax] using this

private lemma canonicalProjection_eq_filter_maskedRestriction
    {V : Type*} [DecidableEq V] (w : List V) (A : Finset V)
    {a x : V} (ha : a ∈ A) (hx : x ∉ A) :
    canonicalProjection a x w =
      (maskedRestriction A x w).filter (fun o => o = none ∨ o = some a) := by
  induction w with
  | nil => simp [canonicalProjection, maskedRestriction]
  | cons z w ih =>
      simp only [canonicalProjection, maskedRestriction]
      by_cases hzx : z = x
      · subst z
        simp [ih]
      · by_cases hza : z = a
        · subst z
          simp [hzx, ha, ih]
        · by_cases hzA : z ∈ A
          · simp [hzx, hza, hzA, ih]
          · simp [hzx, hza, hzA, ih]

private lemma maskedRestriction_filterMap {V : Type*} [DecidableEq V]
    (w : List V) (A : Finset V) {x : V} (hx : x ∉ A) :
    (maskedRestriction A x w).filterMap id = w.filter (fun z => z ∈ A) := by
  induction w with
  | nil => simp [maskedRestriction]
  | cons z w ih =>
      simp only [maskedRestriction]
      by_cases hzx : z = x
      · subst z
        simpa [maskedRestriction, hx, id_eq] using ih
      · by_cases hzA : z ∈ A
        · have ih' : List.filterMap (fun o : Option V => o) (maskedRestriction A x w) =
              List.filter (fun z => z ∈ A) w := by simpa only [id_eq] using ih
          simpa [maskedRestriction, hzx, hzA, id_eq] using congrArg (z :: ·) ih'
        · simpa [maskedRestriction, hzx, hzA, id_eq] using ih

private lemma maskedRestriction_count_none {V : Type*} [DecidableEq V]
    (w : List V) (A : Finset V) (x : V) :
    (maskedRestriction A x w).countP (fun o => o = none) = w.count x := by
  induction w with
  | nil => simp [maskedRestriction]
  | cons z w ih =>
      by_cases hzx : z = x
      · subst z
        simp [maskedRestriction, ih]
      · by_cases hzA : z ∈ A
        · simp [maskedRestriction, hzx, hzA, ih]
        · simp [maskedRestriction, hzx, hzA, ih]

private lemma maskedRestriction_length {V : Type*} [DecidableEq V]
    (w : List V) (A : Finset V) {x : V} (hx : x ∉ A) :
    (maskedRestriction A x w).length =
      w.count x + (w.filter (fun z => z ∈ A)).length := by
  induction w with
  | nil => simp [maskedRestriction]
  | cons z w ih =>
      by_cases hzx : z = x
      · subst z
        simp [maskedRestriction, hx, ih]
        omega
      · by_cases hzA : z ∈ A
        · simp [maskedRestriction, hzx, hzA, ih, Nat.add_comm,
            Nat.add_left_comm]
        · simp [maskedRestriction, hzx, hzA, ih]

private lemma length_filter_of_uniform {V : Type*} [DecidableEq V]
    {k : Nat} {w : List V} (hw : KUniform k w) (A : Finset V) :
    (w.filter (fun z => z ∈ A)).length = k * A.card := by
  change ∀ x, w.count x = k at hw
  rw [← List.countP_eq_length_filter]
  rw [← Finset.sum_filter_count_eq_countP (fun z => z ∈ A) w]
  classical
  calc
    ∑ x ∈ w.toFinset with x ∈ A, w.count x = ∑ x ∈ A, w.count x := by
      apply Finset.sum_subset
      · intro x hx
        simp only [Finset.mem_filter] at hx
        exact hx.2
      · intro x hxA hxnot
        have hxw : x ∉ w := by
          intro hxmem
          apply hxnot
          simp [hxmem, hxA]
        simp [List.count_eq_zero.mpr hxw]
    _ = k * A.card := by
      simp_rw [hw]
      simp [Nat.mul_comm]

private lemma maskedRestriction_length_of_uniform
    {V : Type*} [DecidableEq V] {k : Nat} {w : List V}
    (hw : KUniform k w) (A : Finset V) {x : V} (hx : x ∉ A) :
    (maskedRestriction A x w).length = k * (A.card + 1) := by
  rw [maskedRestriction_length w A hx, hw, length_filter_of_uniform hw]
  simp [Nat.mul_add, Nat.add_comm]

private def nonePositions {V : Type*} {n : Nat}
    (v : List.Vector (Option V) n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v.get i = none)

private lemma nonePositions_card {V : Type*} [DecidableEq V] {n : Nat}
    (v : List.Vector (Option V) n) :
    (nonePositions v).card = v.toList.countP (fun o => o = none) := by
  unfold nonePositions
  rw [Fin.card_filter_univ_eq_vector_get_eq_count none v]
  induction v.toList with
  | nil => simp
  | cons o l ih => cases o <;> simp_all

private def wordPositionCode {V : Type*} [DecidableEq V]
    {k : Nat} {w : List V} (hw : KUniform k w)
    (A : Finset V) (x : V) (hx : x ∉ A) :
    PositionCode (k * (A.card + 1)) k := by
  let vec : List.Vector (Option V) (k * (A.card + 1)) :=
    ⟨maskedRestriction A x w, maskedRestriction_length_of_uniform hw A hx⟩
  exact ⟨nonePositions vec, by
    rw [nonePositions_card]
    simpa [vec, maskedRestriction_count_none] using hw x⟩

private lemma optionList_eq_of_pattern_and_filterMap {V : Type*} :
    ∀ {l₁ l₂ : List (Option V)},
      l₁.map Option.isNone = l₂.map Option.isNone →
      l₁.filterMap id = l₂.filterMap id → l₁ = l₂
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h
  | none :: l₁, none :: l₂, hpat, hsome => by
      simp only [List.map_cons, Option.isNone_none, List.cons.injEq] at hpat
      change l₁.filterMap id = l₂.filterMap id at hsome
      exact congrArg (none :: ·)
        (optionList_eq_of_pattern_and_filterMap hpat.2 hsome)
  | none :: l₁, some b :: l₂, hpat, _ => by simp at hpat
  | some a :: l₁, none :: l₂, hpat, _ => by simp at hpat
  | some a :: l₁, some b :: l₂, hpat, hsome => by
      simp only [List.map_cons, Option.isNone_some, List.cons.injEq] at hpat
      change a :: l₁.filterMap id = b :: l₂.filterMap id at hsome
      simp only [List.cons.injEq] at hsome
      rcases hsome with ⟨rfl, hsome⟩
      exact congrArg (some a :: ·)
        (optionList_eq_of_pattern_and_filterMap hpat.2 hsome)

private lemma vector_pattern_eq_of_nonePositions_eq {V : Type*} {n : Nat}
    (v₁ v₂ : List.Vector (Option V) n) (h : nonePositions v₁ = nonePositions v₂) :
    v₁.toList.map Option.isNone = v₂.toList.map Option.isNone := by
  have hv : v₁.map Option.isNone = v₂.map Option.isNone := by
    apply List.Vector.ext
    intro i
    have hi := Finset.ext_iff.mp h i
    simp only [nonePositions, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    simp only [List.Vector.get_map]
    cases h₁ : v₁.get i <;> cases h₂ : v₂.get i <;> simp_all
  simpa using congrArg (@List.Vector.toList Bool n) hv

private lemma maskedRestriction_eq_of_wordPositionCode_eq
    {V : Type*} [DecidableEq V] {k : Nat} {w : List V}
    (hw : KUniform k w) (A : Finset V) {x y : V}
    (hx : x ∉ A) (hy : y ∉ A)
    (hcode : wordPositionCode hw A x hx = wordPositionCode hw A y hy) :
    maskedRestriction A x w = maskedRestriction A y w := by
  let vx : List.Vector (Option V) (k * (A.card + 1)) :=
    ⟨maskedRestriction A x w, maskedRestriction_length_of_uniform hw A hx⟩
  let vy : List.Vector (Option V) (k * (A.card + 1)) :=
    ⟨maskedRestriction A y w, maskedRestriction_length_of_uniform hw A hy⟩
  apply optionList_eq_of_pattern_and_filterMap
  · apply vector_pattern_eq_of_nonePositions_eq vx vy
    exact congrArg Subtype.val hcode
  · rw [maskedRestriction_filterMap w A hx, maskedRestriction_filterMap w A hy]

private lemma projection_agreement_eq_of_codes_eq
    {V : Type*} [DecidableEq V] {k : Nat} {w v : List V}
    (hw : KUniform k w) (hv : KUniform k v) (A : Finset V)
    {x y : V} (hx : x ∉ A) (hy : y ∉ A)
    (hcodew : wordPositionCode hw A x hx = wordPositionCode hw A y hy)
    (hcodev : wordPositionCode hv A x hx = wordPositionCode hv A y hy)
    {a : V} (ha : a ∈ A) :
    (twoLetterProjection w a x = twoLetterProjection v a x) ↔
      (twoLetterProjection w a y = twoLetterProjection v a y) := by
  have hax : a ≠ x := fun h => hx (h ▸ ha)
  have hay : a ≠ y := fun h => hy (h ▸ ha)
  rw [projection_eq_iff_canonicalProjection_eq hax,
    projection_eq_iff_canonicalProjection_eq hay]
  rw [canonicalProjection_eq_filter_maskedRestriction w A ha hx,
    canonicalProjection_eq_filter_maskedRestriction v A ha hx,
    canonicalProjection_eq_filter_maskedRestriction w A ha hy,
    canonicalProjection_eq_filter_maskedRestriction v A ha hy]
  rw [maskedRestriction_eq_of_wordPositionCode_eq hw A hx hy hcodew,
    maskedRestriction_eq_of_wordPositionCode_eq hv A hx hy hcodev]

theorem neighborhood_trace_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {k : Nat}
    (r : TwoWordPiRepresentation k G) (A X : Finset V)
    (hout : ∀ x ∈ X, x ∉ A)
    (htraces : Set.InjOn (neighborhoodTrace G A) (X : Set V)) :
    X.card ≤ (Nat.choose (k * (A.card + 1)) k) ^ 2 := by
  classical
  let code : X →
      PositionCode (k * (A.card + 1)) k × PositionCode (k * (A.card + 1)) k :=
    fun x =>
      (wordPositionCode r.uniform₁ A x (hout x x.property),
       wordPositionCode r.uniform₂ A x (hout x x.property))
  have hcode : Function.Injective code := by
    intro x y hxy
    apply Subtype.ext
    apply htraces x.property y.property
    apply Finset.ext
    intro a
    simp only [neighborhoodTrace, Finset.mem_filter]
    apply and_congr_right
    intro ha
    have hax : a ≠ (x : V) := fun h => hout x x.property (h ▸ ha)
    have hay : a ≠ (y : V) := fun h => hout y y.property (h ▸ ha)
    have hp := projection_agreement_eq_of_codes_eq
      r.uniform₁ r.uniform₂ A (hout x x.property) (hout y y.property)
      (congrArg Prod.fst hxy) (congrArg Prod.snd hxy) ha
    rw [G.adj_comm, r.adj_iff_projection_eq hax,
      G.adj_comm, r.adj_iff_projection_eq hay, hp]
  have hc := Fintype.card_le_of_injective code hcode
  simpa only [Fintype.card_coe, Fintype.card_prod,
    Fintype.card_finset_len, Fintype.card_fin, pow_two] using hc

abbrev B20Vertex := Fin 20 ⊕ Fin 741322

def b20Bit (i : Fin 20) (j : Fin 741322) : Prop :=
  j.val.testBit i.val = true

def b20Adj : B20Vertex → B20Vertex → Prop
  | Sum.inl i, Sum.inr j => b20Bit i j
  | Sum.inr j, Sum.inl i => b20Bit i j
  | _, _ => False

def B20 : SimpleGraph B20Vertex where
  Adj := b20Adj
  symm := by
    intro x y h
    rcases x with i | j <;> rcases y with i' | j' <;>
      simpa [b20Adj] using h
  loopless := ⟨fun x => by
    rcases x with i | j <;> simp [b20Adj]⟩

private lemma b20Bit_iff_floor_mod (i : Fin 20) (j : Fin 741322) :
    b20Bit i j ↔ j.val / (2 ^ i.val) % 2 = 1 := by
  simp [b20Bit, Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.one_and_eq_mod_two]

private def B20Left : Finset B20Vertex :=
  Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩

private def B20Right : Finset B20Vertex :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

private lemma B20Right_card : B20Right.card = 741322 := by
  simp [B20Right]

private lemma B20Left_card : B20Left.card = 20 := by
  simp [B20Left]

private lemma B20Right_disjoint_left : Disjoint B20Right B20Left := by
  rw [Finset.disjoint_left]
  intro x hxR hxL
  simp [B20Right] at hxR
  simp [B20Left] at hxL
  rcases hxR with ⟨j, rfl⟩
  simp at hxL

private lemma B20_right_traces_injective :
    Set.InjOn (neighborhoodTrace B20 B20Left) (B20Right : Set B20Vertex) := by
  classical
  intro x hx y hy htrace
  simp [B20Right] at hx hy
  rcases hx with ⟨j, rfl⟩
  rcases hy with ⟨l, rfl⟩
  apply congrArg Sum.inr
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro n
  by_cases hn : n < 20
  · let i : Fin 20 := ⟨n, hn⟩
    have hm := Finset.ext_iff.mp htrace (Sum.inl i)
    simp [neighborhoodTrace] at hm
    have hi : Sum.inl i ∈ B20Left := by simp [B20Left]
    simp [hi, B20, b20Adj, b20Bit] at hm
    simpa [i] using hm
  · have hn20 : 20 ≤ n := Nat.le_of_not_gt hn
    have hp : 2 ^ 20 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn20
    have hj20 : j.val < 2 ^ 20 :=
      lt_of_lt_of_le j.isLt (by norm_num)
    have hl20 : l.val < 2 ^ 20 :=
      lt_of_lt_of_le l.isLt (by norm_num)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj20 hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hl20 hp)]

theorem B20_not_twoWordPiRepresentable :
    ¬ TwoWordPiRepresentable 2 B20 := by
  rintro ⟨r⟩
  have hbound := neighborhood_trace_bound B20 r B20Left B20Right
    (fun x hx => Finset.disjoint_left.mp B20Right_disjoint_left hx)
    B20_right_traces_injective
  rw [B20Right_card, B20Left_card] at hbound
  norm_num [Nat.choose_two_right] at hbound

theorem fibre_agreement_iff_no_cross_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k)) {x y : V} (hxy : x ≠ y) :
    (∀ i j : Fin k, L₁.lt (x, i) (y, j) ↔ L₂.lt (x, i) (y, j)) ↔
      ¬ ∃ i j : Fin k,
        (L₁.lt (x, i) (y, j) ∧ L₂.lt (y, j) (x, i)) ∨
        (L₁.lt (y, j) (x, i) ∧ L₂.lt (x, i) (y, j)) := by
  simpa only [G2Companion.FibreAgreement, G2Companion.QuotientEdge,
    G2Companion.inversionAdj] using
    G2Companion.fibreAgreement_iff_not_quotientEdge L₁ L₂ hxy

theorem same_fibre_no_inversion {V : Type*} {k : Nat}
    (L₁ L₂ : LinearOrder (V × Fin k))
    (h₁ : ∀ x i j, L₁.lt (x, i) (x, j) ↔ i < j)
    (h₂ : ∀ x i j, L₂.lt (x, i) (x, j) ↔ i < j)
    (x : V) (i j : Fin k) :
    ¬ ((L₁.lt (x, i) (x, j) ∧ L₂.lt (x, j) (x, i)) ∨
       (L₁.lt (x, j) (x, i) ∧ L₂.lt (x, i) (x, j))) := by
  simpa only [G2Companion.FibreMonotone, G2Companion.inversionAdj] using
    G2Companion.sameFibre_noInversion L₁ L₂ h₁ h₂ x i j

theorem trace_capacity_endpoint : (Nat.choose 42 2) ^ 2 + 20 < 2 ^ 20 := by
  exact G2Companion.vcDimensionEndpoint_2_20

theorem no_trace_code_injection :
    ¬ ∃ f : Fin 741322 → Fin 741321, Function.Injective f := by
  exact G2Companion.no_trace_code_injection

#print axioms fibre_agreement_iff_no_cross_inversion
#print axioms same_fibre_no_inversion
#print axioms trace_capacity_endpoint
#print axioms no_trace_code_injection
#print axioms neighborhood_trace_bound
#print axioms B20_not_twoWordPiRepresentable

end PalomarG2
