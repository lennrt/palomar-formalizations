module

public import LocalDecompression.Main
public import Mathlib.Data.Fintype.Fin

set_option linter.unusedSectionVars false

@[expose] public section

/-! Canonical pairing and orientation of an actual finite cell quotient.

Parallel boundary edges are sorted by their original edge order. The first
half is paired with the second half; an odd last edge is retained in a simple
residual quotient. The finite lifting proof below does not assume balanced
orientation of the multigraph. Its sole orientation input concerns the
residual simple graph.
-/
namespace LocalDecompression.QuotientOrientation
open scoped BigOperators

variable {V E C : Type*} [Fintype V] [LinearOrder V]
  [Fintype E] [LinearOrder E] [Fintype C] [LinearOrder C]

/-- An unordered pair of distinct cells, represented in their fixed linear order. -/
abbrev CellPair (C : Type*) [LinearOrder C] := {p : C × C // p.1 < p.2}

def cellPair (c d : C) (h : c ≠ d) : CellPair C :=
  ⟨(min c d, max c d), min_lt_max.mpr h⟩

@[simp] theorem cellPair_swap (c d : C) (h : c ≠ d) :
    cellPair d c h.symm = cellPair c d h := by
  apply Subtype.ext
  simp [cellPair, min_comm, max_comm]

@[simp] theorem cellPair_of_lt (c d : C) (h : c < d) :
    (cellPair c d (ne_of_lt h)).val = (c,d) := by
  simp [cellPair, min_eq_left h.le, max_eq_right h.le]

abbrev BoundaryEdge (G : EdgePresentation V E) (part : V → C) :=
  {e : E // part (G.left e) ≠ part (G.right e)}

def pairOf (G : EdgePresentation V E) (part : V → C)
    (e : BoundaryEdge G part) : CellPair C :=
  cellPair (part (G.left e.val)) (part (G.right e.val)) e.property

abbrev Parallel (G : EdgePresentation V E) (part : V → C) (p : CellPair C) :=
  {e : BoundaryEdge G part // pairOf G part e = p}

def multiplicity (G : EdgePresentation V E) (part : V → C) (p : CellPair C) : ℕ :=
  Fintype.card (Parallel G part p)

/-- The canonical sorted enumeration of an actual parallel-edge fiber. -/
noncomputable def fiberRank (G : EdgePresentation V E) (part : V → C) (p : CellPair C) :
    Parallel G part p ≃ Fin (multiplicity G part p) :=
  (Fintype.orderIsoFinOfCardEq (Parallel G part p) rfl).symm.toEquiv

/-- Boundary edges are partitioned bijectively into their sorted fibers. -/
noncomputable def boundaryIndex (G : EdgePresentation V E) (part : V → C) :
    BoundaryEdge G part ≃ Σ p : CellPair C, Fin (multiplicity G part p) :=
  (Equiv.sigmaFiberEquiv (pairOf G part)).symm.trans
    (Equiv.sigmaCongrRight (fiberRank G part))

@[simp] theorem boundaryIndex_pair (G : EdgePresentation V E) (part : V → C)
    (e : BoundaryEdge G part) : (boundaryIndex G part e).1 = pairOf G part e := rfl

/-- In each pair, rank j is directed from the lower cell and rank j+m/2
from the upper cell. Only the possible last rank uses the residual bit. -/
def lowerRank (n : ℕ) (bit : Fin 2) (i : Fin n) : Prop :=
  i.val < n / 2 ∨ (2 * (n / 2) ≤ i.val ∧ bit = 0)

instance (n : ℕ) (bit : Fin 2) (i : Fin n) : Decidable (lowerRank n bit i) :=
  inferInstanceAs (Decidable (_ ∨ _))

def blockOwner (p : CellPair C) (n : ℕ) (bit : Fin 2) (i : Fin n) : C :=
  if lowerRank n bit i then p.val.1 else p.val.2

theorem lowerRank_count (n : ℕ) (bit : Fin 2) :
    (Finset.univ.filter (lowerRank n bit)).card =
      n / 2 + if bit = 0 then n % 2 else 0 := by
  classical
  have hfirst : (Finset.univ.filter (fun i : Fin n => i.val < n / 2)).card = n / 2 := by
    rw [Fin.card_filter_val_lt, min_eq_right (Nat.div_le_self n 2)]
  have htwice : (Finset.univ.filter (fun i : Fin n => i.val < 2 * (n / 2))).card = 2 * (n / 2) := by
    rw [Fin.card_filter_val_lt, min_eq_right (by omega)]
  have hlast : (Finset.univ.filter (fun i : Fin n => 2 * (n / 2) ≤ i.val)).card = n % 2 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin n => i.val < 2 * (n / 2))
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hc
    omega
  by_cases hb : bit = 0
  · have hu : Finset.univ.filter (lowerRank n bit) =
        (Finset.univ.filter (fun i : Fin n => i.val < n / 2)) ∪
        (Finset.univ.filter (fun i : Fin n => 2 * (n / 2) ≤ i.val)) := by
      ext i
      simp [lowerRank, hb]
    have hd : Disjoint (Finset.univ.filter (fun i : Fin n => i.val < n / 2))
        (Finset.univ.filter (fun i : Fin n => 2 * (n / 2) ≤ i.val)) := by
      simp only [Finset.disjoint_left, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi hj
      omega
    rw [hu, Finset.card_union_of_disjoint hd, hfirst, hlast, ite_eq_left hb]
  · have he : Finset.univ.filter (lowerRank n bit) =
        Finset.univ.filter (fun i : Fin n => i.val < n / 2) := by
      ext i
      simp [lowerRank, hb]
    rw [he, hfirst]
    simp [hb]

theorem upperRank_count (n : ℕ) (bit : Fin 2) :
    (Finset.univ.filter (fun i => ¬ lowerRank n bit i)).card =
      n / 2 + if bit ≠ 0 then n % 2 else 0 := by
  have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ) (lowerRank n bit)
  rw [lowerRank_count] at hc
  simp only [Finset.card_univ, Fintype.card_fin] at hc
  by_cases hb : bit = 0 <;> simp [hb] at hc ⊢ <;> omega


/-- The source cell of the possible residual edge. -/
def residualOwner (p : CellPair C) (bit : Fin 2) : C :=
  if bit = 0 then p.val.1 else p.val.2

def incident (p : CellPair C) (c : C) : Prop := p.val.1 = c ∨ p.val.2 = c

instance (p : CellPair C) (c : C) : Decidable (incident p c) :=
  inferInstanceAs (Decidable (_ ∨ _))

theorem blockOwner_count (p : CellPair C) (n : ℕ) (bit : Fin 2) (c : C) :
    (Finset.univ.filter (fun i => blockOwner p n bit i = c)).card =
      (if incident p c then n / 2 else 0) +
      (if n % 2 = 1 ∧ residualOwner p bit = c then 1 else 0) := by
  classical
  have hne := ne_of_lt p.property
  have hm : n % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases hl : p.val.1 = c
  · have hr : p.val.2 ≠ c := by exact fun h => hne (hl.trans h.symm)
    have he : Finset.univ.filter (fun i => blockOwner p n bit i = c) =
        Finset.univ.filter (lowerRank n bit) := by
      ext i
      by_cases hi : lowerRank n bit i <;> simp [blockOwner, hi, hl, hr]
    rw [he, lowerRank_count]
    by_cases hb : bit = 0 <;> by_cases hm1 : n % 2 = 1 <;>
      (simp [incident, residualOwner, hb, hl, hr, hm1]; all_goals omega)
  · by_cases hr : p.val.2 = c
    · have he : Finset.univ.filter (fun i => blockOwner p n bit i = c) =
          Finset.univ.filter (fun i => ¬ lowerRank n bit i) := by
        ext i
        by_cases hi : lowerRank n bit i <;> simp [blockOwner, hi, hl, hr]
      rw [he, upperRank_count]
      by_cases hb : bit = 0 <;> by_cases hm1 : n % 2 = 1 <;>
      (simp [incident, residualOwner, hb, hl, hr, hm1]; all_goals omega)
    · have he : Finset.univ.filter (fun i => blockOwner p n bit i = c) = ∅ := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hi : lowerRank n bit i <;>
          simp only [blockOwner, hi, ite_true, ite_false, hl, hr] <;> simp
      rw [he]
      by_cases hb : bit = 0 <;> simp [incident, residualOwner, hb, hl, hr]

@[simp] theorem pairOf_incident (G : EdgePresentation V E) (part : V → C)
    (e : BoundaryEdge G part) (c : C) :
    incident (pairOf G part e) c ↔ part (G.left e.val) = c ∨ part (G.right e.val) = c := by
  unfold incident pairOf cellPair
  by_cases h : part (G.left e.val) ≤ part (G.right e.val)
  · simp [min_eq_left h, max_eq_right h]
  · simp [min_eq_right (le_of_not_ge h), max_eq_left (le_of_not_ge h), or_comm]

/-- The actual source-cell assignment to each original edge. -/
noncomputable def liftedOwner (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (e : E) : C :=
  if h : part (G.left e) ≠ part (G.right e) then
    let index := boundaryIndex G part ⟨e,h⟩
    blockOwner index.1 (multiplicity G part index.1) (orientation a index.1) index.2
  else part (G.left e)

theorem liftedOwner_endpoint (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (e : E) :
    liftedOwner G part orientation a e = part (G.left e) ∨
    liftedOwner G part orientation a e = part (G.right e) := by
  unfold liftedOwner
  split_ifs with h
  · have hi : incident (pairOf G part ⟨e,h⟩)
        (blockOwner (boundaryIndex G part ⟨e,h⟩).1
          (multiplicity G part (boundaryIndex G part ⟨e,h⟩).1)
          (orientation a (boundaryIndex G part ⟨e,h⟩).1)
          (boundaryIndex G part ⟨e,h⟩).2) := by
      rw [← boundaryIndex_pair G part ⟨e,h⟩]
      simp only [blockOwner]
      split_ifs <;> simp [incident]
    rcases (pairOf_incident G part ⟨e,h⟩ _).mp hi with hl | hr
    · exact Or.inl hl.symm
    · exact Or.inr hr.symm
  · exact Or.inl rfl

/-- Lift residual bits to the original left/right endpoint convention. -/
noncomputable def liftedOrientation (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) : (C → Fin 2) → E → Fin 2 :=
  fun a e => if liftedOwner G part orientation a e = part (G.left e) then 0 else 1

@[simp] theorem edgeOwner_lifted (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (e : E) :
    Reduction.edgeOwner G part (liftedOrientation G part orientation) a e =
      liftedOwner G part orientation a e := by
  have h := liftedOwner_endpoint G part orientation a e
  unfold Reduction.edgeOwner liftedOrientation
  by_cases hl : liftedOwner G part orientation a e = part (G.left e)
  · simp [hl]
  · have hr := h.resolve_left hl
    simp only [ite_eq_right hl]
    simpa using hr.symm


/-- Number of paired outgoing edges contributed at a cell. -/
def pairedCount (G : EdgePresentation V E) (part : V → C) (c : C) : ℕ :=
  ∑ p : CellPair C, if incident p c then multiplicity G part p / 2 else 0

/-- Degree of the residual quotient, expressed by its unique canonical pairs. -/
def residualDegree (G : EdgePresentation V E) (part : V → C) (c : C) : ℕ :=
  ∑ p : CellPair C, if multiplicity G part p % 2 = 1 ∧ incident p c then 1 else 0

/-- Outdegree in the residual quotient; bits on even-multiplicity pairs are ignored. -/
def residualOut (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (c : C) : ℕ :=
  ∑ p : CellPair C,
    if multiplicity G part p % 2 = 1 ∧ residualOwner p (orientation a p) = c then 1 else 0

theorem sum_boundary (G : EdgePresentation V E) (part : V → C) (f : E → ℕ) :
    (∑ e : BoundaryEdge G part, f e.val) =
      ∑ e : E, if part (G.left e) ≠ part (G.right e) then f e else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun e => part (G.left e) ≠ part (G.right e)))
    (by intro e; simp) f]
  exact Finset.sum_filter _ _

theorem boundary_sum (G : EdgePresentation V E) (part : V → C) (c : C) :
    G.boundary (Reduction.partCell part c) =
      ∑ e : BoundaryEdge G part, if incident (pairOf G part e) c then 1 else 0 := by
  simp_rw [pairOf_incident]
  rw [sum_boundary G part (fun e => if part (G.left e) = c ∨ part (G.right e) = c then 1 else 0)]
  unfold EdgePresentation.boundary
  apply Finset.sum_congr rfl
  intro e he
  by_cases hl : part (G.left e) = c <;> by_cases hr : part (G.right e) = c <;>
    by_cases hd : part (G.left e) = part (G.right e) <;>
    simp [Reduction.mem_partCell, hl, hr, hd] <;> aesop

theorem boundary_fiber_sum (G : EdgePresentation V E) (part : V → C) (c : C) :
    G.boundary (Reduction.partCell part c) =
      ∑ p : CellPair C, if incident p c then multiplicity G part p else 0 := by
  rw [boundary_sum]
  calc
    _ = ∑ i : (Σ p : CellPair C, Fin (multiplicity G part p)),
        if incident i.1 c then 1 else 0 :=
      Fintype.sum_equiv (boundaryIndex G part) _ _ (by intro e; rfl)
    _ = _ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases hi : incident p c <;> simp [hi]

/-- Exact decomposition of the original boundary into paired and residual edges. -/
theorem boundary_decomposition (G : EdgePresentation V E) (part : V → C) (c : C) :
    G.boundary (Reduction.partCell part c) =
      2 * pairedCount G part c + residualDegree G part c := by
  rw [boundary_fiber_sum]
  unfold pairedCount residualDegree
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hm := Nat.mod_lt (multiplicity G part p) (by omega : 0 < 2)
  by_cases hi : incident p c <;> by_cases ho : multiplicity G part p % 2 = 1 <;>
    simp [hi, ho] <;> omega

theorem outgoing_boundary_sum (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (c : C) :
    (Reduction.outgoingEdges G part (liftedOrientation G part orientation) a c).card =
      ∑ e : BoundaryEdge G part, if liftedOwner G part orientation a e.val = c then 1 else 0 := by
  rw [sum_boundary G part (fun e => if liftedOwner G part orientation a e = c then 1 else 0)]
  simp only [Reduction.outgoingEdges, Reduction.ownedEdges, Finset.card_eq_sum_ones,
    Finset.sum_filter, edgeOwner_lifted]
  apply Finset.sum_congr rfl
  intro e he
  by_cases ho : liftedOwner G part orientation a e = c <;>
    by_cases hd : part (G.left e) ≠ part (G.right e) <;> simp [ho, hd]

/-- Every pair contributes exactly one outgoing edge to either endpoint;
only its possible odd last edge depends on the residual orientation. -/
theorem outgoing_decomposition (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) (c : C) :
    (Reduction.outgoingEdges G part (liftedOrientation G part orientation) a c).card =
      pairedCount G part c + residualOut G part orientation a c := by
  rw [outgoing_boundary_sum]
  calc
    _ = ∑ i : (Σ p : CellPair C, Fin (multiplicity G part p)),
        if blockOwner i.1 (multiplicity G part i.1) (orientation a i.1) i.2 = c then 1 else 0 :=
      Fintype.sum_equiv (boundaryIndex G part) _ _ (by
        intro e
        unfold liftedOwner
        rw [dite_eq_left e.property])
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp_rw [Finset.sum_boole, blockOwner_count]
      exact Finset.sum_add_distrib

/-- Finite quotient-lifting theorem. A near-half outdegree bound is required
only on the simple residual quotient and is proved for the original boundary. -/
theorem lifted_balanced (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2)
    (hresidual : ∀ c, 2 * residualOut G part orientation a c ≤ residualDegree G part c + 1) :
    Reduction.BalancedAdvice G part (liftedOrientation G part orientation) a := by
  intro c
  rw [outgoing_decomposition, boundary_decomposition]
  exact paired_boundary_balance _ _ _ (hresidual c)


/-- The other endpoint of a canonical pair incident to c. -/
def otherCell (p : CellPair C) (c : C) : C := if p.val.1 = c then p.val.2 else p.val.1

theorem otherCell_ne (p : CellPair C) (c : C) (hi : incident p c) :
    c ≠ otherCell p c := by
  have hn := ne_of_lt p.property
  by_cases hl : p.val.1 = c
  · simpa [otherCell, hl] using hn
  · have hr := hi.resolve_left hl
    simpa [otherCell, hl, hr] using hn.symm

theorem cellPair_otherCell (p : CellPair C) (c : C) (hi : incident p c) :
    cellPair c (otherCell p c) (otherCell_ne p c hi) = p := by
  apply Subtype.ext
  have hp := p.property.le
  by_cases hl : p.val.1 = c
  · simp only [otherCell, hl, ite_true, cellPair]
    simp [← hl, min_eq_left hp, max_eq_right hp]
  · have hr := hi.resolve_left hl
    simp only [otherCell, hl, ite_false, cellPair]
    simp [← hr, min_eq_right hp, max_eq_left hp]

/-- Exactly one simple residual edge survives each odd parallel multiplicity. -/
def residualGraph (G : EdgePresentation V E) (part : V → C) : SimpleGraph C where
  Adj c d := ∃ p : CellPair C, multiplicity G part p % 2 = 1 ∧
    ((p.val.1 = c ∧ p.val.2 = d) ∨ (p.val.1 = d ∧ p.val.2 = c))
  symm := by
    constructor
    intro c d h
    obtain ⟨p, hp, h⟩ := h
    exact ⟨p, hp, h.symm⟩
  loopless := by
    constructor
    intro c h
    obtain ⟨p, hp, h | h⟩ := h <;> exact (ne_of_lt p.property) (h.1.trans h.2.symm)

noncomputable instance (G : EdgePresentation V E) (part : V → C) :
    DecidableRel (residualGraph G part).Adj := Classical.decRel _

/-- Canonical residual pairs incident to a cell. -/
abbrev ResidualAt (G : EdgePresentation V E) (part : V → C) (c : C) :=
  {p : CellPair C // multiplicity G part p % 2 = 1 ∧ incident p c}

noncomputable def residualNeighborEquiv (G : EdgePresentation V E) (part : V → C) (c : C) :
    ResidualAt G part c ≃ (residualGraph G part).neighborSet c := by
  classical
  let f : ResidualAt G part c → (residualGraph G part).neighborSet c := fun p =>
    ⟨otherCell p.val c, by
      refine ⟨p.val,p.property.1,?_⟩
      by_cases hl : p.val.val.1 = c
      · exact Or.inl ⟨hl,by simp [otherCell,hl]⟩
      · exact Or.inr ⟨by simp [otherCell,hl],p.property.2.resolve_left hl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q he
    have he' : otherCell p.val c = otherCell q.val c := congrArg Subtype.val he
    apply Subtype.ext
    rw [← cellPair_otherCell p.val c p.property.2,
      ← cellPair_otherCell q.val c q.property.2]
    apply Subtype.ext
    simp [cellPair,he']
  · intro d
    obtain ⟨p, hp, h | h⟩ := d.property
    · refine ⟨⟨p,hp,Or.inl h.1⟩,?_⟩
      apply Subtype.ext
      simp [f, otherCell, h.1, h.2]
    · refine ⟨⟨p,hp,Or.inr h.2⟩,?_⟩
      apply Subtype.ext
      have hn : p.val.1 ≠ c := by
        intro he
        exact (ne_of_lt p.property) (he.trans h.2.symm)
      change otherCell p c = d.val
      rw [otherCell, ite_eq_right hn]
      exact h.1

/-- The residual degree used in the lift is the actual simple-graph degree. -/
theorem residualDegree_eq_degree (G : EdgePresentation V E) (part : V → C) (c : C) :
    residualDegree G part c = (residualGraph G part).degree c := by
  classical
  have he := Fintype.card_congr (residualNeighborEquiv G part c)
  rw [SimpleGraph.card_neighborSet_eq_degree] at he
  simpa [residualDegree, Fintype.card_subtype] using he

/-- The residual quotient never increases the incident boundary count. -/
theorem residual_degree_le_boundary (G : EdgePresentation V E) (part : V → C) (c : C) :
    (residualGraph G part).degree c ≤ G.boundary (Reduction.partCell part c) := by
  rw [← residualDegree_eq_degree, boundary_decomposition]
  omega

/-- A degree-d original graph gives the expected d|cell| residual degree bound. -/
theorem residual_degree_bound (G : EdgePresentation V E) (part : V → C)
    (d : ℕ) (hd : ∀ v, G.degree v ≤ d) (c : C) :
    (residualGraph G part).degree c ≤ d * (Reduction.partCell part c).card := by
  have hb := G.incidence_bound (Reduction.partCell part c) d (fun v _ => hd v)
  have hr := residual_degree_le_boundary G part c
  omega

/-- The needed consequence of the external almost-balanced-orientation theorem:
a near-half outdegree bound on the actual residual simple graph. This one-sided
bound is sufficient for storage and does not itself assert almost balance.
No external theorem is declared as a Lean axiom. -/
def ResidualBalanced (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2) : Prop :=
  ∀ c, 2 * residualOut G part orientation a c ≤ (residualGraph G part).degree c + 1

theorem lifted_balanced_of_simpleGraph (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (a : C → Fin 2)
    (hresidual : ResidualBalanced G part orientation a) :
    Reduction.BalancedAdvice G part (liftedOrientation G part orientation) a := by
  apply lifted_balanced
  intro c
  rw [residualDegree_eq_degree]
  exact hresidual c


/-- The actual canonical rank partner; the possible unpaired last rank is fixed. -/
def partnerRank (n : ℕ) (i : Fin n) : Fin n :=
  ⟨if i.val < n / 2 then i.val + n / 2
    else if i.val < 2 * (n / 2) then i.val - n / 2 else i.val, by
      have hi := i.isLt
      split_ifs <;> omega⟩

theorem partnerRank_involutive (n : ℕ) : Function.Involutive (partnerRank n) := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  simp only [partnerRank]
  split_ifs <;> omega

theorem partnerRank_fixed_iff (n : ℕ) (i : Fin n) :
    partnerRank n i = i ↔ 2 * (n / 2) ≤ i.val := by
  rw [Fin.ext_iff]
  simp only [partnerRank]
  split_ifs <;> omega

theorem paired_rank_opposite (n : ℕ) (bit : Fin 2) (i : Fin n)
    (hi : i.val < 2 * (n / 2)) :
    lowerRank n bit (partnerRank n i) ↔ ¬ lowerRank n bit i := by
  unfold lowerRank partnerRank
  split_ifs <;> dsimp only <;> omega

/-- An involution on actual boundary edges: parallel pairs exchange their
sorted ranks, while exactly the possible residual edge stays fixed. -/
noncomputable def boundaryPartner (G : EdgePresentation V E) (part : V → C)
    (e : BoundaryEdge G part) : BoundaryEdge G part :=
  let index := boundaryIndex G part e
  (boundaryIndex G part).symm ⟨index.1, partnerRank (multiplicity G part index.1) index.2⟩

theorem boundaryPartner_involutive (G : EdgePresentation V E) (part : V → C) :
    Function.Involutive (boundaryPartner G part) := by
  intro e
  apply (boundaryIndex G part).injective
  unfold boundaryPartner
  dsimp only
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hi := partnerRank_involutive (multiplicity G part (boundaryIndex G part e).1)
    (boundaryIndex G part e).2
  rw [hi]

theorem pairOf_endpoints (G : EdgePresentation V E) (part : V → C)
    (e : BoundaryEdge G part) :
    (part (G.left e.val) = (pairOf G part e).val.1 ∧
      part (G.right e.val) = (pairOf G part e).val.2) ∨
    (part (G.left e.val) = (pairOf G part e).val.2 ∧
      part (G.right e.val) = (pairOf G part e).val.1) := by
  unfold pairOf cellPair
  by_cases hl : part (G.left e.val) ≤ part (G.right e.val)
  · simp [min_eq_left hl, max_eq_right hl]
  · simp [min_eq_right (le_of_not_ge hl), max_eq_left (le_of_not_ge hl)]

/-- Every residual adjacency has an actual original crossing edge as witness. -/
theorem residual_adj_has_edge (G : EdgePresentation V E) (part : V → C)
    {c d : C} (h : (residualGraph G part).Adj c d) :
    ∃ e : E, (part (G.left e) = c ∧ part (G.right e) = d) ∨
      (part (G.left e) = d ∧ part (G.right e) = c) := by
  obtain ⟨p,hodd,hend⟩ := h
  have hpos : 0 < Fintype.card (Parallel G part p) := by
    change 0 < multiplicity G part p
    omega
  obtain ⟨e⟩ := Fintype.card_pos_iff.mp hpos
  have he := pairOf_endpoints G part e.val
  rw [e.property] at he
  exact ⟨e.val.val, by rcases he with he | he <;> rcases hend with hend | hend <;> aesop⟩

/-- The residual simple graph is a subgraph of the actual Voronoi-cell quotient. -/
theorem residual_adj_cluster (physical : SimpleGraph V) (G : EdgePresentation V E)
    (hedge : ∀ e, physical.Adj (G.left e) (G.right e))
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) {c d : roots}
    (h : (residualGraph G (rootOwner physical roots id hne)).Adj c d) :
    (clusterGraph physical roots id).Adj c.val d.val := by
  have hne' : c.val ≠ d.val := by
    intro he
    exact h.ne (Subtype.ext he)
  obtain ⟨e,he | he⟩ := residual_adj_has_edge G (rootOwner physical roots id hne) h
  · exact ⟨hne',G.left e,G.right e,
      (rootOwner_eq_iff physical roots id hne hinj _ _).mp he.1,
      (rootOwner_eq_iff physical roots id hne hinj _ _).mp he.2,hedge e⟩
  · exact ⟨hne',G.right e,G.left e,
      (rootOwner_eq_iff physical roots id hne hinj _ _).mp he.2,
      (rootOwner_eq_iff physical roots id hne hinj _ _).mp he.1,(hedge e).symm⟩

/-- Residual quotient messages traverse at most 4r+1 physical edges. -/
theorem residual_root_adj_dist (physical : SimpleGraph V) (hconn : physical.Connected)
    (G : EdgePresentation V E) (hedge : ∀ e, physical.Adj (G.left e) (G.right e))
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty) (hinj : Function.Injective id)
    (r : ℕ) (hcover : ∀ v, ∃ c ∈ roots, physical.dist c v ≤ 2*r)
    {c d : roots} (h : (residualGraph G (rootOwner physical roots id hne)).Adj c d) :
    physical.dist c.val d.val ≤ 4*r+1 :=
  cluster_adj_dist physical hconn roots id r hcover
    (residual_adj_cluster physical G hedge roots id hne hinj h)

/-- On a fixed quotient, a lifted edge reads at most the residual-orientation
bit for its own parallel class. The other original-edge records supply ranks. -/
theorem liftedOrientation_congr (G : EdgePresentation V E) (part : V → C)
    (orientation orientation' : (C → Fin 2) → CellPair C → Fin 2)
    (a a' : C → Fin 2) (e : E)
    (heq : ∀ h : part (G.left e) ≠ part (G.right e),
      orientation a (pairOf G part ⟨e,h⟩) = orientation' a' (pairOf G part ⟨e,h⟩)) :
    liftedOrientation G part orientation a e = liftedOrientation G part orientation' a' e := by
  unfold liftedOrientation
  congr 1
  unfold liftedOwner
  split_ifs with h
  · dsimp only
    have hbits : orientation a (boundaryIndex G part ⟨e,h⟩).1 =
        orientation' a' (boundaryIndex G part ⟨e,h⟩).1 := heq h
    rw [hbits]
  · rfl


/-- Locality of the actual lift on the fixed residual quotient. The extra
round lets an edge anchored at its original left cell reach its lower cell.
Internal and paired edges do not read the residual orientation at all. -/
theorem liftedOrientation_local (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → CellPair C → Fin 2) (T : ℕ)
    (horacle : LocalAt (residualGraph G part) T (fun p : CellPair C => p.val.1) orientation) :
    LocalAt (residualGraph G part) (T+1) (part ∘ G.left)
      (liftedOrientation G part orientation) := by
  intro a a' e hagree
  have hsource : liftedOwner G part orientation a e = liftedOwner G part orientation a' e := by
    unfold liftedOwner
    split_ifs with h
    · let index := boundaryIndex G part ⟨e,h⟩
      change blockOwner index.1 (multiplicity G part index.1) (orientation a index.1) index.2 =
        blockOwner index.1 (multiplicity G part index.1) (orientation a' index.1) index.2
      by_cases hi : index.2.val < 2 * (multiplicity G part index.1 / 2)
      · have ht : ¬ 2 * (multiplicity G part index.1 / 2) ≤ index.2.val := by omega
        unfold blockOwner lowerRank
        simp only [ht, false_and, or_false]
      · have hbound := index.2.isLt
        have hodd : multiplicity G part index.1 % 2 = 1 := by omega
        have hend := pairOf_endpoints G part ⟨e,h⟩
        change (part (G.left e) = index.1.val.1 ∧ part (G.right e) = index.1.val.2) ∨
          (part (G.left e) = index.1.val.2 ∧ part (G.right e) = index.1.val.1) at hend
        have hbit : orientation a index.1 = orientation a' index.1 := by
          apply horacle a a' index.1
          intro c hc
          apply hagree c
          obtain ⟨walk,hlen⟩ := hc
          change Within (residualGraph G part) (T+1) (part (G.left e)) c
          rcases hend with hend | hend
          · rw [hend.1]
            exact ⟨walk,by omega⟩
          · have hadj : (residualGraph G part).Adj (part (G.left e)) index.1.val.1 :=
              ⟨index.1,hodd,Or.inr ⟨rfl,hend.1.symm⟩⟩
            exact ⟨walk.cons hadj,by simp only [SimpleGraph.Walk.length_cons]; omega⟩
        rw [hbit]
    · rfl
  simp only [liftedOrientation, hsource]


/-- Explicit external input obtained from the published one-bit simple-graph
orientation theorem (Balliu et al., full-version Appendix B, Corollary 15).
The field records only its needed outdegree consequence. This is an input
structure, not an axiom or an asserted implementation of that algorithm. -/
structure SimpleOrientationOracle (G : EdgePresentation V E) (part : V → C) (T : ℕ) where
  decode : (C → Fin 2) → CellPair C → Fin 2
  locality : LocalAt (residualGraph G part) T (fun p => p.val.1) decode
  advice : C → Fin 2
  bound : ResidualBalanced G part decode advice

/-- Both the finite balance lift and its label-locality follow from the
explicit simple-graph oracle, with no multigraph orientation assumption. -/
theorem lift_oracle (G : EdgePresentation V E) (part : V → C) (T : ℕ)
    (oracle : SimpleOrientationOracle G part T) :
    LocalAt (residualGraph G part) (T+1) (part ∘ G.left)
      (liftedOrientation G part oracle.decode) ∧
    Reduction.BalancedAdvice G part (liftedOrientation G part oracle.decode) oracle.advice :=
  ⟨liftedOrientation_local G part oracle.decode T oracle.locality,
    lifted_balanced_of_simpleGraph G part oracle.decode oracle.advice oracle.bound⟩

end LocalDecompression.QuotientOrientation
