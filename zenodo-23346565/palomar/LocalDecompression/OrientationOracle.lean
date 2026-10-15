module

public import UniformStatement
public import LocalDecompression.Padding
public import LocalDecompression.QuotientOrientation

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace LocalDecompression.OrientationOracle

open scoped BigOperators

theorem tailId_endpoints {V : Type*} [Fintype V]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (advice : V → Fin 2) (u v : V) :
    tailId F N D c t G id advice u v = id u ∨
      tailId F N D c t G id advice u v = id v := by
  unfold tailId
  split_ifs <;> simp

theorem tailId_swap {V : Type*} [Fintype V]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (id : V → ℕ)
    (advice : V → Fin 2) (u v : V) :
    tailId F N D c t G id advice u v = tailId F N D c t G id advice v u := by
  rcases lt_trichotomy (id u) (id v) with h | h | h
  · simp only [tailId, h, not_lt.mpr h.le, ite_true, ite_false]
  · simp [tailId, h]
  · simp only [tailId, h, not_lt.mpr h.le, ite_true, ite_false]

/-- Convert the canonical identifier-based tail to the existing CellPair bit
convention, whose auxiliary linear order need not coincide with identifiers. -/
noncomputable def pairRule {C : Type*} [Fintype C] [LinearOrder C]
    (F : Rule) (N D c t : ℕ) (H : SimpleGraph C) (id : C → ℕ) :
    (C → Fin 2) → LocalDecompression.QuotientOrientation.CellPair C → Fin 2 :=
  fun a p => if tailId F N D c t H id a p.val.1 p.val.2 = id p.val.1 then 0 else 1

theorem pairRule_owner_id {C : Type*} [Fintype C] [LinearOrder C]
    (F : Rule) (N D c t : ℕ) (H : SimpleGraph C) (id : C → ℕ)
    (a : C → Fin 2) (p : LocalDecompression.QuotientOrientation.CellPair C) :
    id (LocalDecompression.QuotientOrientation.residualOwner p (pairRule F N D c t H id a p)) =
      tailId F N D c t H id a p.val.1 p.val.2 := by
  unfold pairRule LocalDecompression.QuotientOrientation.residualOwner
  by_cases h : tailId F N D c t H id a p.val.1 p.val.2 = id p.val.1
  · simp [h]
  · have hr := (tailId_endpoints F N D c t H id a p.val.1 p.val.2).resolve_left h
    have hn : id p.val.2 ≠ id p.val.1 := fun he => h (hr.trans he)
    simp [hr, hn]

theorem mem_floodBall_iff_within {V : Type*} [Fintype V]
    (G : SimpleGraph V) (t : ℕ) (u v : V) :
    v ∈ floodBall G t u ↔ LocalDecompression.Within G t u v := by
  classical
  induction t generalizing u v with
  | zero =>
    simp only [floodBall, Finset.mem_singleton]
    constructor
    · intro h
      subst v
      exact ⟨.nil, by simp⟩
    · rintro ⟨p, hp⟩
      exact (SimpleGraph.Walk.eq_of_length_eq_zero (Nat.eq_zero_of_le_zero hp)).symm
  | succ t ih =>
    simp only [floodBall, Finset.mem_union, Finset.mem_biUnion]
    constructor
    · rintro (h | ⟨w, hw, hwv⟩)
      · obtain ⟨p, hp⟩ := (ih u v).mp h
        exact ⟨p, by omega⟩
      · obtain ⟨p, hp⟩ := (ih u w).mp hw
        have hadj : G.Adj w v := by simpa only [neighbors, SimpleGraph.mem_neighborFinset] using hwv
        exact ⟨p.concat hadj, by simp only [SimpleGraph.Walk.length_concat]; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact Or.inl ((ih u u).mpr ⟨.nil, by simp⟩)
      | cons h p =>
        obtain ⟨w, q, hlast, he⟩ := p.exists_cons_eq_concat h
        have hq : q.length ≤ t := by
          rw [he, SimpleGraph.Walk.length_concat] at hp
          omega
        exact Or.inr ⟨w, (ih u w).mpr ⟨q, hq⟩,
          by simpa only [neighbors, SimpleGraph.mem_neighborFinset] using hlast⟩

theorem floodBall_image {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hneighbors : ∀ v, neighbors H (f v) = (neighbors G v).image f)
    (t : ℕ) (v : V) : floodBall H t (f v) = (floodBall G t v).image f := by
  classical
  induction t with
  | zero => simp [floodBall]
  | succ t ih =>
    simp only [floodBall, ih, Finset.image_union, Finset.biUnion_image,
      Finset.image_biUnion]
    simp_rw [hneighbors]
    ext w
    simp

/-- A closed graph embedding preserves the entire finite oracle view.
This single lemma handles both root inclusion and disjoint dummy padding. -/
theorem view_image {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V → W)
    (hneighbors : ∀ v, neighbors H (f v) = (neighbors G v).image f)
    (idV : V → ℕ) (idW : W → ℕ) (hid : ∀ v, idW (f v) = idV v)
    (a : V → Fin 2) (b : W → Fin 2) (hadvice : ∀ v, b (f v) = a v)
    (t : ℕ) (v : V) : view H idW b t (f v) = view G idV a t v := by
  classical
  rw [view, floodBall_image G H f hneighbors, Finset.image_image]
  unfold view
  apply Finset.image_congr
  intro x hx
  simp only [Function.comp_apply, record, hid, hadvice, hneighbors, Finset.image_image]
  congr 1
  apply Finset.image_congr
  intro w hw
  exact hid w

theorem padded_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D : ℕ) (v : V) :
    neighbors (LocalDecompression.Padding.paddedGraph G D) (Sum.inl v) =
      (neighbors G v).image Sum.inl := by
  classical
  ext w
  simp only [neighbors, SimpleGraph.mem_neighborFinset, Finset.mem_image]
  cases w <;> simp [LocalDecompression.Padding.paddedGraph]

/-- Dummy-clique topology and arbitrary advice on the dummy vertices never
enter an original vertex's finite view. Public N,D,c remain supplied explicitly. -/
theorem padded_view {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (D n c : ℕ) (id : V → ℕ)
    (a : V → Fin 2) (dummy : Fin (D + 1) → Fin 2) (t : ℕ) (v : V) :
    view (LocalDecompression.Padding.paddedGraph G D)
      (LocalDecompression.Padding.paddedId id n c D) (Sum.elim a dummy) t (.inl v) =
      view G id a t v := by
  apply view_image G (LocalDecompression.Padding.paddedGraph G D) Sum.inl
    (padded_neighbors G D) id _ (fun _ => rfl) a _ (fun _ => rfl)

theorem original_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) (v : roots) :
    neighbors (LocalDecompression.Padding.onOriginal roots H) v.val =
      (neighbors H v).image Subtype.val := by
  classical
  ext w
  simp only [neighbors, SimpleGraph.mem_neighborFinset, Finset.mem_image]
  change (H.map Subtype.val).Adj v.val w ↔ _
  rw [SimpleGraph.map_adj']
  constructor
  · rintro ⟨_, a, b, hab, ha, hb⟩
    have hav : a = v := Subtype.ext ha
    subst a
    exact ⟨b, hab, hb⟩
  · rintro ⟨b, hab, rfl⟩
    exact ⟨Subtype.val_injective.ne hab.ne, v, b, hab, rfl, rfl⟩

theorem tailId_image {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W)
    (hneighbors : ∀ v, neighbors H (f v) = (neighbors G v).image f)
    (idV : V → ℕ) (idW : W → ℕ) (hid : ∀ v, idW (f v) = idV v)
    (a : V → Fin 2) (b : W → Fin 2) (hadvice : ∀ v, b (f v) = a v)
    (u v : V) : tailId F N D c t H idW b (f u) (f v) =
      tailId F N D c t G idV a u v := by
  unfold tailId output
  simp_rw [hid, view_image G H f hneighbors idV idW hid a b hadvice]

theorem outdegree_image {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (F : Rule) (N D c t : ℕ) (G : SimpleGraph V) (H : SimpleGraph W)
    (f : V → W) (hinj : Function.Injective f)
    (hneighbors : ∀ v, neighbors H (f v) = (neighbors G v).image f)
    (idV : V → ℕ) (idW : W → ℕ) (hid : ∀ v, idW (f v) = idV v)
    (a : V → Fin 2) (b : W → Fin 2) (hadvice : ∀ v, b (f v) = a v)
    (v : V) : outdegree F N D c t H idW b (f v) =
      outdegree F N D c t G idV a v := by
  classical
  have he : (neighbors H (f v)).filter
      (fun w => tailId F N D c t H idW b (f v) w = idW (f v)) =
      ((neighbors G v).filter
        (fun w => tailId F N D c t G idV a v w = idV v)).image f := by
    rw [hneighbors]
    ext w
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, ht⟩
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      simpa only [tailId_image F N D c t G H f hneighbors idV idW hid a b hadvice,
        hid] using ht
    · rintro ⟨x, ⟨hx, ht⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      simpa only [tailId_image F N D c t G H f hneighbors idV idW hid a b hadvice,
        hid] using ht
  unfold outdegree
  rw [he, Finset.card_image_of_injective _ hinj]

open LocalDecompression.QuotientOrientation in
/-- Bridge the ordinary neighbor-count outdegree of the finite-view rule to
the retained library's canonical residual-pair count. -/
theorem residualOut_le_outdegree
    {V E C : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
    [Fintype C] [LinearOrder C]
    (F : Rule) (N D c t : ℕ) (G : LocalDecompression.EdgePresentation V E)
    (part : V → C) (id : C → ℕ)
    (a : C → Fin 2) (v : C) :
    residualOut G part (pairRule F N D c t (residualGraph G part) id) a v ≤
      outdegree F N D c t (residualGraph G part) id a v := by
  classical
  let H := residualGraph G part
  let orientation := pairRule F N D c t H id
  let P := {p : CellPair C // multiplicity G part p % 2 = 1 ∧
    residualOwner p (orientation a p) = v}
  let S := {w : C // w ∈ neighbors H v ∧ tailId F N D c t H id a v w = id v}
  have hi : ∀ p : P, incident p.val v := by
    intro p
    have hp := p.property.2
    unfold residualOwner at hp
    split_ifs at hp with h
    · exact Or.inl hp
    · exact Or.inr hp
  let toIncident : P → ResidualAt G part v := fun p => ⟨p.val, p.property.1, hi p⟩
  let toNeighbor : P → H.neighborSet v := fun p =>
    residualNeighborEquiv G part v (toIncident p)
  have ht : ∀ p : P, tailId F N D c t H id a v (toNeighbor p).val = id v := by
    intro p
    have hp : tailId F N D c t H id a p.val.val.1 p.val.val.2 = id v :=
      (pairRule_owner_id F N D c t H id a p.val).symm.trans (congrArg id p.property.2)
    change tailId F N D c t H id a v (otherCell p.val v) = id v
    by_cases hl : p.val.val.1 = v
    · simpa [otherCell, hl] using hp
    · have hr := (hi p).resolve_left hl
      rw [tailId_swap]
      simpa [otherCell, hl, hr] using hp
  let f : P → S := fun p => ⟨(toNeighbor p).val,
    by simpa only [neighbors, SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborSet]
      using (toNeighbor p).property,
    ht p⟩
  have hf : Function.Injective f := by
    intro p q he
    have hn : toNeighbor p = toNeighbor q :=
      Subtype.ext (congrArg (fun z : S => z.val) he)
    have hpair : toIncident p = toIncident q := (residualNeighborEquiv G part v).injective hn
    exact Subtype.ext (congrArg (fun z : ResidualAt G part v => z.val) hpair)
  have hc := Fintype.card_le_of_injective f hf
  have hP : Fintype.card P = residualOut G part orientation a v := by
    simp [P, residualOut, Fintype.card_subtype]
  have hS : Fintype.card S = outdegree F N D c t H id a v := by
    dsimp only [S]
    rw [Fintype.card_subtype]
    unfold outdegree
    congr 1
    ext w
    simp
  rw [hP, hS] at hc
  exact hc

open LocalDecompression.QuotientOrientation in
theorem residualBalanced_of_outdegree
    {V E C : Type*} [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
    [Fintype C] [LinearOrder C]
    (F : Rule) (N D c t : ℕ) (G : LocalDecompression.EdgePresentation V E)
    (part : V → C) (id : C → ℕ)
    (a : C → Fin 2)
    (hbound : ∀ v, 2 * outdegree F N D c t (residualGraph G part) id a v ≤
      (residualGraph G part).degree v + 1) :
    ResidualBalanced G part (pairRule F N D c t (residualGraph G part) id) a := by
  intro v
  have hle := residualOut_le_outdegree F N D c t G part id a v
  have hb := hbound v
  omega

/-- Isolated original nonroots likewise disappear from the root's view. -/
theorem original_view {V : Type*} [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) (id : V → ℕ)
    (a : roots → Fin 2) (allAdvice : V → Fin 2)
    (hadv : ∀ v : roots, allAdvice v.val = a v) (t : ℕ) (v : roots) :
    view (LocalDecompression.Padding.onOriginal roots H) id allAdvice t v.val =
      view H (id ∘ Subtype.val) a t v := by
  apply view_image H (LocalDecompression.Padding.onOriginal roots H) Subtype.val
    (original_neighbors roots H) _ id (fun _ => rfl) a allAdvice hadv

/-- The fully padded graph supplied to the external theorem has exactly the
same root-local input as the residual quotient, for every total advice input. -/
theorem padded_original_view {V : Type*} [Fintype V] [DecidableEq V]
    (roots : Finset V) (H : SimpleGraph roots) (D n c : ℕ) (id : V → ℕ)
    (a : roots → Fin 2) (allAdvice : V → Fin 2)
    (hadv : ∀ v : roots, allAdvice v.val = a v)
    (dummy : Fin (D + 1) → Fin 2) (t : ℕ) (v : roots) :
    view (LocalDecompression.Padding.paddedGraph
      (LocalDecompression.Padding.onOriginal roots H) D)
      (LocalDecompression.Padding.paddedId id n c D)
      (Sum.elim allAdvice dummy) t (.inl v.val) =
        view H (id ∘ Subtype.val) a t v := by
  rw [padded_view, original_view roots H id a allAdvice hadv]

/-- Restrict a good padded input to the residual roots. No advice is stored
on isolated original vertices or on the artificial clique. -/
theorem exists_good_root_advice {V : Type} [Fintype V] [DecidableEq V]
    (F : Rule) (T : ℕ → ℕ) (hgood : GoodOneBitOracle F T)
    (roots : Finset V) (H : SimpleGraph roots) [DecidableRel H.Adj]
    (id : V → ℕ) (c D : ℕ) (hc : 1 ≤ c)
    (hinj : Function.Injective id) (hpositive : ∀ v, 1 ≤ id v)
    (hbound : ∀ v, id v ≤ (Fintype.card V) ^ c)
    (hdegree : ∀ v, H.degree v ≤ D) :
    ∃ a : roots → Fin 2, ∀ v,
      2 * outdegree F (Fintype.card V + D + 1) D c (T D) H
        (id ∘ Subtype.val) a v ≤ H.degree v + 1 := by
  classical
  let N := Fintype.card V + D + 1
  let PG := LocalDecompression.Padding.paddedGraph
    (LocalDecompression.Padding.onOriginal roots H) D
  let pid := LocalDecompression.Padding.paddedId id (Fintype.card V) c D
  have hp := LocalDecompression.Padding.padded_input_parameters roots H id c D hc
    hinj hpositive hbound hdegree
  obtain ⟨b, hb⟩ := hgood (V ⊕ Fin (D + 1)) PG N D c hp.1 hp.2.1 hc
    pid hp.2.2.1 hp.2.2.2
  let f : roots → V ⊕ Fin (D + 1) := fun v => .inl v.val
  let a : roots → Fin 2 := fun v => b (f v)
  have hn : ∀ v, neighbors PG (f v) = (neighbors H v).image f := by
    intro v
    dsimp only [PG, f]
    rw [padded_neighbors, original_neighbors, Finset.image_image]
    rfl
  refine ⟨a, fun v => ?_⟩
  have he := outdegree_image F N D c (T D) H PG f
    (Sum.inl_injective.comp Subtype.val_injective) hn (id ∘ Subtype.val) pid
    (fun _ => rfl) a b (fun _ => rfl) v
  have hd : PG.degree (f v) = H.degree v := by
    dsimp only [PG, f]
    rw [LocalDecompression.Padding.original_degree,
      LocalDecompression.Padding.onOriginal_root_degree]
  simpa only [he, hd] using hb (f v)

end LocalDecompression.OrientationOracle
