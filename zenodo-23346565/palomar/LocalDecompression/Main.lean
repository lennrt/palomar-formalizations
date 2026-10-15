module

public import LocalDecompression.GraphLayout
public import LocalDecompression.LocalView
public import LocalDecompression.Encoding
public import LocalDecompression.GraphPresentation
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Finset.Sort

/-! The finite graph/cell compression reduction.

The external input is an orientation decoder together with a witness that some
one-bit-per-cell advice gives a near-half upper bound on outgoing boundary edges. This
is the precise interface obtained in the paper from the published simple-graph
orientation theorem and the pairing of parallel boundary edges. Neither that
published theorem nor the LOCAL machine simulation is asserted as an axiom.

The decoder below first recovers the advice, recomputes ownership, and only
then looks up the edge's payload slot. Its roundtrip is proved, not assumed.
-/

@[expose] public section

namespace LocalDecompression
open scoped BigOperators

namespace Reduction
variable {V E C : Type*} [Fintype V] [LinearOrder V]
  [Fintype E] [LinearOrder E] [DecidableEq C]

def partCell (part : V → C) (c : C) : Finset V :=
  Finset.univ.filter (fun v => part v = c)

omit [LinearOrder V] in
@[simp] theorem mem_partCell (part : V → C) (c : C) (v : V) :
    v ∈ partCell part c ↔ part v = c := by simp [partCell]

/-- A decoder output selects one of an edge's two endpoints. -/
def edgeOwner (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (e : E) : C :=
  if orientation a e = 0 then part (G.left e) else part (G.right e)

def ownedEdges (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (c : C) : Finset E :=
  Finset.univ.filter (fun e => edgeOwner G part orientation a e = c)

def outgoingEdges (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (c : C) : Finset E :=
  (ownedEdges G part orientation a c).filter
    (fun e => part (G.left e) ≠ part (G.right e))

/-- The one-sided outdegree bound required for boundary ownership. It is
implied by an almost-balanced orientation but does not assert both sides of
almost balance. It assumes no edge-label recovery or encoding conclusion. -/
def BalancedAdvice (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) : Prop :=
  ∀ c, 2 * (outgoingEdges G part orientation a c).card ≤
    G.boundary (partCell part c) + 1

omit [LinearOrder E] in
theorem ownedEdges_card (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (c : C) :
    (ownedEdges G part orientation a c).card =
      G.internal (partCell part c) + (outgoingEdges G part orientation a c).card := by
  simp only [ownedEdges, outgoingEdges, EdgePresentation.internal,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases ho : orientation a e = 0 <;>
    by_cases hl : part (G.left e) = c <;>
    by_cases hr : part (G.right e) = c <;>
    simp [edgeOwner, ho, hl, hr, partCell]
  all_goals aesop

omit [LinearOrder E] in
theorem ownedEdges_card_bound (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2)
    (d : ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (hbalanced : BalancedAdvice G part orientation a) (c : C) :
    (ownedEdges G part orientation a c).card ≤ payloadLength d (partCell part c).card := by
  rw [ownedEdges_card]
  exact cell_owned_edge_bound G (partCell part c) d _ (fun v _ => hdegree v)
    (hbalanced c)

/-- Owned-edge type; it is recomputed from the recovered advice. -/
abbrev Owned (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (c : C) :=
  {e : E // e ∈ ownedEdges G part orientation a c}

/-- Increasing enumeration of an explicit finite set of original edges. -/
noncomputable def orderedSlots (edges : Finset E) :
    {e : E // e ∈ edges} ≃ Fin edges.card :=
  (edges.orderIsoOfFin rfl).symm.toEquiv

noncomputable def edgeSlots (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (c : C) :=
  orderedSlots (ownedEdges G part orientation a c)

/-- Actual finite payloads assigned to cells, padded with zero bits. -/
noncomputable def cellPayload (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (hbalanced : BalancedAdvice G part orientation a)
    (x : E → Fin 2) (c : C) : Fin (payloadLength d (partCell part c).card) → Fin 2 :=
  finitePayload (edgeSlots G part orientation a c)
    (by simpa using ownedEdges_card_bound G part orientation a d hdegree hbalanced c)
    (fun e => x e.val)

/-- All cell words have a known size independent of ownership. -/
abbrev Words (q : ℕ) (sites : C → ℕ) := ∀ c, Fin (sites c) → Fin q

noncomputable def encodeWords (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ)
    (sites : C → ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤ q ^ sites c)
    (x : E → Fin 2) : Words q sites :=
  fun c => bitBlockEncode (capacity c) (a c)
    (cellPayload G part orientation a d hdegree hbalanced x c)

def decodeAdvice {q : ℕ} {sites : C → ℕ} (word : Words q sites) : C → Fin 2 :=
  fun c => blockAdvice (word c)

/-- Read one edge's canonically ordered slot in a given finite ownership set.
The membership proof carries no payload information. -/
noncomputable def readCellSlot {q slots : ℕ} (edges : Finset E) (e : E)
    (he : e ∈ edges) (length : ℕ) (word : Fin slots → Fin q) : Fin 2 := by
  let index := orderedSlots edges ⟨e, he⟩
  exact if h : index.val < length then bitBlockPayload word ⟨index.val, h⟩ else 0

/-- Total decoder. Bad packets whose recomputed slot exceeds its block return
zero; all packets produced by the encoder use the other branch. -/
noncomputable def decodeUsingAdvice (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ)
    (sites : C → ℕ) (a : C → Fin 2) (word : Words q sites) (e : E) : Fin 2 :=
  let c := edgeOwner G part orientation a e
  readCellSlot (ownedEdges G part orientation a c) e (by simp [ownedEdges, c])
    (payloadLength d (partCell part c).card) (word c)

noncomputable def decodeWords (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ)
    (sites : C → ℕ) (word : Words q sites) : E → Fin 2 :=
  decodeUsingAdvice G part orientation d q sites (decodeAdvice word) word

@[simp] theorem decodeAdvice_encode (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ)
    (sites : C → ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤ q ^ sites c)
    (x : E → Fin 2) :
    decodeAdvice (encodeWords G part orientation a d q sites hdegree hbalanced capacity x) = a := by
  funext c
  simp [decodeAdvice, encodeWords]

/-- The new finite compression reduction: advice is read first, and its
orientation output determines the payload index used to recover each edge. -/
theorem decodeWords_encode (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ)
    (sites : C → ℕ) (hdegree : ∀ v, G.degree v ≤ d)
    (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤ q ^ sites c)
    (x : E → Fin 2) :
    decodeWords G part orientation d q sites
      (encodeWords G part orientation a d q sites hdegree hbalanced capacity x) = x := by
  unfold decodeWords
  rw [decodeAdvice_encode]
  funext e
  simp only [decodeUsingAdvice, readCellSlot]
  let c := edgeOwner G part orientation a e
  let owned : Owned G part orientation a c := ⟨e, by simp [ownedEdges, c]⟩
  have hs : (ownedEdges G part orientation a c).card ≤
      payloadLength d (partCell part c).card :=
    ownedEdges_card_bound G part orientation a d hdegree hbalanced c
  have hi : (edgeSlots G part orientation a c owned).val <
      payloadLength d (partCell part c).card :=
    (edgeSlots G part orientation a c owned).isLt.trans_le hs
  dsimp only [edgeSlots, c, owned] at hi
  rw [dite_eq_left hi]
  simp only [encodeWords, bitBlockPayload_encode, cellPayload]
  exact finitePayload_read (edgeSlots G part orientation a c) hs (fun e => x e.val) owned

/-- Actual graph vertices, bijectively enumerated as one marker and the
nonroot digit positions of each cell. No extra storage vertices are assumed. -/
noncomputable def digitLayout (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) :
    V ≃ Σ c, Option (Fin (Fintype.card (Sites part root c))) :=
  (markedLayoutEquiv part root hroot).trans
    (Equiv.sigmaCongrRight (fun c => Equiv.optionCongr (Fintype.orderIsoFinOfCardEq (Sites part root c) rfl).symm.toEquiv))

theorem digitLayout_symm_part (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (c : C)
    (i : Fin (Fintype.card (Sites part root c))) :
    part ((digitLayout part root hroot).symm ⟨c, some i⟩) = c := by
  change part ((Fintype.orderIsoFinOfCardEq (Sites part root c) rfl) i).val = c
  exact ((Fintype.orderIsoFinOfCardEq (Sites part root c) rfl) i).property.1

/-- Convert each cell word into vertex labels with a distinguished zero marker. -/
def labelsOfWords {q : ℕ} {sites : C → ℕ}
    (layout : V ≃ Σ c, Option (Fin (sites c))) (word : Words q sites) (v : V) : Fin (q + 1) :=
  match layout v with
  | ⟨_c, none⟩ => 0
  | ⟨c, some i⟩ => (word c i).succ

def unmark {q : ℕ} (hq : 0 < q) (label : Fin (q + 1)) : Fin q :=
  ⟨(label.val - 1) % q, Nat.mod_lt _ hq⟩

@[simp] theorem unmark_succ {q : ℕ} (hq : 0 < q) (digit : Fin q) :
    unmark hq digit.succ = digit := by
  apply Fin.ext
  simp [unmark, Nat.mod_eq_of_lt digit.isLt]

def wordsOfLabels {q : ℕ} {sites : C → ℕ} (hq : 0 < q)
    (layout : V ≃ Σ c, Option (Fin (sites c))) (labels : V → Fin (q + 1)) : Words q sites :=
  fun c i => unmark hq (labels (layout.symm ⟨c, some i⟩))

omit [Fintype V] [LinearOrder V] [DecidableEq C] in
@[simp] theorem wordsOfLabels_labelsOfWords {q : ℕ} {sites : C → ℕ} (hq : 0 < q)
    (layout : V ≃ Σ c, Option (Fin (sites c))) (word : Words q sites) :
    wordsOfLabels hq layout (labelsOfWords layout word) = word := by
  funext c i
  simp [wordsOfLabels, labelsOfWords]

omit [Fintype V] [LinearOrder V] [DecidableEq C] in
theorem labelsOfWords_marker {q : ℕ} {sites : C → ℕ}
    (layout : V ≃ Σ c, Option (Fin (sites c))) (word : Words q sites)
    (c : C) (i : Option (Fin (sites c))) :
    labelsOfWords layout word (layout.symm ⟨c, i⟩) = 0 ↔ i = none := by
  cases i <;> simp [labelsOfWords, Fin.ext_iff]

omit [Fintype V] [LinearOrder V] [DecidableEq C] in
/-- Reading a packet uses only the labels on its own nonroot positions. -/
theorem wordsOfLabels_local {q : ℕ} {sites : C → ℕ} (hq : 0 < q)
    (layout : V ≃ Σ c, Option (Fin (sites c))) (labels labels' : V → Fin (q + 1)) (c : C)
    (hlocal : ∀ i, labels (layout.symm ⟨c, some i⟩) = labels' (layout.symm ⟨c, some i⟩)) :
    wordsOfLabels hq layout labels c = wordsOfLabels hq layout labels' c := by
  funext i
  exact congrArg (unmark hq) (hlocal i)

/-- This reader has no access to labels outside the actual cell. -/
theorem packet_reader_fiber_local {q : ℕ} (hq : 0 < q)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (labels labels' : V → Fin (q + 1)) (c : C)
    (hlocal : ∀ v, part v = c → labels v = labels' v) :
    wordsOfLabels hq (digitLayout part root hroot) labels c =
      wordsOfLabels hq (digitLayout part root hroot) labels' c := by
  apply wordsOfLabels_local
  intro i
  exact hlocal _ (digitLayout_symm_part part root hroot c i)

/-- The actual advice reader, proved local on a fixed physical topology. -/
theorem advice_reader_local {q : ℕ} (hq : 0 < q)
    (physical : SimpleGraph V) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c) (A : ℕ)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A) :
    LocalAt physical A root
      (fun labels => decodeAdvice (wordsOfLabels hq (digitLayout part root hroot) labels)) := by
  intro x y c hagree
  apply congrArg blockAdvice
  apply packet_reader_fiber_local
  intro v hv
  apply hagree v
  apply (within_iff_dist physical hconn A (root c) v).mpr
  simpa [hv] using hcell v

omit [Fintype E] [LinearOrder E] in
/-- Joint advice-to-orientation locality: finite packet reading is composed
with an explicitly supplied local orientation decoder, not with recovery. -/
theorem extracted_orientation_local {q : ℕ} (hq : 0 < q)
    (physical : SimpleGraph V) (quotient : SimpleGraph C) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (anchor : E → C) (A T L : ℕ)
    (orientation : (C → Fin 2) → E → Fin 2)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A)
    (horacle : LocalAt quotient T anchor orientation)
    (hedge : ∀ c c', quotient.Adj c c' → physical.dist (root c) (root c') ≤ L) :
    LocalAt physical (L * T + A) (root ∘ anchor)
      (fun labels => orientation
        (decodeAdvice (wordsOfLabels hq (digitLayout part root hroot) labels))) := by
  exact local_composition physical quotient hconn root anchor A T L _ orientation
    (advice_reader_local hq physical hconn part root hroot A hcell) horacle hedge

noncomputable def vertexEncode (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤
      q ^ Fintype.card (Sites part root c)) (x : E → Fin 2) : V → Fin (q + 1) :=
  labelsOfWords (digitLayout part root hroot)
    (encodeWords G part orientation a d q _ hdegree hbalanced capacity x)

noncomputable def vertexDecode (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ) (hq : 0 < q)
    (labels : V → Fin (q + 1)) : E → Fin 2 :=
  decodeWords G part orientation d q _
    (wordsOfLabels hq (digitLayout part root hroot) labels)

/-- Complete finite vertex-label roundtrip, conditional only on boundary
orientation advice and the proved numeric storage bound. -/
theorem vertexDecode_encode (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ) (hq : 0 < q)
    (hdegree : ∀ v, G.degree v ≤ d) (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤
      q ^ Fintype.card (Sites part root c)) (x : E → Fin 2) :
    vertexDecode G part root hroot orientation d q hq
      (vertexEncode G part root hroot orientation a d q hdegree hbalanced capacity x) = x := by
  simp only [vertexDecode, vertexEncode, wordsOfLabels_labelsOfWords]
  exact decodeWords_encode G part orientation a d q _ hdegree hbalanced capacity x

/-- The produced labels identify precisely the designated roots. -/
theorem vertexEncode_zero_iff (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (d q : ℕ)
    (hdegree : ∀ v, G.degree v ≤ d) (hbalanced : BalancedAdvice G part orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d (partCell part c).card) ≤
      q ^ Fintype.card (Sites part root c)) (x : E → Fin 2) (v : V) :
    vertexEncode G part root hroot orientation a d q hdegree hbalanced capacity x v = 0 ↔
      v = root (part v) := by
  let layout := digitLayout part root hroot
  let word := encodeWords G part orientation a d q
    (fun c => Fintype.card (Sites part root c)) hdegree hbalanced capacity x
  change labelsOfWords layout word v = 0 ↔ v = root (part v)
  obtain ⟨⟨c, i⟩, hv⟩ := layout.symm.surjective v
  rw [← hv, labelsOfWords_marker]
  cases i with
  | none =>
    have hn : layout.symm ⟨c, none⟩ = root c := rfl
    rw [hn, hroot]
    simp
  | some i =>
    simp only [Option.some_ne_none, false_iff]
    change (digitLayout part root hroot).symm ⟨c, some i⟩ ≠
      root (part ((digitLayout part root hroot).symm ⟨c, some i⟩))
    rw [digitLayout_symm_part part root hroot c i]
    change ((Fintype.orderIsoFinOfCardEq (Sites part root c) rfl) i).val ≠ root c
    exact ((Fintype.orderIsoFinOfCardEq (Sites part root c) rfl) i).property.2

variable [Fintype C]

/-- The capacity hypothesis for actual cells follows from the explicit odd
degree inequality and their minimum size, not from the recovery conclusion. -/
theorem odd_cell_capacity (part : V → C) (root : C → V)
    (hroot : ∀ c, part (root c) = c) (k : ℕ) (hk : 2 ≤ k)
    (hsize : ∀ c, 16 * (k + 1) + 1 ≤ (partCell part c).card) :
    ∀ c, 2 ^ (1 + payloadLength (2 * k - 1) (partCell part c).card) ≤
      (2 ^ k - 1) ^ Fintype.card (Sites part root c) := by
  intro c
  have hf : Fintype.card (Fiber part c) = (partCell part c).card := by
    exact Fintype.card_subtype (fun v => part v = c)
  rw [card_sites part root hroot c, hf]
  exact odd_degree_capacity k _ hk (hsize c)

/-- A fixed decoder recovers every edge labelling using exactly 2^k possible
labels per original vertex. The oracle premise supplies orientation only. -/
theorem odd_degree_reduction (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (k : ℕ) (hk : 2 ≤ k)
    (hdegree : ∀ v, G.degree v ≤ 2 * k - 1)
    (hsize : ∀ c, 16 * (k + 1) + 1 ≤ (partCell part c).card)
    (horacle : ∃ a, BalancedAdvice G part orientation a) :
    ∃ encode : (E → Fin 2) → (V → Fin ((2 ^ k - 1) + 1)),
      ∀ x, vertexDecode G part root hroot orientation (2 * k - 1) (2 ^ k - 1)
        (by have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega); omega)
        (encode x) = x := by
  obtain ⟨a, ha⟩ := horacle
  refine ⟨vertexEncode G part root hroot orientation a (2 * k - 1) (2 ^ k - 1)
    hdegree ha (odd_cell_capacity part root hroot k hk hsize), ?_⟩
  intro x
  exact vertexDecode_encode G part root hroot orientation a _ _ _ hdegree ha _ x

/-- The finite reduction specialized to ID-tiebroken cells of an actual
connected simple graph. The graph itself determines the metric, the actual edge type, and the
incidence degree. The lower cell-size hypothesis is discharged by its separated
net and component size. Boundary advice remains the explicit input.
-/
theorem graph_partition_reduction
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (k : ℕ) (hk : 2 ≤ k)
    (hsep : Separated physical (16 * (k + 1)) roots)
    (hlarge : 16 * (k + 1) < Fintype.card V)
    (hdegree : ∀ v, physical.degree v ≤ 2 * k - 1)
    (orientation : (roots → Fin 2) → GraphEdge physical → Fin 2)
    (horacle : ∃ a, BalancedAdvice (graphPresentation physical)
      (rootOwner physical roots id hne) orientation a) :
    ∃ encode : (GraphEdge physical → Fin 2) → (V → Fin ((2 ^ k - 1) + 1)),
      ∀ x, vertexDecode (graphPresentation physical) (rootOwner physical roots id hne) Subtype.val
        (rootOwner_root physical hconn roots id hne hinj)
        orientation (2 * k - 1) (2 ^ k - 1)
        (by have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega); omega)
        (encode x) = x := by
  apply odd_degree_reduction (graphPresentation physical)
    (rootOwner physical roots id hne) Subtype.val
    (rootOwner_root physical hconn roots id hne hinj) orientation k hk
    (fun v => (graphPresentation_degree physical v).trans_le (hdegree v)) _ horacle
  intro c
  have hc : (partCell (rootOwner physical roots id hne) c).card =
      (cell physical roots id c.val).card := by
    have hf := fiber_card_eq_cell physical roots id hne hinj c
    rw [Fintype.card_subtype] at hf
    exact hf
  rw [hc]
  exact cell_card_lower physical hconn roots id _ hsep hlarge c.property

end Reduction
end LocalDecompression
