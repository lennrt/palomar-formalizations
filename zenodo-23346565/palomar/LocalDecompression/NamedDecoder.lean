module
public import LocalDecompression.ViewPackets

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

@[expose] public section
namespace LocalDecompression.FiniteView
open Reduction MarkerLocality BoundedCells BoundedPacket
open scoped BigOperators

/-- Read a canonically sorted finite payload without changing slot indices
when the ambient edge representation is replaced by an order embedding. -/
theorem orderedSlots_map_val {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f : A ↪o B) (s : Finset A) (a : A) (ha : a ∈ s) :
    (orderedSlots (s.map f.toEmbedding) ⟨f a, s.mem_map_of_mem f.toEmbedding ha⟩).val =
      (orderedSlots s ⟨a,ha⟩).val := by
  let iso : s ≃o s.map f.toEmbedding :=
    { toEquiv := Finset.equivMap f.toEmbedding s
      map_rel_iff' := by intro x y; exact f.le_iff_le }
  let ranks : Fin s.card ≃o Fin (s.map f.toEmbedding).card :=
    ((s.orderIsoOfFin rfl).trans iso).trans ((s.map f.toEmbedding).orderIsoOfFin rfl).symm
  have h := Fin.coe_orderIso_apply ranks ((s.orderIsoOfFin rfl).symm ⟨a,ha⟩)
  simpa [ranks, iso, Finset.equivMap, orderedSlots] using h

theorem readCellSlot_map {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f : A ↪o B) (s : Finset A) (a : A) (ha : a ∈ s)
    (length : ℕ) {q slots : ℕ} (word : Fin slots → Fin q) :
    readCellSlot (s.map f.toEmbedding) (f a) (s.mem_map_of_mem f.toEmbedding ha) length word =
      readCellSlot s a ha length word := by
  have h := orderedSlots_map_val f s a ha
  unfold readCellSlot
  dsimp only
  split_ifs with hi hj hj
  · apply congrArg (bitBlockPayload word)
    exact Fin.ext h
  · omega
  · omega
  · rfl

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- The common ambient edge-name type is independent of physical topology.
Lexicographic order agrees with the original GraphEdge order. -/
abbrev NamedPair (V : Type*) := V ×ₗ V

def graphPairEmbedding (G : SimpleGraph V) :
    @OrderEmbedding (GraphEdge G) (NamedPair V) (graphEdgeLinearOrder G).toLE inferInstance where
  toFun := fun e => toLex e.val
  inj' := by intro a b h; exact Subtype.ext (congrArg ofLex h)
  map_rel_iff' := by intro a b; rfl

/-- A finite actual-edge set represented in the common name space. -/
noncomputable def actualPairs (G : SimpleGraph V) : Finset (NamedPair V) := by
  classical
  exact Finset.univ.filter (fun p => (ofLex p).1 < (ofLex p).2 ∧ G.Adj (ofLex p).1 (ofLex p).2)

@[simp] theorem mem_actualPairs (G : SimpleGraph V) (p : NamedPair V) :
    p ∈ actualPairs G ↔ (ofLex p).1 < (ofLex p).2 ∧ G.Adj (ofLex p).1 (ofLex p).2 := by
  classical
  simp [actualPairs]

/-- Select an endpoint's cell only if both endpoints are assigned. Edges
incident to an uncovered vertex have no owner and ultimately receive zero. -/
def pairOwner (part : V → Option V) (directions : NamedPair V → Fin 2)
    (e : NamedPair V) : Option V :=
  match part (ofLex e).1, part (ofLex e).2 with
  | some c, some d => some (if directions e = 0 then c else d)
  | _, _ => none

noncomputable def pairOwnedEdges (G : SimpleGraph V) (part : V → Option V)
    (directions : NamedPair V → Fin 2) (c : V) : Finset (NamedPair V) := by
  classical
  exact (actualPairs G).filter (fun e => pairOwner part directions e = some c)

@[simp] theorem mem_pairOwnedEdges (G : SimpleGraph V) (part : V → Option V)
    (directions : NamedPair V → Fin 2) (c : V) (e : NamedPair V) :
    e ∈ pairOwnedEdges G part directions c ↔
      e ∈ actualPairs G ∧ pairOwner part directions e = some c := by
  classical
  simp [pairOwnedEdges]

/-- The final total bounded decoder. The supplied direction array is the
output of the separate advice/quotient stage, never encoded payload data.
No global marker-cover, separation, balance, or capacity test occurs here. -/
noncomputable def boundedPairDecode {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R d : ℕ) (labels : V → Fin (q+1))
    (directions : NamedPair V → Fin 2) (e : NamedPair V) : Fin 2 := by
  classical
  let part := boundedOwner G id R labels
  match pairOwner part directions e with
  | none => exact 0
  | some c =>
    if he : e ∈ pairOwnedEdges G part directions c then
      exact readCellSlot (pairOwnedEdges G part directions c) e he
        (payloadLength d (boundedCell G id R labels c).card)
        (boundedWord hq G id R labels c)
    else exact 0

theorem boundedPairDecode_nonedge {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R d : ℕ) (labels : V → Fin (q+1))
    (directions : NamedPair V → Fin 2) (e : NamedPair V) (he : e ∉ actualPairs G) :
    boundedPairDecode hq G id R d labels directions e = 0 := by
  classical
  simp only [boundedPairDecode]
  split <;> simp [he]

theorem boundedPairDecode_unassigned {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R d : ℕ) (labels : V → Fin (q+1))
    (directions : NamedPair V → Fin 2) (e : NamedPair V)
    (ho : pairOwner (boundedOwner G id R labels) directions e = none) :
    boundedPairDecode hq G id R d labels directions e = 0 := by
  simp [boundedPairDecode,ho]

/-- The arbitrary-input final lookup is determined by its actual owner,
owned-edge set, bounded cell size and ordered packet. This intermediate
congruence contains no correctness or balanced-orientation premise. -/
theorem boundedPairDecode_congr {q : ℕ} (hq : 0 < q)
    (G H : SimpleGraph V) (id : V → ℕ) (R d : ℕ) (x y : V → Fin (q+1))
    (ox oy : NamedPair V → Fin 2) (e : NamedPair V)
    (_hedge : e ∈ actualPairs G ↔ e ∈ actualPairs H)
    (howner : pairOwner (boundedOwner G id R x) ox e =
      pairOwner (boundedOwner H id R y) oy e)
    (hsets : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
      pairOwnedEdges G (boundedOwner G id R x) ox c =
        pairOwnedEdges H (boundedOwner H id R y) oy c)
    (hcell : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
      boundedCell G id R x c = boundedCell H id R y c)
    (hsites : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
      boundedSites G id R x c = boundedSites H id R y c)
    (hword : ∀ c, pairOwner (boundedOwner G id R x) ox e = some c →
      HEq (boundedWord hq G id R x c) (boundedWord hq H id R y c)) :
    boundedPairDecode hq G id R d x ox e = boundedPairDecode hq H id R d y oy e := by
  classical
  cases ho : pairOwner (boundedOwner G id R x) ox e with
  | none => simp [boundedPairDecode, ← howner, ho]
  | some c =>
    have ho' : pairOwner (boundedOwner H id R y) oy e = some c := howner.symm.trans ho
    simp only [boundedPairDecode, ho, ho']
    have hs := hsets c ho
    have hc := hcell c ho
    have hsi := hsites c ho
    have hw := hword c ho
    have hm : Fintype.card {v // v ∈ boundedSites G id R x c} =
        Fintype.card {v // v ∈ boundedSites H id R y c} := by rw [hsi]
    have key : ∀ {m n : ℕ}, m = n → ∀ (w : Fin m → Fin q) (w' : Fin n → Fin q),
        HEq w w' → ∀ (s : Finset (NamedPair V)) (a : NamedPair V) (ha : a ∈ s) (len : ℕ),
        readCellSlot s a ha len w = readCellSlot s a ha len w' := by
      intro m n h w w' hw s a ha len
      subst n
      cases hw
      rfl
    simp only [hs, hc]
    split_ifs with he
    · exact key hm _ _ hw _ e he _
    · rfl

end LocalDecompression.FiniteView
