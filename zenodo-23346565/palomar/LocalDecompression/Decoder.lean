module

public import LocalDecompression.Main

@[expose] public section

/-! Reading the actual markers and the final payload decoder.

The marker decoder reconstructs its roots and Voronoi cells from the input
labels. Its roundtrip is a statement on encoded inputs. Locality statements
below specify their domain: unrestricted invalid marker patterns need not
have bounded-radius cells.
-/
namespace LocalDecompression
namespace Reduction

variable {V E C : Type*} [Fintype V] [LinearOrder V]
  [Fintype E] [LinearOrder E] [DecidableEq C]

omit [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
  [DecidableEq C] in
/-- An edge can only be owned by one of its endpoint cells. -/
theorem edgeOwner_endpoint (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a : C → Fin 2) (e : E) :
    edgeOwner G part orientation a e = part (G.left e) ∨
      edgeOwner G part orientation a e = part (G.right e) := by
  unfold edgeOwner
  split_ifs <;> simp

omit [Fintype V] [LinearOrder V] [LinearOrder E] in
/-- Orientations of edges outside a cell cannot change its owned-edge set. -/
theorem ownedEdges_congr_incident (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (a b : C → Fin 2) (c : C)
    (hincident : ∀ e, part (G.left e) = c ∨ part (G.right e) = c →
      orientation a e = orientation b e) :
    ownedEdges G part orientation a c = ownedEdges G part orientation b c := by
  ext e
  simp only [ownedEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : part (G.left e) = c ∨ part (G.right e) = c
  · simp only [edgeOwner, hincident e hi]
  · have hl : part (G.left e) ≠ c := fun h => hi (Or.inl h)
    have hr : part (G.right e) ≠ c := fun h => hi (Or.inr h)
    simp only [edgeOwner]
    split_ifs <;> simp [hl, hr]

omit [LinearOrder V] in
/-- The final lookup depends on the selected owner's packet and owned-edge
set. Equality of unrelated orientations or packets is unnecessary. -/
theorem decodeUsingAdvice_congr (G : EdgePresentation V E) (part : V → C)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ) (sites : C → ℕ)
    (a b : C → Fin 2) (word word' : Words q sites) (e : E)
    (ho : edgeOwner G part orientation a e = edgeOwner G part orientation b e)
    (hs : ownedEdges G part orientation a (edgeOwner G part orientation a e) =
      ownedEdges G part orientation b (edgeOwner G part orientation a e))
    (hw : word (edgeOwner G part orientation a e) =
      word' (edgeOwner G part orientation a e)) :
    decodeUsingAdvice G part orientation d q sites a word e =
      decodeUsingAdvice G part orientation d q sites b word' e := by
  unfold decodeUsingAdvice
  simp only [← ho, ← hs]
  congr 1
  · exact congrArg sites ho
  · have hd : ∀ c c' : C, c = c' → HEq (word' c) (word' c') := by
      intro c c' h
      subst c'
      rfl
    exact (heq_of_eq hw).trans (hd _ _ ho)

/-- Only the two possible owner's cells and their incident-edge orientations
can affect the final edge lookup. This includes the slot-index computation. -/
theorem vertexDecode_congr_incident (G : EdgePresentation V E) (part : V → C)
    (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ) (hq : 0 < q)
    (x y : V → Fin (q + 1)) (e : E)
    (hori : ∀ c, c = part (G.left e) ∨ c = part (G.right e) →
      ∀ f, part (G.left f) = c ∨ part (G.right f) = c →
      orientation (decodeAdvice (wordsOfLabels hq (digitLayout part root hroot) x)) f =
      orientation (decodeAdvice (wordsOfLabels hq (digitLayout part root hroot) y)) f)
    (hlabels : ∀ c, c = part (G.left e) ∨ c = part (G.right e) →
      ∀ v, part v = c → x v = y v) :
    vertexDecode G part root hroot orientation d q hq x e =
      vertexDecode G part root hroot orientation d q hq y e := by
  unfold vertexDecode decodeWords
  apply decodeUsingAdvice_congr
  · unfold edgeOwner
    rw [hori (part (G.left e)) (Or.inl rfl) e (Or.inl rfl)]
  · apply ownedEdges_congr_incident
    exact hori _ (edgeOwner_endpoint G part orientation _ e)
  · apply packet_reader_fiber_local
    exact hlabels _ (edgeOwner_endpoint G part orientation _ e)

omit [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
  [DecidableEq C] in
/-- Either endpoint-cell root is at distance at most A+1 from an edge's left
endpoint when each cell has radius A in the actual graph. -/
theorem endpoint_cell_distance (G : EdgePresentation V E)
    (physical : SimpleGraph V) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (A : ℕ)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A)
    (hphysical : ∀ e, physical.Adj (G.left e) (G.right e))
    (e : E) (c : C) (hc : c = part (G.left e) ∨ c = part (G.right e)) :
    physical.dist (G.left e) (root c) ≤ A + 1 := by
  rcases hc with rfl | rfl
  · have h := hcell (G.left e)
    rw [SimpleGraph.dist_comm] at h
    omega
  · have h := hcell (G.right e)
    rw [SimpleGraph.dist_comm] at h
    have he := SimpleGraph.dist_eq_one_iff_adj.mpr (hphysical e)
    have ht := hconn.dist_triangle (u := G.left e) (v := G.right e)
      (w := root (part (G.right e)))
    omega

omit [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
  [DecidableEq C] in
/-- The roots anchoring an incident edge and its incident cell are close.
This is the extra neighborhood needed to recompute all payload-slot ranks. -/
theorem incident_cell_anchor_distance (G : EdgePresentation V E)
    (physical : SimpleGraph V) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (A : ℕ)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A)
    (hphysical : ∀ e, physical.Adj (G.left e) (G.right e))
    (f : E) (c : C) (hc : part (G.left f) = c ∨ part (G.right f) = c) :
    physical.dist (root c) (root (part (G.left f))) ≤ 2 * A + 1 := by
  have h := endpoint_cell_distance G physical hconn part root A hcell hphysical f c
    (hc.imp Eq.symm Eq.symm)
  have hl := hcell (G.left f)
  have ht := hconn.dist_triangle (u := root (part (G.left f))) (v := G.left f)
    (w := root c)
  rw [SimpleGraph.dist_comm]
  omega

/-- The complete fixed-partition vertex decoder is local, including ownership
and slot recomputation. Its only oracle premise concerns orientation outputs. -/
theorem vertexDecode_local_of_extracted_orientation (G : EdgePresentation V E)
    (physical : SimpleGraph V) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ) (hq : 0 < q) (A R : ℕ)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A)
    (hphysical : ∀ e, physical.Adj (G.left e) (G.right e))
    (horientation : LocalAt physical R (root ∘ part ∘ G.left)
      (fun labels => orientation
        (decodeAdvice (wordsOfLabels hq (digitLayout part root hroot) labels)))) :
    LocalAt physical (R + 3 * A + 2) G.left
      (vertexDecode G part root hroot orientation d q hq) := by
  intro x y e hagree
  apply vertexDecode_congr_incident
  · intro c hc f hf
    apply horientation x y f
    intro v hv
    apply hagree v
    have h₁ := endpoint_cell_distance G physical hconn part root A hcell hphysical e c hc
    have h₂ := incident_cell_anchor_distance G physical hconn part root A hcell hphysical f c hf
    have h₃ := (within_iff_dist physical hconn R _ v).mp hv
    have ht₁ := hconn.dist_triangle (u := G.left e) (v := root c)
      (w := root (part (G.left f)))
    have ht₂ := hconn.dist_triangle (u := G.left e) (v := root (part (G.left f))) (w := v)
    apply (within_iff_dist physical hconn _ _ _).mpr
    dsimp only [Function.comp_apply] at h₃
    omega
  · intro c hc v hv
    apply hagree v
    have h₁ := endpoint_cell_distance G physical hconn part root A hcell hphysical e c hc
    have h₂ := hcell v
    rw [hv] at h₂
    have ht := hconn.dist_triangle (u := G.left e) (v := root c) (w := v)
    apply (within_iff_dist physical hconn _ _ _).mpr
    omega

/-- A local orientation oracle on the quotient gives a local final decoder
on the physical graph. No locality or recovery of the final output is assumed. -/
theorem vertexDecode_local (G : EdgePresentation V E)
    (physical : SimpleGraph V) (quotient : SimpleGraph C) (hconn : physical.Connected)
    (part : V → C) (root : C → V) (hroot : ∀ c, part (root c) = c)
    (orientation : (C → Fin 2) → E → Fin 2) (d q : ℕ) (hq : 0 < q) (A T L : ℕ)
    (hcell : ∀ v, physical.dist (root (part v)) v ≤ A)
    (hphysical : ∀ e, physical.Adj (G.left e) (G.right e))
    (horacle : LocalAt quotient T (part ∘ G.left) orientation)
    (hedge : ∀ c c', quotient.Adj c c' → physical.dist (root c) (root c') ≤ L) :
    LocalAt physical (L * T + 4 * A + 2) G.left
      (vertexDecode G part root hroot orientation d q hq) := by
  have h := vertexDecode_local_of_extracted_orientation G physical hconn part root hroot
    orientation d q hq A (L * T + A) hcell hphysical
    (extracted_orientation_local hq physical quotient hconn part root hroot
      (part ∘ G.left) A T L orientation hcell horacle hedge)
  convert h using 1
  congr 1
  omega

omit [Fintype V] [LinearOrder V] [Fintype E] [LinearOrder E]
  [DecidableEq C] in
/-- One additional physical hop lets the other endpoint read any edge output
that is local at the first endpoint. -/
theorem localAt_right_endpoint {Input Output : Type*} (G : EdgePresentation V E)
    (physical : SimpleGraph V) (R : ℕ)
    (hphysical : ∀ e, physical.Adj (G.left e) (G.right e))
    (decode : (V → Input) → E → Output) (hlocal : LocalAt physical R G.left decode) :
    LocalAt physical (R + 1) G.right decode := by
  intro x y e hagree
  apply hlocal x y e
  intro v hv
  apply hagree v
  obtain ⟨p, hp⟩ := hv
  exact ⟨p.cons (hphysical e).symm, by simp only [SimpleGraph.Walk.length_cons]; omega⟩

/-- Root recovery for the actual vertex encoder, with no marker premise left
to the caller. -/
theorem vertexEncode_recognizedRoots
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id)
    (orientation : (roots → Fin 2) → GraphEdge physical → Fin 2)
    (a : roots → Fin 2) (d q : ℕ)
    (hdegree : ∀ v, (graphPresentation physical).degree v ≤ d)
    (hbalanced : BalancedAdvice (graphPresentation physical)
      (rootOwner physical roots id hne) orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d
      (partCell (rootOwner physical roots id hne) c).card) ≤
      q ^ Fintype.card (Sites (rootOwner physical roots id hne) Subtype.val c))
    (x : GraphEdge physical → Fin 2) :
    recognizedRoots (vertexEncode (graphPresentation physical)
      (rootOwner physical roots id hne) Subtype.val
      (rootOwner_root physical hconn roots id hne hinj)
      orientation a d q hdegree hbalanced capacity x) = roots := by
  apply marker_root_recovery physical hconn roots id hne hinj
  intro v
  exact (vertexEncode_zero_iff _ _ _ _ _ _ _ _ _ _ _ _ v).trans eq_comm

/-- Decode with the Voronoi partition of a specified nonempty marker set. -/
noncomputable def decodeForRoots
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (id : V → ℕ) (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge physical → Fin 2)
    (d q : ℕ) (hq : 0 < q) (labels : V → Fin (q + 1))
    (roots : Finset V) (hne : roots.Nonempty) : GraphEdge physical → Fin 2 :=
  vertexDecode (graphPresentation physical) (rootOwner physical roots id hne) Subtype.val
    (rootOwner_root physical hconn roots id hne hinj) (orientation roots hne) d q hq labels

/-- A total decoder whose partition is read from zero markers in its input.
The no-marker branch is an arbitrary invalid-input fallback. -/
noncomputable def markerDecode
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (id : V → ℕ) (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge physical → Fin 2)
    (d q : ℕ) (hq : 0 < q) (labels : V → Fin (q + 1)) : GraphEdge physical → Fin 2 :=
  if hne : (recognizedRoots labels).Nonempty then
    decodeForRoots physical hconn id hinj orientation d q hq labels (recognizedRoots labels) hne
  else fun _ => 0

/-- On a label assignment with the specified markers, the dynamic decoder
is exactly the decoder for the recovered graph partition. -/
theorem markerDecode_eq_decodeForRoots
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (id : V → ℕ) (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge physical → Fin 2)
    (d q : ℕ) (hq : 0 < q) (labels : V → Fin (q + 1))
    (roots : Finset V) (hne : roots.Nonempty) (hmarkers : recognizedRoots labels = roots) :
    markerDecode physical hconn id hinj orientation d q hq labels =
      decodeForRoots physical hconn id hinj orientation d q hq labels roots hne := by
  unfold markerDecode
  rw [hmarkers]
  simp only [dite_eq_left hne]

/-- The actual marker-reading decoder is local on each fixed valid marker
domain. The two explicit marker equalities are domain restrictions, not
unrestricted locality assertions for arbitrary invalid label assignments. -/
theorem markerDecode_local_on_markers
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge physical → Fin 2)
    (d q : ℕ) (hq : 0 < q) (quotient : SimpleGraph roots) (A T L : ℕ)
    (hcell : ∀ v, physical.dist (rootOwner physical roots id hne v).val v ≤ A)
    (horacle : LocalAt quotient T
      (rootOwner physical roots id hne ∘ (graphPresentation physical).left)
      (orientation roots hne))
    (hedge : ∀ c c' : roots, quotient.Adj c c' → physical.dist c.val c'.val ≤ L)
    (x y : V → Fin (q + 1))
    (hx : recognizedRoots x = roots) (hy : recognizedRoots y = roots)
    (e : GraphEdge physical)
    (hagree : ∀ v, Within physical (L * T + 4 * A + 2)
      ((graphPresentation physical).left e) v → x v = y v) :
    markerDecode physical hconn id hinj orientation d q hq x e =
      markerDecode physical hconn id hinj orientation d q hq y e := by
  rw [markerDecode_eq_decodeForRoots physical hconn id hinj orientation d q hq x roots hne hx,
    markerDecode_eq_decodeForRoots physical hconn id hinj orientation d q hq y roots hne hy]
  exact vertexDecode_local (graphPresentation physical) physical quotient hconn
    (rootOwner physical roots id hne) Subtype.val
    (rootOwner_root physical hconn roots id hne hinj)
    (orientation roots hne) d q hq A T L hcell
    (graphPresentation_adj physical) horacle hedge x y e hagree

/-- The marker-reading decoder recovers every edge bit. It is not passed the
encoder's chosen root set or partition. -/
theorem markerDecode_vertexEncode
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id)
    (orientation : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → GraphEdge physical → Fin 2)
    (a : roots → Fin 2) (d q : ℕ) (hq : 0 < q)
    (hdegree : ∀ v, (graphPresentation physical).degree v ≤ d)
    (hbalanced : BalancedAdvice (graphPresentation physical)
      (rootOwner physical roots id hne) (orientation roots hne) a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d
      (partCell (rootOwner physical roots id hne) c).card) ≤
      q ^ Fintype.card (Sites (rootOwner physical roots id hne) Subtype.val c))
    (x : GraphEdge physical → Fin 2) :
    markerDecode physical hconn id hinj orientation d q hq
      (vertexEncode (graphPresentation physical)
        (rootOwner physical roots id hne) Subtype.val
        (rootOwner_root physical hconn roots id hne hinj)
        (orientation roots hne) a d q hdegree hbalanced capacity x) = x := by
  unfold markerDecode
  rw [vertexEncode_recognizedRoots physical hconn roots id hne hinj]
  simp only [dite_eq_left hne]
  exact vertexDecode_encode _ _ _ _ _ _ _ _ _ _ _ _ x

end Reduction
end LocalDecompression
