module
public import LocalDecompression.NamedDecoder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
@[expose] public section
namespace LocalDecompression.FiniteView
open Reduction MarkerLocality BoundedCells BoundedPacket
variable {V : Type*} [Fintype V] [LinearOrder V]

theorem pairOwner_some (G : SimpleGraph V) (roots : Finset V) (part : V → roots)
    (orientation : (roots → Fin 2) → GraphEdge G → Fin 2) (a : roots → Fin 2)
    (directions : NamedPair V → Fin 2) (e : GraphEdge G)
    (hdir : directions (graphPairEmbedding G e) = orientation a e) :
    pairOwner (fun v => some (part v).val) directions (graphPairEmbedding G e) =
      some (edgeOwner (graphPresentation G) part orientation a e).val := by
  change some (if directions (graphPairEmbedding G e) = 0 then (part e.val.1).val else (part e.val.2).val) = _
  rw [hdir]
  unfold edgeOwner
  split_ifs <;> rfl

theorem pairOwnedEdges_map (G : SimpleGraph V) [DecidableRel G.Adj]
    (roots : Finset V) (part : V → roots)
    (orientation : (roots → Fin 2) → GraphEdge G → Fin 2) (a : roots → Fin 2)
    (directions : NamedPair V → Fin 2)
    (hdir : ∀ e, directions (graphPairEmbedding G e) = orientation a e) (c : roots) :
    pairOwnedEdges G (fun v => some (part v).val) directions c.val =
      (ownedEdges (graphPresentation G) part orientation a c).map
        (graphPairEmbedding G).toEmbedding := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨he,ho⟩ := (mem_pairOwnedEdges _ _ _ _ _).mp hp
    let e : GraphEdge G := ⟨ofLex p,(mem_actualPairs G p).mp he⟩
    have heq : graphPairEmbedding G e = p := by rfl
    refine Finset.mem_map.mpr ⟨e,?_,heq⟩
    simp only [ownedEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    rw [← heq,pairOwner_some G roots part orientation a directions e (hdir e)] at ho
    exact Subtype.ext (Option.some.inj ho)
  · intro hp
    obtain ⟨e,he,rfl⟩ := Finset.mem_map.mp hp
    simp only [ownedEdges,Finset.mem_filter,Finset.mem_univ,true_and] at he
    apply (mem_pairOwnedEdges _ _ _ _ _).mpr
    refine ⟨?_,?_⟩
    · exact (mem_actualPairs _ _).mpr e.property
    · change pairOwner _ directions (graphPairEmbedding G e) = _
      rw [pairOwner_some G roots part orientation a directions e (hdir e),he]

theorem readCellSlot_heq {A : Type*} [LinearOrder A] {q m n : ℕ}
    (hcard : m = n) (w : Fin m → Fin q) (w' : Fin n → Fin q) (hw : HEq w w')
    (s : Finset A) (a : A) (ha : a ∈ s) (len : ℕ) :
    readCellSlot s a ha len w = readCellSlot s a ha len w' := by
  subst n
  cases hw
  rfl

/-- On every covered marker input, the bounded total pair decoder is exactly
 the existing decoder, when both are given the same computed direction bits. -/
theorem boundedPairDecode_eq_vertexDecode_of_cover {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R d : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    (hne : (recognizedRoots labels).Nonempty)
    (orientation : (recognizedRoots labels → Fin 2) → GraphEdge G → Fin 2)
    (directions : NamedPair V → Fin 2)
    (hdir : ∀ e, directions (graphPairEmbedding G e) = orientation
      (decodeAdvice (wordsOfLabels hq (digitLayout
        (rootOwner G (recognizedRoots labels) id hne) Subtype.val
        (rootOwner_root G hconn (recognizedRoots labels) id hne hinj)) labels)) e)
    (e : GraphEdge G) :
    boundedPairDecode hq G id R d labels directions (graphPairEmbedding G e) =
      vertexDecode (graphPresentation G) (rootOwner G (recognizedRoots labels) id hne)
        Subtype.val (rootOwner_root G hconn (recognizedRoots labels) id hne hinj)
        orientation d q hq labels e := by
  classical
  let roots := recognizedRoots labels
  let part := rootOwner G roots id hne
  let word := wordsOfLabels hq (digitLayout part Subtype.val
    (rootOwner_root G hconn roots id hne hinj)) labels
  let a := decodeAdvice word
  let c := edgeOwner (graphPresentation G) part orientation a e
  have hb : boundedOwner G id R labels = fun v => some (part v).val := by
    funext v
    exact boundedOwner_eq_rootOwner G id hinj R labels hne v (hcover v)
  have ho : pairOwner (boundedOwner G id R labels) directions (graphPairEmbedding G e) =
      some c.val := by
    rw [hb]
    exact pairOwner_some G roots part orientation a directions e (hdir e)
  have hs := pairOwnedEdges_map G roots part orientation a directions hdir c
  have hc : boundedCell G id R labels c.val = partCell part c := by
    ext v
    simp only [mem_boundedCell,hb,Option.some.injEq,mem_partCell,Subtype.ext_iff]
  have hw : HEq (boundedWord hq G id R labels c.val) (word c) :=
    boundedWord_eq_wordsOfLabels_of_cover hq G hconn id hinj R labels hcover hne c
  have hcard : Fintype.card {v // v ∈ boundedSites G id R labels c.val} =
      Fintype.card (Sites part Subtype.val c) :=
    Fintype.card_congr (Equiv.subtypeEquivRight
      (mem_boundedSites_iff_sites_of_cover G id hinj R labels hcover hne c))
  have he : graphPairEmbedding G e ∈ pairOwnedEdges G (boundedOwner G id R labels)
      directions c.val := by
    apply (mem_pairOwnedEdges _ _ _ _ _).mpr
    exact ⟨(mem_actualPairs _ _).mpr e.property,ho⟩
  simp only [boundedPairDecode,ho,dite_eq_left he]
  rw [hc]
  change readCellSlot _ _ _ _ (boundedWord hq G id R labels c.val) =
    readCellSlot (ownedEdges (graphPresentation G) part orientation a c) e _
      (payloadLength d (partCell part c).card) (word c)
  rw [readCellSlot_heq hcard _ _ hw]
  simp only [hb,hs]
  exact readCellSlot_map (graphPairEmbedding G) _ e _ _ (word c)


theorem boundedOwner_eq_rootOwner_of_roots {q : ℕ}
    (G : SimpleGraph V) (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    (roots : Finset V) (hne : roots.Nonempty) (hmarkers : recognizedRoots labels = roots)
    (v : V) : boundedOwner G id R labels v = some (rootOwner G roots id hne v).val := by
  subst roots
  exact boundedOwner_eq_rootOwner G id hinj R labels hne v (hcover v)

theorem boundedPairDecode_eq_vertexDecode_of_roots {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (id : V → ℕ) (hinj : Function.Injective id) (R d : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    (roots : Finset V) (hne : roots.Nonempty) (hmarkers : recognizedRoots labels = roots)
    (orientation : (roots → Fin 2) → GraphEdge G → Fin 2)
    (directions : NamedPair V → Fin 2)
    (hdir : ∀ e, directions (graphPairEmbedding G e) = orientation
      (decodeAdvice (wordsOfLabels hq (digitLayout
        (rootOwner G roots id hne) Subtype.val
        (rootOwner_root G hconn roots id hne hinj)) labels)) e)
    (e : GraphEdge G) :
    boundedPairDecode hq G id R d labels directions (graphPairEmbedding G e) =
      vertexDecode (graphPresentation G) (rootOwner G roots id hne)
        Subtype.val (rootOwner_root G hconn roots id hne hinj)
        orientation d q hq labels e := by
  subst roots
  exact boundedPairDecode_eq_vertexDecode_of_cover hq G hconn id hinj R d
    labels hcover hne orientation directions hdir e

/-- The bounded pair decoder reads the actual old encoder, including its
same lexicographic edge ranks. The direction premise is discharged separately
by the uniform residual-graph orientation construction. -/
theorem boundedPairDecode_vertexEncode {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (R : ℕ)
    (hcell : ∀ v, G.dist (rootOwner G roots id hne v).val v ≤ R)
    (orientation : (roots → Fin 2) → GraphEdge G → Fin 2)
    (a : roots → Fin 2) (d : ℕ)
    (hdegree : ∀ v, (graphPresentation G).degree v ≤ d)
    (hbalanced : BalancedAdvice (graphPresentation G)
      (rootOwner G roots id hne) orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d
      (partCell (rootOwner G roots id hne) c).card) ≤
      q ^ Fintype.card (Sites (rootOwner G roots id hne) Subtype.val c))
    (x : GraphEdge G → Fin 2) (directions : NamedPair V → Fin 2)
    (hdir : ∀ e, directions (graphPairEmbedding G e) = orientation a e)
    (e : GraphEdge G) :
    boundedPairDecode hq G id R d
      (vertexEncode (graphPresentation G) (rootOwner G roots id hne)
        Subtype.val (rootOwner_root G hconn roots id hne hinj)
        orientation a d q hdegree hbalanced capacity x) directions (graphPairEmbedding G e) = x e := by
  let labels := vertexEncode (graphPresentation G) (rootOwner G roots id hne)
    Subtype.val (rootOwner_root G hconn roots id hne hinj)
    orientation a d q hdegree hbalanced capacity x
  have hmarkers : recognizedRoots labels = roots :=
    vertexEncode_recognizedRoots G hconn roots id hne hinj
      orientation a d q hdegree hbalanced capacity x
  have hcover : MarkerCover G R labels := by
    intro v
    refine ⟨(rootOwner G roots id hne v).val, ?_, hcell v⟩
    have hm : (rootOwner G roots id hne v).val ∈ recognizedRoots labels := by
      rw [hmarkers]
      exact (rootOwner G roots id hne v).property
    simpa [recognizedRoots] using hm
  change boundedPairDecode hq G id R d labels directions (graphPairEmbedding G e) = x e
  rw [boundedPairDecode_eq_vertexDecode_of_roots hq G hconn id hinj R d labels
    hcover roots hne hmarkers orientation directions ?_ e]
  · exact congrFun (vertexDecode_encode (graphPresentation G) (rootOwner G roots id hne)
      Subtype.val (rootOwner_root G hconn roots id hne hinj)
      orientation a d q hq hdegree hbalanced capacity x) e
  · intro e'
    simpa only [labels,vertexEncode,wordsOfLabels_labelsOfWords,decodeAdvice_encode] using hdir e'

end LocalDecompression.FiniteView
