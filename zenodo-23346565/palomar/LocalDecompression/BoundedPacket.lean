module

public import LocalDecompression.BoundedCells
public import LocalDecompression.Decoder

@[expose] public section

/-! Ordered packets of the existing bounded marker selector.

The reader uses the actual nonroot sites, the same increasing enumeration as
`Reduction.digitLayout`, and the same digit offset as `Reduction.wordsOfLabels`.
Its label dependence is bounded without assuming marker coverage. Coverage is
needed only to identify its packet with the existing global Voronoi codec.
All locality statements concern a fixed connected graph and a fixed vertex
order; they do not assert an operational decoder on changing graph topologies.
-/
namespace LocalDecompression.BoundedPacket
open MarkerLocality BoundedCells

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Read the nonroot labels of the bounded cell in increasing vertex order,
using exactly the digit offset of the existing marked codec. -/
noncomputable def boundedWord {q : ℕ} (hq : 0 < q) (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V) :
    Fin (Fintype.card {v // v ∈ boundedSites G id R labels c}) → Fin q :=
  fun i => Reduction.unmark hq
    (labels ((Fintype.orderIsoFinOfCardEq
      {v // v ∈ boundedSites G id R labels c} rfl) i).val)

/-- The actual base-q packet value, with its dependent length forgotten. -/
noncomputable def boundedValue {q : ℕ} (hq : 0 < q) (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V) : ℕ :=
  (finFunctionFinEquiv (boundedWord hq G id R labels c)).val

/-- The advice bit is extracted by the existing block codec. -/
noncomputable def boundedAdvice {q : ℕ} (hq : 0 < q) (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V) : Fin 2 :=
  blockAdvice (boundedWord hq G id R labels c)

private theorem value_congr {q m n : ℕ} (hcard : m = n)
    (w : Fin m → Fin q) (w' : Fin n → Fin q) (hword : HEq w w') :
    (finFunctionFinEquiv w).val = (finFunctionFinEquiv w').val := by
  subst n
  exact congrArg (fun z => (finFunctionFinEquiv z).val) (eq_of_heq hword)

private theorem advice_congr {q m n : ℕ} (hcard : m = n)
    (w : Fin m → Fin q) (w' : Fin n → Fin q) (hword : HEq w w') :
    blockAdvice w = blockAdvice w' := by
  subst n
  exact congrArg blockAdvice (eq_of_heq hword)

omit [Fintype V] in
/-- Finset subtypes and general predicate subtypes synthesize different
`Fintype` instances. Their increasing enumerations still coincide. -/
private theorem ordered_reader_congr_fintype {q : ℕ} (hq : 0 < q)
    (P Q : V → Prop) [fp : Fintype {v // P v}] [fq : Fintype {v // Q v}]
    (x y : V → Fin (q+1)) (hpred : P = Q)
    (hlabels : ∀ v, P v → x v = y v) :
    HEq (fun i : Fin (Fintype.card {v // P v}) =>
      Reduction.unmark hq (x ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).val))
      (fun i : Fin (Fintype.card {v // Q v}) =>
      Reduction.unmark hq (y ((Fintype.orderIsoFinOfCardEq {v // Q v} rfl) i).val)) := by
  subst Q
  have hf : fp = fq := Subsingleton.elim _ _
  subst fq
  apply heq_of_eq
  funext i
  exact congrArg (Reduction.unmark hq)
    (hlabels _ ((Fintype.orderIsoFinOfCardEq {v // P v} rfl) i).property)

/-- Arbitrary inputs agreeing within radius 2R have identical ordered
bounded packets. The heterogeneous equality accounts only for packet length. -/
theorem boundedWord_eq_of_label_agreement {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q+1)) (c : V)
    (hagree : ∀ v, G.dist c v ≤ 2*R → x v = y v) :
    HEq (boundedWord hq G id R x c) (boundedWord hq G id R y c) := by
  apply ordered_reader_congr_fintype
  · have hs := boundedSites_eq_of_marker_agreement G hconn id hinj R x y c
      (fun v hv => by rw [hagree v hv])
    exact funext (fun v => propext (by rw [hs]))
  · intro v hv
    have hd := boundedCell_radius G id hinj R x (Finset.mem_erase.mp hv).2
    exact hagree v (by omega)

/-- The packed natural value has the same coverage-free dependence bound. -/
theorem boundedValue_eq_of_label_agreement {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q+1)) (c : V)
    (hagree : ∀ v, G.dist c v ≤ 2*R → x v = y v) :
    boundedValue hq G id R x c = boundedValue hq G id R y c := by
  apply value_congr _ _ _
    (boundedWord_eq_of_label_agreement hq G hconn id hinj R x y c hagree)
  rw [boundedSites_eq_of_marker_agreement G hconn id hinj R x y c
    (fun v hv => by rw [hagree v hv])]

/-- The actual advice extractor is local even when vertices lack a nearby
marker and different inputs have different global root sets. -/
theorem boundedAdvice_eq_of_label_agreement {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (x y : V → Fin (q+1)) (c : V)
    (hagree : ∀ v, G.dist c v ≤ 2*R → x v = y v) :
    boundedAdvice hq G id R x c = boundedAdvice hq G id R y c := by
  apply advice_congr _ _ _
    (boundedWord_eq_of_label_agreement hq G hconn id hinj R x y c hagree)
  rw [boundedSites_eq_of_marker_agreement G hconn id hinj R x y c
    (fun v hv => by rw [hagree v hv])]

theorem boundedValue_local {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) :
    LocalAt G (2*R) (fun c => c) (boundedValue hq G id R) := by
  intro x y c hagree
  exact boundedValue_eq_of_label_agreement hq G hconn id hinj R x y c
    (fun v hv => hagree v ((within_iff_dist G hconn (2*R) c v).mpr hv))

theorem boundedAdvice_local {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) :
    LocalAt G (2*R) (fun c => c) (boundedAdvice hq G id R) := by
  intro x y c hagree
  exact boundedAdvice_eq_of_label_agreement hq G hconn id hinj R x y c
    (fun v hv => hagree v ((within_iff_dist G hconn (2*R) c v).mpr hv))

/-- A marker always owns itself, so it cannot be another root's data site.
Thus every selected nonroot label is a genuine nonzero marked digit. -/
theorem label_ne_zero_of_mem_boundedSites {q : ℕ} (G : SimpleGraph V)
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (R : ℕ) (labels : V → Fin (q+1)) {c v : V}
    (hv : v ∈ boundedSites G id R labels c) : labels v ≠ 0 := by
  obtain ⟨hne,howner⟩ := (mem_boundedSites G id R labels c v).mp hv
  intro hz
  have hself := (boundedOwner_self_iff_marker G hconn id hinj R labels v).mpr hz
  rw [howner] at hself
  exact hne (Option.some.inj hself).symm

/-- The empty positional word has the natural value zero, including when
the named vertex is a singleton cell or has no selected cell at all. -/
theorem boundedValue_eq_zero_of_empty {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V)
    (hempty : boundedSites G id R labels c = ∅) :
    boundedValue hq G id R labels c = 0 := by
  have hc : Fintype.card {v // v ∈ boundedSites G id R labels c} = 0 := by
    simp [hempty]
  have hv := (finFunctionFinEquiv (boundedWord hq G id R labels c)).isLt
  change boundedValue hq G id R labels c <
    q ^ Fintype.card {v // v ∈ boundedSites G id R labels c} at hv
  rw [hc, Nat.pow_zero] at hv
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hv)

theorem boundedAdvice_eq_zero_of_empty {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V)
    (hempty : boundedSites G id R labels c = ∅) :
    boundedAdvice hq G id R labels c = 0 := by
  apply Fin.ext
  change boundedValue hq G id R labels c % 2 = 0
  rw [boundedValue_eq_zero_of_empty hq G id R labels c hempty]

/-- A nonmarker cannot be the named owner of any data site. -/
theorem boundedSites_empty_of_nonmarker {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (c : V) (hc : labels c ≠ 0) :
    boundedSites G id R labels c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have ho := (mem_boundedSites G id R labels c v).mp hv
  have hm := ((boundedOwner_some_iff G id hinj R labels v c).mp ho.2).1.1
  exact hc (by simpa [recognizedRoots] using hm)

theorem boundedValue_eq_zero_of_nonmarker {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (c : V) (hc : labels c ≠ 0) :
    boundedValue hq G id R labels c = 0 :=
  boundedValue_eq_zero_of_empty hq G id R labels c
    (boundedSites_empty_of_nonmarker G id hinj R labels c hc)

theorem boundedAdvice_eq_zero_of_nonmarker {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (c : V) (hc : labels c ≠ 0) :
    boundedAdvice hq G id R labels c = 0 :=
  boundedAdvice_eq_zero_of_empty hq G id R labels c
    (boundedSites_empty_of_nonmarker G id hinj R labels c hc)

theorem boundedSites_empty_of_no_markers {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hmarkers : recognizedRoots labels = ∅) (c : V) :
    boundedSites G id R labels c = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have ho := (mem_boundedSites G id R labels c v).mp hv
  rw [boundedOwner_of_no_markers G id R labels hmarkers v] at ho
  cases ho.2

theorem boundedValue_eq_zero_of_no_markers {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hmarkers : recognizedRoots labels = ∅) (c : V) :
    boundedValue hq G id R labels c = 0 :=
  boundedValue_eq_zero_of_empty hq G id R labels c
    (boundedSites_empty_of_no_markers G id R labels hmarkers c)

theorem boundedAdvice_eq_zero_of_no_markers {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1))
    (hmarkers : recognizedRoots labels = ∅) (c : V) :
    boundedAdvice hq G id R labels c = 0 :=
  boundedAdvice_eq_zero_of_empty hq G id R labels c
    (boundedSites_empty_of_no_markers G id R labels hmarkers c)

/-- A selected cell consisting only of its root contains no storage digits. -/
theorem boundedSites_empty_of_singleton {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V)
    (hcell : boundedCell G id R labels c = {c}) :
    boundedSites G id R labels c = ∅ := by
  simp [boundedSites, hcell]

theorem boundedPacket_zero_of_singleton {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (id : V → ℕ) (R : ℕ) (labels : V → Fin (q+1)) (c : V)
    (hcell : boundedCell G id R labels c = {c}) :
    boundedValue hq G id R labels c = 0 ∧ boundedAdvice hq G id R labels c = 0 := by
  have hs := boundedSites_empty_of_singleton G id R labels c hcell
  exact ⟨boundedValue_eq_zero_of_empty hq G id R labels c hs,
    boundedAdvice_eq_zero_of_empty hq G id R labels c hs⟩

/-- Coverage identifies the bounded selector's actual sites with the
nonroot sites used by the existing global partition codec. -/
theorem mem_boundedSites_iff_sites_of_cover {q : ℕ} (G : SimpleGraph V)
    (id : V → ℕ) (hinj : Function.Injective id) (R : ℕ)
    (labels : V → Fin (q+1)) (hcover : MarkerCover G R labels)
    (hne : (recognizedRoots labels).Nonempty) (c : recognizedRoots labels) (v : V) :
    v ∈ boundedSites G id R labels c.val ↔
      rootOwner G (recognizedRoots labels) id hne v = c ∧ v ≠ c.val := by
  rw [mem_boundedSites, boundedOwner_eq_rootOwner G id hinj R labels hne v (hcover v)]
  simp only [Option.some.injEq, Subtype.ext_iff, and_comm]

/-- The complete bounded word agrees with `wordsOfLabels`, preserving the
existing layout's enumeration and marked-digit offset. -/
theorem boundedWord_eq_wordsOfLabels_of_cover {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (hcover : MarkerCover G R labels) (hne : (recognizedRoots labels).Nonempty)
    (c : recognizedRoots labels) :
    HEq (boundedWord hq G id R labels c.val)
      (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots labels) id hne) Subtype.val
          (rootOwner_root G hconn (recognizedRoots labels) id hne hinj)) labels c) := by
  change HEq
    (fun i : Fin (Fintype.card {v // v ∈ boundedSites G id R labels c.val}) =>
      Reduction.unmark hq (labels ((Fintype.orderIsoFinOfCardEq
        {v // v ∈ boundedSites G id R labels c.val} rfl) i).val))
    (fun i : Fin (Fintype.card
        (Sites (rootOwner G (recognizedRoots labels) id hne) Subtype.val c)) =>
      Reduction.unmark hq (labels ((Fintype.orderIsoFinOfCardEq
        (Sites (rootOwner G (recognizedRoots labels) id hne) Subtype.val c) rfl) i).val))
  exact ordered_reader_congr_fintype hq _ _ labels labels
    (funext (fun v => propext
      (mem_boundedSites_iff_sites_of_cover G id hinj R labels hcover hne c v)))
    (fun _ _ => rfl)

/-- The bounded advice bit is exactly the one used by the existing decoder
on covered marker inputs. -/
theorem boundedAdvice_eq_decodeAdvice_of_cover {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (hcover : MarkerCover G R labels) (hne : (recognizedRoots labels).Nonempty)
    (c : recognizedRoots labels) :
    boundedAdvice hq G id R labels c.val =
      Reduction.decodeAdvice (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G (recognizedRoots labels) id hne) Subtype.val
          (rootOwner_root G hconn (recognizedRoots labels) id hne hinj)) labels) c := by
  apply advice_congr _ _ _
    (boundedWord_eq_wordsOfLabels_of_cover hq G hconn id hinj R labels hcover hne c)
  exact Fintype.card_congr (Equiv.subtypeEquivRight
    (mem_boundedSites_iff_sites_of_cover G id hinj R labels hcover hne c))

/-- A specified root set may be used after proving it is exactly the set of
zero markers in the input. The packet order and layout remain unchanged. -/
theorem boundedAdvice_eq_decodeAdvice_of_roots {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) (hconn : G.Connected) (id : V → ℕ)
    (hinj : Function.Injective id) (R : ℕ) (labels : V → Fin (q+1))
    (hcover : MarkerCover G R labels) (roots : Finset V) (hne : roots.Nonempty)
    (hmarkers : recognizedRoots labels = roots) (c : roots) :
    boundedAdvice hq G id R labels c.val =
      Reduction.decodeAdvice (Reduction.wordsOfLabels hq
        (Reduction.digitLayout (rootOwner G roots id hne) Subtype.val
          (rootOwner_root G hconn roots id hne hinj)) labels) c := by
  subst roots
  exact boundedAdvice_eq_decodeAdvice_of_cover hq G hconn id hinj R labels hcover hne c

/-- On labels produced by the actual encoder, the bounded reader recovers
the advice that was encoded. The radius assumption concerns the selected
Voronoi cells; degree, balance, and capacity are the existing encoder inputs. -/
theorem boundedAdvice_vertexEncode {q : ℕ} (hq : 0 < q)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (R : ℕ)
    (hcell : ∀ v, G.dist (rootOwner G roots id hne v).val v ≤ R)
    (orientation : (roots → Fin 2) → GraphEdge G → Fin 2)
    (a : roots → Fin 2) (d : ℕ)
    (hdegree : ∀ v, (graphPresentation G).degree v ≤ d)
    (hbalanced : Reduction.BalancedAdvice (graphPresentation G)
      (rootOwner G roots id hne) orientation a)
    (capacity : ∀ c, 2 ^ (1 + payloadLength d
      (Reduction.partCell (rootOwner G roots id hne) c).card) ≤
      q ^ Fintype.card (Sites (rootOwner G roots id hne) Subtype.val c))
    (x : GraphEdge G → Fin 2) (c : roots) :
    boundedAdvice hq G id R
      (Reduction.vertexEncode (graphPresentation G) (rootOwner G roots id hne)
        Subtype.val (rootOwner_root G hconn roots id hne hinj)
        orientation a d q hdegree hbalanced capacity x) c.val = a c := by
  let labels := Reduction.vertexEncode (graphPresentation G) (rootOwner G roots id hne)
    Subtype.val (rootOwner_root G hconn roots id hne hinj)
    orientation a d q hdegree hbalanced capacity x
  have hmarkers : recognizedRoots labels = roots :=
    Reduction.vertexEncode_recognizedRoots G hconn roots id hne hinj
      orientation a d q hdegree hbalanced capacity x
  have hcover : MarkerCover G R labels := by
    intro v
    refine ⟨(rootOwner G roots id hne v).val, ?_, hcell v⟩
    have hm : (rootOwner G roots id hne v).val ∈ recognizedRoots labels := by
      rw [hmarkers]
      exact (rootOwner G roots id hne v).property
    simpa [recognizedRoots] using hm
  change boundedAdvice hq G id R labels c.val = a c
  rw [boundedAdvice_eq_decodeAdvice_of_roots hq G hconn id hinj R labels hcover
    roots hne hmarkers c]
  simp only [labels, Reduction.vertexEncode, Reduction.wordsOfLabels_labelsOfWords,
    Reduction.decodeAdvice_encode]

end LocalDecompression.BoundedPacket
