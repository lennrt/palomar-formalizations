module

public import LocalDecompression.Decoder
public import LocalDecompression.QuotientOrientation

@[expose] public section

/-! The graph-native reconstruction reduction, including quotient pairing.

The graph determines both its canonical original edges and its Voronoi metric.
The decoder reads roots from zero markers. The remaining external input is a
one-bit orientation decoder for the actual residual simple quotient, with the
needed outdegree bound and, for locality, its label-dependence radius. The
published orientation algorithm is not introduced as a Lean axiom.
-/
namespace LocalDecompression
namespace Reduction

variable {V : Type*} [Fintype V] [LinearOrder V]

/-- Lift a family of simple-quotient decoders after the actual marker set has
been read. No chosen root set is retained by the resulting marker decoder. -/
noncomputable def liftedGraphOrientation
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (id : V → ℕ)
    (residual : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → QuotientOrientation.CellPair roots → Fin 2)
    (roots : Finset V) (hne : roots.Nonempty) :
    (roots → Fin 2) → GraphEdge physical → Fin 2 :=
  QuotientOrientation.liftedOrientation (graphPresentation physical)
    (rootOwner physical roots id hne) (residual roots hne)

/-- Numeric storage capacity of actual graph cells follows from separation
and component size. It is independent of any edge labels or decoder. -/
theorem graph_cell_capacity
    (physical : SimpleGraph V) (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (k : ℕ) (hk : 2 ≤ k)
    (hsep : Separated physical (16 * (k + 1)) roots)
    (hlarge : 16 * (k + 1) < Fintype.card V) :
    ∀ c, 2 ^ (1 + payloadLength (2 * k - 1)
      (partCell (rootOwner physical roots id hne) c).card) ≤
      (2 ^ k - 1) ^ Fintype.card (Sites (rootOwner physical roots id hne) Subtype.val c) := by
  apply odd_cell_capacity (rootOwner physical roots id hne) Subtype.val
    (rootOwner_root physical hconn roots id hne hinj) k hk
  intro c
  have hf := fiber_card_eq_cell physical roots id hne hinj c
  rw [Fintype.card_subtype] at hf
  change 16 * (k + 1) + 1 ≤ (partCell (rootOwner physical roots id hne) c).card
  have hc : (partCell (rootOwner physical roots id hne) c).card =
      (cell physical roots id c.val).card := hf
  rw [hc]
  exact cell_card_lower physical hconn roots id _ hsep hlarge c.property

/-- Graph-native compression with actual marker recovery and canonical
parallel-edge pairing. The only orientation bound assumed is on the residual
simple quotient; the boundary ownership bound is proved by the lift. -/
theorem graph_marker_reconstruction
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (k : ℕ) (hk : 2 ≤ k)
    (hsep : Separated physical (16 * (k + 1)) roots)
    (hlarge : 16 * (k + 1) < Fintype.card V)
    (hdegree : ∀ v, physical.degree v ≤ 2 * k - 1)
    (residual : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → QuotientOrientation.CellPair roots → Fin 2)
    (a : roots → Fin 2)
    (hresidual : QuotientOrientation.ResidualBalanced (graphPresentation physical)
      (rootOwner physical roots id hne) (residual roots hne) a) :
    ∃ encode : (GraphEdge physical → Fin 2) → (V → Fin ((2 ^ k - 1) + 1)),
      ∀ x, markerDecode physical hconn id hinj (liftedGraphOrientation physical id residual)
          (2 * k - 1) (2 ^ k - 1)
          (by have : 1 < 2 ^ k := Nat.one_lt_pow (by omega) (by omega); omega)
          (encode x) = x ∧ recognizedRoots (encode x) = roots := by
  let orientation := liftedGraphOrientation physical id residual
  have hdegree' : ∀ v, (graphPresentation physical).degree v ≤ 2 * k - 1 :=
    fun v => (graphPresentation_degree physical v).trans_le (hdegree v)
  have hb : BalancedAdvice (graphPresentation physical)
      (rootOwner physical roots id hne) (orientation roots hne) a := by
    dsimp only [orientation, liftedGraphOrientation]
    convert QuotientOrientation.lifted_balanced_of_simpleGraph _ _ _ _ hresidual using 1
  have hc := graph_cell_capacity physical hconn roots id hne hinj k hk hsep hlarge
  refine ⟨vertexEncode (graphPresentation physical) (rootOwner physical roots id hne)
    Subtype.val (rootOwner_root physical hconn roots id hne hinj)
    (orientation roots hne) a (2 * k - 1) (2 ^ k - 1) hdegree' hb hc, ?_⟩
  intro x
  constructor
  · exact markerDecode_vertexEncode physical hconn roots id hne hinj orientation
      a _ _ _ hdegree' hb hc x
  · exact vertexEncode_recognizedRoots physical hconn roots id hne hinj
      (orientation roots hne) a _ _ hdegree' hb hc x

/-- Label-locality of the full marker decoder on one fixed marker domain,
now derived directly from locality on the actual residual simple quotient.
Topology and marker pattern are fixed; cross-topology or cross-marker-pattern
LOCAL execution is not asserted by this extensional theorem. -/
theorem graph_marker_decoder_local
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id)
    (residual : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → QuotientOrientation.CellPair roots → Fin 2)
    (d q : ℕ) (hq : 0 < q) (r T : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, physical.dist c v ≤ 2 * r)
    (horacle : LocalAt
      (QuotientOrientation.residualGraph (graphPresentation physical)
        (rootOwner physical roots id hne)) T
      (fun p : QuotientOrientation.CellPair roots => p.val.1) (residual roots hne))
    (x y : V → Fin (q + 1))
    (hx : recognizedRoots x = roots) (hy : recognizedRoots y = roots)
    (e : GraphEdge physical)
    (hagree : ∀ v, Within physical ((4 * r + 1) * (T + 1) + 8 * r + 2)
      ((graphPresentation physical).left e) v → x v = y v) :
    markerDecode physical hconn id hinj (liftedGraphOrientation physical id residual) d q hq x e =
      markerDecode physical hconn id hinj (liftedGraphOrientation physical id residual) d q hq y e := by
  have hcell : ∀ v, physical.dist (rootOwner physical roots id hne v).val v ≤ 2 * r := by
    intro v
    exact voronoi_radius physical roots id r hcover (owner_spec physical roots id hne v)
  apply markerDecode_local_on_markers physical hconn roots id hne hinj
    (liftedGraphOrientation physical id residual) d q hq
    (QuotientOrientation.residualGraph (graphPresentation physical)
      (rootOwner physical roots id hne)) (2 * r) (T + 1) (4 * r + 1) hcell
    (QuotientOrientation.liftedOrientation_local _ _ _ T horacle)
    (fun _ _ h => QuotientOrientation.residual_root_adj_dist physical hconn
      (graphPresentation physical) (graphPresentation_adj physical)
      roots id hne hinj r hcover h) x y hx hy e
  simpa only [← Nat.mul_assoc, Nat.reduceMul] using hagree

/-- The other endpoint reads the same reconstructed edge bit after one
additional physical round, on the same explicit marker domain. -/
theorem graph_marker_decoder_local_right
    (physical : SimpleGraph V) [DecidableRel physical.Adj] (hconn : physical.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id)
    (residual : (roots : Finset V) → roots.Nonempty →
      (roots → Fin 2) → QuotientOrientation.CellPair roots → Fin 2)
    (d q : ℕ) (hq : 0 < q) (r T : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, physical.dist c v ≤ 2 * r)
    (horacle : LocalAt
      (QuotientOrientation.residualGraph (graphPresentation physical)
        (rootOwner physical roots id hne)) T
      (fun p : QuotientOrientation.CellPair roots => p.val.1) (residual roots hne))
    (x y : V → Fin (q + 1))
    (hx : recognizedRoots x = roots) (hy : recognizedRoots y = roots)
    (e : GraphEdge physical)
    (hagree : ∀ v, Within physical ((4 * r + 1) * (T + 1) + 8 * r + 2 + 1)
      ((graphPresentation physical).right e) v → x v = y v) :
    markerDecode physical hconn id hinj (liftedGraphOrientation physical id residual) d q hq x e =
      markerDecode physical hconn id hinj (liftedGraphOrientation physical id residual) d q hq y e := by
  apply graph_marker_decoder_local physical hconn roots id hne hinj residual
    d q hq r T hcover horacle x y hx hy e
  intro v hv
  apply hagree v
  obtain ⟨p, hp⟩ := hv
  exact ⟨p.cons (graphPresentation_adj physical e).symm,
    by simp only [SimpleGraph.Walk.length_cons]; omega⟩

end Reduction
end LocalDecompression
