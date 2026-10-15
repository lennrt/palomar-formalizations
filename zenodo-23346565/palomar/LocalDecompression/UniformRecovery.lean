module
public import LocalDecompression.OrientationOracle
public import LocalDecompression.NamedCorrectness
public import LocalDecompression.GraphReduction
public import LocalDecompression.UniformDirections
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
@[expose] public section
namespace LocalDecompression.FiniteView
open Reduction MarkerLocality BoundedCells BoundedPacket QuotientOrientation
open LocalDecompression.OrientationOracle

def codecRadius (k : ℕ) : ℕ := 2 * (16 * (k+1))
def codecDegree (k : ℕ) : ℕ := (2*k-1) * (2*k) ^ codecRadius k
def canonicalId {n : ℕ} (v : Fin n) : ℕ := v.val+1

/-- The explicit degree bound and exact-size padding produce one fixed advice
assignment for a separated covering partition, before any payload is chosen. -/
theorem exists_uniform_partition_advice
    (F : Rule) (T : ℕ → ℕ) (hgood : GoodOneBitOracle F T)
    (k n : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdegree : ∀ v, G.degree v ≤ 2*k-1)
    (hlarge : 16*(k+1) < n) :
    ∃ (roots : Finset (Fin n)) (hne : roots.Nonempty),
      Separated G (16*(k+1)) roots ∧
      (∀ v, G.dist (rootOwner G roots canonicalId hne v).val v ≤ codecRadius k) ∧
      ∃ a : roots → Fin 2,
        BalancedAdvice (graphPresentation G) (rootOwner G roots canonicalId hne)
          (liftedOrientation (graphPresentation G) (rootOwner G roots canonicalId hne)
            (pairRule F (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k))
              (residualGraph (graphPresentation G) (rootOwner G roots canonicalId hne))
              (canonicalId ∘ Subtype.val))) a := by
  have hinj : Function.Injective (canonicalId (n := n)) := by
    intro v w h
    apply Fin.ext
    simpa only [canonicalId,Nat.add_right_cancel_iff] using h
  obtain ⟨roots,hne,hsep,hcover,hunique,hsizes,hradius,hpaths⟩ :=
    exists_large_component_partition G hconn canonicalId hinj
      (16*(k+1)) (2*k-1) hdegree (by simpa using hlarge)
  let part := rootOwner G roots canonicalId hne
  have hcell : ∀ v, G.dist (part v).val v ≤ codecRadius k := by
    intro v
    exact hradius _ _ (owner_spec G roots canonicalId hne v)
  have hpres : ∀ v, (graphPresentation G).degree v ≤ 2*k-1 :=
    fun v => (graphPresentation_degree G v).trans_le (hdegree v)
  have hbound : ∀ c : roots, (residualGraph (graphPresentation G) part).degree c ≤ codecDegree k := by
    intro c
    have hb := residual_degree_bound (graphPresentation G) part (2*k-1) hpres c
    have hc : (partCell part c).card = (cell G roots canonicalId c.val).card := by
      have hf := fiber_card_eq_cell G roots canonicalId hne hinj c
      simpa only [Fintype.card_subtype,partCell,part] using hf
    simp only [partCell,part] at hb hc
    rw [hc] at hb
    have hs := (hsizes c.val c.property).2
    have hbase : 2*k-1+1 = 2*k := by omega
    rw [hbase] at hs
    exact hb.trans (Nat.mul_le_mul_left _ hs)
  obtain ⟨a,ha⟩ := exists_good_root_advice F T hgood roots
    (residualGraph (graphPresentation G) part) canonicalId 1 (codecDegree k) (by omega)
    hinj (fun v => by simp [canonicalId])
    (fun v => by simp only [Fintype.card_fin,pow_one,canonicalId]; omega) hbound
  have ha' : ∀ v : roots,
      2 * outdegree F (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k))
        (residualGraph (graphPresentation G) part) (canonicalId ∘ Subtype.val) a v ≤
      (residualGraph (graphPresentation G) part).degree v + 1 := by
    intro v
    simpa only [Fintype.card_fin] using ha v
  have hres := residualBalanced_of_outdegree F (n+codecDegree k+1) (codecDegree k) 1
    (T (codecDegree k)) (graphPresentation G) part (canonicalId ∘ Subtype.val) a ha'
  have hb := lifted_balanced_of_simpleGraph (graphPresentation G) part
    (pairRule F (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k))
      (residualGraph (graphPresentation G) part) (canonicalId ∘ Subtype.val)) a hres
  refine ⟨roots,hne,hsep,hcell,a,?_⟩
  intro c
  have hc := hb c
  simpa only [BalancedAdvice,outgoingEdges,ownedEdges,edgeOwner,partCell,part] using hc


theorem codecAlphabet_pos (k : ℕ) (hk : 2 ≤ k) : 0 < 2^k-1 := by
  have h : 1 < 2^k := Nat.one_lt_pow (by omega) (by omega)
  omega

/-- A single explicitly specified bounded decoder reconstructs every edge
labelling of each sufficiently large connected odd-degree-bounded graph. The
external assumption supplies only a total finite-view orientation rule with
good advice; the encoder, exact packet order, markers and recovery are proved. -/
theorem uniform_reconstruction
    (F : Rule) (T : ℕ → ℕ) (hgood : GoodOneBitOracle F T)
    (k n : ℕ) (hk : 2 ≤ k) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hdegree : ∀ v, G.degree v ≤ 2*k-1)
    (hlarge : 16*(k+1) < n) :
    ∃ encode : (GraphEdge G → Fin 2) → (Fin n → Fin ((2^k-1)+1)),
      ∀ x e, uniformDecode (codecAlphabet_pos k hk) F
        (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k))
        G canonicalId (codecRadius k) (2*k-1) (encode x) (graphPairEmbedding G e) = x e := by
  have hinj : Function.Injective (canonicalId (n := n)) := by
    intro v w h
    apply Fin.ext
    simpa only [canonicalId,Nat.add_right_cancel_iff] using h
  obtain ⟨roots,hne,hsep,hcell,a,hbalanced⟩ :=
    exists_uniform_partition_advice F T hgood k n hk G hconn hdegree hlarge
  let part := rootOwner G roots canonicalId hne
  let residual := pairRule F (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k))
    (residualGraph (graphPresentation G) part) (canonicalId ∘ Subtype.val)
  let orientation := liftedOrientation (graphPresentation G) part residual
  have hdegree' : ∀ v, (graphPresentation G).degree v ≤ 2*k-1 :=
    fun v => (graphPresentation_degree G v).trans_le (hdegree v)
  have hcapacity := graph_cell_capacity G hconn roots canonicalId hne hinj k hk hsep
    (by simpa only [Fintype.card_fin] using hlarge)
  let encode := vertexEncode (graphPresentation G) part Subtype.val
    (rootOwner_root G hconn roots canonicalId hne hinj)
    orientation a (2*k-1) (2^k-1) hdegree' hbalanced hcapacity
  refine ⟨encode,?_⟩
  intro x e
  have hmarkers : recognizedRoots (encode x) = roots :=
    vertexEncode_recognizedRoots G hconn roots canonicalId hne hinj
      orientation a _ _ hdegree' hbalanced hcapacity x
  have hcover : MarkerCover G (codecRadius k) (encode x) := by
    intro v
    refine ⟨(part v).val,?_,hcell v⟩
    have hm : (part v).val ∈ recognizedRoots (encode x) := by
      rw [hmarkers]
      exact (part v).property
    simpa only [recognizedRoots,Finset.mem_filter,Finset.mem_univ,true_and] using hm
  have hpart : ∀ v, boundedOwner G canonicalId (codecRadius k) (encode x) v = some (part v).val :=
    boundedOwner_eq_rootOwner_of_roots G canonicalId hinj (codecRadius k)
      (encode x) hcover roots hne hmarkers
  have hadvice : ∀ v : roots, boundedAdvice (codecAlphabet_pos k hk) G canonicalId
      (codecRadius k) (encode x) v.val = a v := by
    intro v
    exact boundedAdvice_vertexEncode (codecAlphabet_pos k hk) G hconn roots canonicalId
      hne hinj (codecRadius k) hcell orientation a (2*k-1) hdegree' hbalanced hcapacity x v
  change boundedPairDecode (codecAlphabet_pos k hk) G canonicalId (codecRadius k) (2*k-1)
    (encode x) (boundedDirections (codecAlphabet_pos k hk) F
      (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k)) G canonicalId
      (codecRadius k) (encode x)) (graphPairEmbedding G e) = x e
  apply boundedPairDecode_vertexEncode (codecAlphabet_pos k hk) G hconn roots canonicalId
    hne hinj (codecRadius k) hcell orientation a (2*k-1) hdegree' hbalanced hcapacity x _ _ e
  intro e'
  exact boundedDirections_eq_liftedOrientation (codecAlphabet_pos k hk) F
    (n+codecDegree k+1) (codecDegree k) 1 (T (codecDegree k)) G roots part canonicalId
    (codecRadius k) (encode x) hpart a hadvice e'

end LocalDecompression.FiniteView
