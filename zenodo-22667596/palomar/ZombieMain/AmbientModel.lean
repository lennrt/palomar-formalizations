import ZombieMain.AmbientMap

namespace ZombieMain.PortedPresentation
open SimpleGraph ZombieDamage
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {N : Nat} {T : Task N} {D : Diagram} (P : PortedPresentation T D)

/-- Construct every field of the ambient game model from the actual component
embedding, cubic degrees and the literal leaf presentation. No strategy
or ambient routing hypothesis is required. -/
noncomputable def ambientModel (K : (shortGraph G).ConnectedComponent)
    (e : D.Embedding (shortComponent G K)) (hcubic : ∀ v, G.degree v=3) (fallback : V) :
    ShortComponentModel T (gameGraph G) where
  map := P.ambientMap e hcubic fallback
  internal_injective u v hu hv h := by
    rw [P.ambientMap_inside e hcubic fallback u hu,
      P.ambientMap_inside e hcubic fallback v hv] at h
    have he := e.injective h
    calc
      u = P.internal (P.label u hu) := (P.internal_label u hu).symm
      _ = P.internal (P.label v hv) := congrArg P.internal he
      _ = v := P.internal_label v hv
  edges u v h := by
    by_cases hu : T.inside u=true
    · by_cases hv : T.inside v=true
      · exact ((P.ambientMap_internal_adj e hcubic fallback hu hv).mp h).adj_sub
      · exact (P.ambientMap_boundary_adj e hcubic fallback hu (bool_false_of_not_true hv) h).1
    · have hv := P.outside_neighbors u v (bool_false_of_not_true hu) h
      have hrev : T.adj v u=true := by rw [P.good.1]; exact h
      exact (P.ambientMap_boundary_adj e hcubic fallback hv (bool_false_of_not_true hu) hrev).1.symm
  internal_edges u v hu hv := by
    rw [P.ambientMap_internal_adj e hcubic fallback hu hv]
    have humem : P.ambientMap e hcubic fallback u ∈ K.supp := by
      rw [P.ambientMap_inside e hcubic fallback u hu]
      exact e.mem _
    exact ⟨fun h => (shortEdge_iff_gameShort G _ _).mp h.2,
      fun h => ⟨humem,(shortEdge_iff_gameShort G _ _).mpr h⟩⟩
  clean_boundary u v hu hv h := by
    have he := P.ambientMap_boundary_adj e hcubic fallback hu hv h
    have humem : P.ambientMap e hcubic fallback u ∈ K.supp := by
      rw [P.ambientMap_inside e hcubic fallback u hu]
      exact e.mem _
    exact shortComponent_missing_clean K humem he.1 he.2
  one_stub := P.one_stub
  closed u hu x hx := by
    have humem : P.ambientMap e hcubic fallback u ∈ K.supp := by
      rw [P.ambientMap_inside e hcubic fallback u hu]
      exact e.mem _
    have hshort := (shortEdge_iff_gameShort G _ _).mpr hx
    have hxmem : x ∈ (shortComponent G K).verts := K.mem_supp_of_adj_mem_supp humem hshort
    obtain ⟨i,hi⟩ := e.exists_label hxmem
    exact ⟨P.internal i,P.internal_inside i,(P.ambientMap_internal e hcubic fallback i).trans hi⟩

/-- The constructed model realizes any actual clean entry at a labelled port. -/
theorem ambientModel_entry (K : (shortGraph G).ConnectedComponent)
    (e : D.Embedding (shortComponent G K)) (hcubic : ∀ v, G.degree v=3) (fallback : V)
    (i : Fin D.order) (stub : Fin N) (hout : T.inside stub=false)
    (hadj : T.adj (P.internal i) stub=true) {z : V}
    (hclean : (gameGraph G).Clean (e.vertices i) z) :
    (P.ambientModel K e hcubic fallback).map (P.internal i) = e.vertices i ∧
    (P.ambientModel K e hcubic fallback).map stub = z := by
  constructor
  · exact P.ambientMap_internal e hcubic fallback i
  · change P.ambientMap e hcubic fallback stub = z
    rw [P.ambientMap_boundary e hcubic fallback i stub hout hadj]
    exact ambientStub_eq e hcubic _ _ ⟨hclean.1, shortComponent_clean_missing K hclean⟩

end ZombieMain.PortedPresentation
