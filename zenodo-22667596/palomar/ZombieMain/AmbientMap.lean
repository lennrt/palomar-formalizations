import ZombieMain.PortedPresentation

namespace ZombieMain
open SimpleGraph ZombieDamage
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H : G.Subgraph} {D : Diagram}

noncomputable def ambientStub (e : D.Embedding H) (hcubic : ∀ v, G.degree v=3)
    (i : Fin D.order) (hp : D.degree i.val=2) : V :=
  Classical.choose (port_neighbor_unique ((e.degree i).symm.trans hp) (hcubic _))

theorem ambientStub_spec (e : D.Embedding H) (hcubic : ∀ v, G.degree v=3)
    (i : Fin D.order) (hp : D.degree i.val=2) :
    G.Adj (e.vertices i) (ambientStub e hcubic i hp) ∧
      ¬ H.Adj (e.vertices i) (ambientStub e hcubic i hp) :=
  (Classical.choose_spec (port_neighbor_unique ((e.degree i).symm.trans hp) (hcubic _))).1

theorem ambientStub_eq (e : D.Embedding H) (hcubic : ∀ v, G.degree v=3)
    (i : Fin D.order) (hp : D.degree i.val=2) {w : V}
    (hw : G.Adj (e.vertices i) w ∧ ¬ H.Adj (e.vertices i) w) :
    ambientStub e hcubic i hp = w :=
  ((Classical.choose_spec (port_neighbor_unique ((e.degree i).symm.trans hp)
    (hcubic _))).2 w hw).symm

theorem bool_false_of_not_true {b : Bool} (h : ¬ b=true) : b=false := by
  cases b <;> simp_all

namespace PortedPresentation
variable {N : Nat} {T : Task N} (P : PortedPresentation T D)
variable (e : D.Embedding H) (hcubic : ∀ v, G.degree v=3) (fallback : V)

/-- The map uses the actual unique additional neighbor at each port.
Different leaves may therefore have the same image, including an internal image. -/
noncomputable def ambientMap (u : Fin N) : V := by
  classical
  exact if hu : T.inside u=true then e.vertices (P.label u hu)
    else if hp : P.HasParent u then
      ambientStub e hcubic (P.parent u hp) (P.parent_port u (bool_false_of_not_true hu) hp)
    else fallback

theorem ambientMap_inside (u : Fin N) (hu : T.inside u=true) :
    P.ambientMap e hcubic fallback u = e.vertices (P.label u hu) := by
  simp only [ambientMap, dif_pos hu]

theorem ambientMap_internal (i : Fin D.order) :
    P.ambientMap e hcubic fallback (P.internal i) = e.vertices i := by
  rw [P.ambientMap_inside e hcubic fallback _ (P.internal_inside i), P.label_internal]

theorem ambientMap_boundary (i : Fin D.order) (u : Fin N)
    (hout : T.inside u=false) (hadj : T.adj (P.internal i) u=true) :
    P.ambientMap e hcubic fallback u =
      ambientStub e hcubic i ((P.port_stub i).mpr ⟨u,hout,hadj⟩) := by
  have hn : ¬ T.inside u=true := by rw [hout]; decide
  have hp : P.HasParent u := ⟨i,hadj⟩
  simp only [ambientMap, dif_neg hn, dif_pos hp]
  have he := P.parent_unique u hout hp i hadj
  subst i
  rfl

theorem ambientMap_internal_adj {u v : Fin N}
    (hu : T.inside u=true) (hv : T.inside v=true) :
    T.adj u v=true ↔ H.Adj (P.ambientMap e hcubic fallback u)
      (P.ambientMap e hcubic fallback v) := by
  rw [P.ambientMap_inside e hcubic fallback u hu,
    P.ambientMap_inside e hcubic fallback v hv]
  have h1 := P.internal_label u hu
  have h2 := P.internal_label v hv
  calc
    T.adj u v=true ↔ T.adj (P.internal (P.label u hu)) (P.internal (P.label v hv))=true := by
      rw [h1,h2]
    _ ↔ D.adj (P.label u hu).val (P.label v hv).val=true := by rw [P.internal_adj]
    _ ↔ _ := e.adjacency _ _

theorem ambientMap_boundary_adj {u v : Fin N}
    (hu : T.inside u=true) (hv : T.inside v=false) (ha : T.adj u v=true) :
    G.Adj (P.ambientMap e hcubic fallback u) (P.ambientMap e hcubic fallback v) ∧
      ¬ H.Adj (P.ambientMap e hcubic fallback u) (P.ambientMap e hcubic fallback v) := by
  have hlabel := P.internal_label u hu
  have hadj : T.adj (P.internal (P.label u hu)) v=true := by rw [hlabel]; exact ha
  rw [P.ambientMap_inside e hcubic fallback u hu,
    P.ambientMap_boundary e hcubic fallback (P.label u hu) v hv hadj]
  exact ambientStub_spec e hcubic _ _

end PortedPresentation
end ZombieMain
