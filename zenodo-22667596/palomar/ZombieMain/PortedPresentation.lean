import ZombieMain.ComponentPorts
import ZombieDamage.Ambient
import ZombieDamage.FullGameConverse

namespace ZombieMain
open ZombieDamage

/-- An exact labelling of a component together with one leaf at each port.
These are finite graph facts, independent of targets and strategy choices. -/
structure PortedPresentation {N : Nat} (T : Task N) (D : Diagram) where
  internal : Fin D.order → Fin N
  internal_injective : Function.Injective internal
  inside_exact : ∀ v, T.inside v=true ↔ ∃ i, internal i=v
  internal_adj : ∀ i j, T.adj (internal i) (internal j) = D.adj i.val j.val
  good : T.GoodGraph
  boundary_leaves : T.BoundaryLeaves
  outside_neighbors : ∀ u v, T.inside u=false → T.adj u v=true → T.inside v=true
  one_stub : ∀ u v w, T.inside v=true → T.inside u=false → T.inside w=false →
    T.adj u v=true → T.adj v w=true → u=w
  port_stub : ∀ i, D.degree i.val=2 ↔
    ∃ v, T.inside v=false ∧ T.adj (internal i) v=true

namespace PortedPresentation
variable {N : Nat} {T : Task N} {D : Diagram} (P : PortedPresentation T D)

theorem internal_inside (i : Fin D.order) : T.inside (P.internal i)=true :=
  (P.inside_exact _).mpr ⟨i,rfl⟩

noncomputable def label (u : Fin N) (hu : T.inside u=true) : Fin D.order :=
  Classical.choose ((P.inside_exact u).mp hu)

theorem internal_label (u : Fin N) (hu : T.inside u=true) :
    P.internal (P.label u hu) = u := Classical.choose_spec ((P.inside_exact u).mp hu)

theorem label_internal (i : Fin D.order) :
    P.label (P.internal i) (P.internal_inside i) = i :=
  P.internal_injective (P.internal_label _ _)

def HasParent (u : Fin N) : Prop := ∃ i, T.adj (P.internal i) u=true

noncomputable def parent (u : Fin N) (h : P.HasParent u) : Fin D.order := Classical.choose h

theorem parent_adj (u : Fin N) (h : P.HasParent u) :
    T.adj (P.internal (P.parent u h)) u=true := Classical.choose_spec h

theorem parent_unique (u : Fin N) (hout : T.inside u=false) (h : P.HasParent u)
    (i : Fin D.order) (hi : T.adj (P.internal i) u=true) : P.parent u h = i := by
  apply P.internal_injective
  apply P.boundary_leaves u hout
  · rw [P.good.1]; exact P.parent_adj u h
  · rw [P.good.1]; exact hi

theorem parent_port (u : Fin N) (hout : T.inside u=false) (h : P.HasParent u) :
    D.degree (P.parent u h).val=2 := (P.port_stub _).mpr ⟨u,hout,P.parent_adj u h⟩

def retarget (target : Option (Fin N)) (allowed : Fin N → Bool) :
    PortedPresentation {T with target := target, allowedExit := allowed} D where
  internal := P.internal
  internal_injective := P.internal_injective
  inside_exact := P.inside_exact
  internal_adj := P.internal_adj
  good := P.good
  boundary_leaves := P.boundary_leaves
  outside_neighbors := P.outside_neighbors
  one_stub := P.one_stub
  port_stub := P.port_stub

end PortedPresentation
end ZombieMain
