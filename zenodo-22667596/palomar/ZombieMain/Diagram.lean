import ZombieMain.CycleUnion

namespace ZombieMain
open SimpleGraph

/-- A finite adjacency table or formula. Its graph vertices are precisely the
natural-number labels below `order`; values outside that range have no meaning. -/
structure Diagram where
  order : Nat
  adj : Nat → Nat → Bool

namespace Diagram

def degree (D : Diagram) (v : Nat) : Nat :=
  (Finset.univ.filter (fun w : Fin D.order => D.adj v w.val)).card

def portCount (D : Diagram) : Nat :=
  (Finset.univ.filter (fun v : Fin D.order => D.degree v.val = 2)).card

def reach (D : Diagram) : Nat → Nat → Nat → Bool
  | 0, u, v => u == v
  | k+1, u, v => (u == v) ||
      (List.range D.order).any (fun w => D.adj u w && D.reach k w v)

def pathAdj (path : List Nat) (u v : Nat) : Bool :=
  (path.zip path.tail).any (fun e => (u == e.1 && v == e.2) ||
    (u == e.2 && v == e.1))

def adjoinPath (D : Diagram) (p q r : Nat) : Diagram where
  order := D.order + (r-1)
  adj u v := (decide (u < D.order ∧ v < D.order) && D.adj u v) ||
    pathAdj ([p] ++ (List.range (r-1)).map (D.order + ·) ++ [q]) u v

def LegalPath (D : Diagram) (p q r : Nat) : Prop :=
  p < D.order ∧ q < D.order ∧ p ≠ q ∧
  D.degree p = 2 ∧ D.degree q = 2 ∧
  1 ≤ r ∧ r ≤ 3 ∧ D.reach (4-r) p q = true ∧
  (r = 1 → D.adj p q = false)

instance (D : Diagram) (p q r : Nat) : Decidable (D.LegalPath p q r) := by
  unfold LegalPath
  infer_instance

def adjoinMatching (D : Diagram) (a b c d : Nat) : Diagram where
  order := D.order
  adj u v := D.adj u v ||
    (u == a && v == c) || (u == c && v == a) ||
    (u == b && v == d) || (u == d && v == b)

def LegalMatching (D : Diagram) (a b c d : Nat) : Prop :=
  a < D.order ∧ b < D.order ∧ c < D.order ∧ d < D.order ∧
  [a,b,c,d].Nodup ∧
  D.degree a = 2 ∧ D.degree b = 2 ∧ D.degree c = 2 ∧ D.degree d = 2 ∧
  D.adj a b = true ∧ D.adj c d = true ∧
  D.adj a c = false ∧ D.adj b d = false

instance (D : Diagram) (a b c d : Nat) : Decidable (D.LegalMatching a b c d) := by
  unfold LegalMatching
  infer_instance

structure Iso (D E : Diagram) where
  vertices : Fin D.order ≃ Fin E.order
  adjacency : ∀ u v, D.adj u.val v.val = E.adj (vertices u).val (vertices v).val

def Iso.refl (D : Diagram) : D.Iso D := ⟨Equiv.refl _, fun _ _ => rfl⟩

def Iso.symm {D E : Diagram} (f : D.Iso E) : E.Iso D where
  vertices := f.vertices.symm
  adjacency u v := by simpa using (f.adjacency (f.vertices.symm u) (f.vertices.symm v)).symm

def Iso.trans {D E F : Diagram} (f : D.Iso E) (g : E.Iso F) : D.Iso F where
  vertices := f.vertices.trans g.vertices
  adjacency u v := (f.adjacency u v).trans (g.adjacency _ _)

def isoOfNat (D E : Diagram) (f g : Nat → Nat)
    (hf : ∀ u, u < D.order → f u < E.order)
    (hg : ∀ v, v < E.order → g v < D.order)
    (hgf : ∀ u, u < D.order → g (f u) = u)
    (hfg : ∀ v, v < E.order → f (g v) = v)
    (hadj : ∀ u v, u < D.order → v < D.order → D.adj u v = E.adj (f u) (f v)) :
    D.Iso E where
  vertices :=
    { toFun := fun u => ⟨f u.val, hf u.val u.isLt⟩
      invFun := fun v => ⟨g v.val, hg v.val v.isLt⟩
      left_inv := fun u => Fin.ext (hgf u.val u.isLt)
      right_inv := fun v => Fin.ext (hfg v.val v.isLt) }
  adjacency u v := hadj u.val v.val u.isLt v.isLt

/-- Explicit mutually inverse label lists. Their validator is a finite
proposition checked with ordinary kernel reduction, never `native_decide`. -/
structure Certificate where
  forward : List Nat
  backward : List Nat
  deriving Repr

def Certificate.Valid (c : Certificate) (D E : Diagram) : Prop :=
  (∀ u : Fin D.order, c.forward.getD u.val 0 < E.order) ∧
  (∀ v : Fin E.order, c.backward.getD v.val 0 < D.order) ∧
  (∀ u : Fin D.order, c.backward.getD (c.forward.getD u.val 0) 0 = u.val) ∧
  (∀ v : Fin E.order, c.forward.getD (c.backward.getD v.val 0) 0 = v.val) ∧
  (∀ u v : Fin D.order, D.adj u.val v.val =
    E.adj (c.forward.getD u.val 0) (c.forward.getD v.val 0))

instance (c : Certificate) (D E : Diagram) : Decidable (c.Valid D E) := by
  unfold Certificate.Valid
  infer_instance

def Certificate.toIso {c : Certificate} {D E : Diagram} (h : c.Valid D E) : D.Iso E where
  vertices :=
    { toFun := fun u => ⟨c.forward.getD u.val 0, h.1 u⟩
      invFun := fun v => ⟨c.backward.getD v.val 0, h.2.1 v⟩
      left_inv := fun u => Fin.ext (h.2.2.1 u)
      right_inv := fun v => Fin.ext (h.2.2.2.1 v) }
  adjacency := h.2.2.2.2

/-- An exact copy of a diagram in an ambient subgraph. The internal vertex
map is bijective onto the subgraph, and adjacency is reflected as well as preserved. -/
structure Embedding (D : Diagram) {V : Type*} {G : SimpleGraph V} (H : G.Subgraph) where
  vertices : Fin D.order → V
  injective : Function.Injective vertices
  range_eq : Set.range vertices = H.verts
  adjacency : ∀ u v, D.adj u.val v.val = true ↔ H.Adj (vertices u) (vertices v)

def Embedding.relabel {D E : Diagram} {V : Type*} {G : SimpleGraph V}
    {H : G.Subgraph} (f : D.Embedding H) (e : E.Iso D) : E.Embedding H where
  vertices := f.vertices ∘ e.vertices
  injective := f.injective.comp e.vertices.injective
  range_eq := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, f.range_eq]
  adjacency u v := by rw [e.adjacency]; exact f.adjacency _ _

end Diagram
end ZombieMain
