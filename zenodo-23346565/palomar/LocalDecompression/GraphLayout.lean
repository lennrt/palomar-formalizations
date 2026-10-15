module

public import LocalDecompression.Partition
public import LocalDecompression.Layout

@[expose] public section

/-! The generic marked-block layout instantiated by actual Voronoi cells. -/
namespace LocalDecompression
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The graph partition map takes values in the selected roots themselves. -/
noncomputable def rootOwner (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (v : V) : roots :=
  ⟨owner G roots id hne v, (owner_spec G roots id hne v).1⟩

 theorem rootOwner_eq_iff (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (hinj : Function.Injective id) (v : V) (c : roots) :
    rootOwner G roots id hne v = c ↔ Voronoi G roots id c.val v := by
  rw [← owner_eq_iff G roots id hne hinj v c.val]
  exact Subtype.ext_iff

 theorem rootOwner_root (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (c : roots) :
    rootOwner G roots id hne c.val = c := by
  apply Subtype.ext
  exact owner_root G hconn roots id hne hinj c.property

/-- Fiber cardinality in the generic codec is exactly the graph-cell cardinality. -/
theorem fiber_card_eq_cell (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (hinj : Function.Injective id) (c : roots) :
    Fintype.card (Fiber (rootOwner G roots id hne) c) = (cell G roots id c.val).card := by
  classical
  let e : Fiber (rootOwner G roots id hne) c ≃ {v // v ∈ cell G roots id c.val} :=
    Equiv.subtypeEquivProp (funext (fun v => propext
      ((rootOwner_eq_iff G roots id hne hinj v c).trans
        (mem_cell G roots id c.val v).symm)))
  exact (Fintype.card_congr e).trans (Fintype.card_coe _)

/-- No virtual sites are introduced: the data positions are exactly the
non-root vertices of the graph cell. -/
theorem graph_sites_card (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (c : roots) :
    Fintype.card (Sites (rootOwner G roots id hne) Subtype.val c) =
      (cell G roots id c.val).card - 1 := by
  rw [card_sites (rootOwner G roots id hne) Subtype.val
    (rootOwner_root G hconn roots id hne hinj), fiber_card_eq_cell G roots id hne hinj]

/-- On a connected component, exactly the roots are fixed points of its
uniquely determined nearest-root partition map. -/
theorem owner_fixed_iff (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) (v : V) :
    owner G roots id hne v = v ↔ v ∈ roots := by
  constructor
  · intro h
    have hv := (owner_spec G roots id hne v).1
    simpa [h] using hv
  · intro hv
    exact owner_root G hconn roots id hne hinj hv

/-- The root set actually read from zero markers in the vertex labels. -/
def recognizedRoots {q : ℕ} (labels : V → Fin (q + 1)) : Finset V :=
  Finset.univ.filter (fun v => labels v = 0)

/-- The marker decoder recovers the exact selected roots. The marker premise
is supplied by the vertex encoder's zero-iff-root theorem. -/
theorem marker_root_recovery (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) {q : ℕ} (labels : V → Fin (q + 1))
    (hmarker : ∀ v, labels v = 0 ↔ owner G roots id hne v = v) :
    recognizedRoots labels = roots := by
  ext v
  simp only [recognizedRoots, Finset.mem_filter, Finset.mem_univ, true_and]
  exact (hmarker v).trans (owner_fixed_iff G hconn roots id hne hinj v)

/-- Recomputing the nearest-root partition from the decoded markers gives
the exact original cell assignment. -/
theorem marker_partition_recovery (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) {q : ℕ} (labels : V → Fin (q + 1))
    (hmarker : ∀ v, labels v = 0 ↔ owner G roots id hne v = v)
    (c v : V) :
    Voronoi G (recognizedRoots labels) id c v ↔ Voronoi G roots id c v := by
  rw [marker_root_recovery G hconn roots id hne hinj labels hmarker]

end LocalDecompression
