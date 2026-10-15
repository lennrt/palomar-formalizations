module

public import LocalDecompression.Partition

@[expose] public section

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-! Exact finite-neighborhood facts used by the LOCAL decoder.
Distances computed in the observed induced subgraph agree with the original
ones whenever the appropriate shortest paths lie inside the observed radius.
-/
namespace LocalDecompression
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Restricting a graph does not change an endpoint distance when a shortest
path remains in the retained vertex set. -/
theorem induced_dist_eq_of_geodesic (G : SimpleGraph V) (S : Set V)
    {u v : V} (hu : u ∈ S) (hv : v ∈ S) (p : G.Walk u v)
    (hp : p.length = G.dist u v) (hS : ∀ w ∈ p.support, w ∈ S) :
    (G.induce S).dist ⟨u, hu⟩ ⟨v, hv⟩ = G.dist u v := by
  let q : (G.induce S).Walk ⟨u, hu⟩ ⟨v, hv⟩ := p.induce S hS
  have hq : q.length = p.length := by
    have h := congrArg SimpleGraph.Walk.length (p.map_induce (s := S) hS)
    dsimp only [q]
    simpa only [SimpleGraph.Walk.length_map] using h
  apply Nat.le_antisymm
  · exact (SimpleGraph.dist_le q).trans_eq (hq.trans hp)
  · obtain ⟨t, ht⟩ := q.reachable.exists_walk_length_eq_dist
    have h := SimpleGraph.dist_le (t.map (SimpleGraph.Embedding.induce S).toHom)
    rw [SimpleGraph.Walk.length_map, ht] at h
    exact h

/-- With sufficient margin around u, every distance from u to a nearby vertex
can be computed in the induced physical view centered at c. -/
theorem induced_dist_eq_with_margin (G : SimpleGraph V) (hconn : G.Connected)
    (c : V) (R : ℕ) {u v : V} (hu : G.dist c u ≤ R) (hv : G.dist c v ≤ R)
    (hmargin : G.dist c u + G.dist u v ≤ R) :
    (G.induce {w | G.dist c w ≤ R}).dist ⟨u, hu⟩ ⟨v, hv⟩ = G.dist u v := by
  obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist u v
  apply induced_dist_eq_of_geodesic G _ hu hv p hp
  intro w hw
  have hd : G.dist u w ≤ p.length :=
    (SimpleGraph.dist_le (p.takeUntil w hw)).trans (p.length_takeUntil_le_length hw)
  have ht := hconn.dist_triangle (u := c) (v := u) (w := w)
  change G.dist c w ≤ R
  omega

/-- The center can measure every distance in its own observed ball exactly. -/
theorem view_center_dist (G : SimpleGraph V) (hconn : G.Connected)
    (c : V) (R : ℕ) (v : V) (hv : G.dist c v ≤ R) :
    (G.induce {w | G.dist c w ≤ R}).dist ⟨c, by simp⟩ ⟨v, hv⟩ = G.dist c v := by
  apply induced_dist_eq_with_margin G hconn c R (by simp) hv
  simpa using hv

/-- A cell root's radius-4r view contains exact distance comparisons between
any vertex of its cell and every root that could win at that vertex. -/
theorem cell_view_candidate_dist (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    {c v q : V} (hv : Voronoi G roots id c v) (hq : G.dist v q ≤ 2 * r) :
    ∃ hvR : G.dist c v ≤ 4 * r, ∃ hqR : G.dist c q ≤ 4 * r,
      (G.induce {w | G.dist c w ≤ 4 * r}).dist ⟨v, hvR⟩ ⟨q, hqR⟩ = G.dist v q := by
  have hcv := voronoi_radius G roots id r hcover hv
  have hcq := cell_view_containment G hconn roots id r (2 * r) hcover hv hq
  have hvR : G.dist c v ≤ 4 * r := by omega
  have hqR : G.dist c q ≤ 4 * r := by omega
  exact ⟨hvR, hqR, induced_dist_eq_with_margin G hconn c (4 * r)
    hvR hqR (by omega)⟩

/-- A finite-radius neighborhood defined by actual walks, valid even in
 disconnected graphs (unlike the junk value of `SimpleGraph.dist`). -/
def Within {W : Type*} (G : SimpleGraph W) (R : ℕ) (a b : W) : Prop :=
  ∃ p : G.Walk a b, p.length ≤ R

/-- Extensional LOCAL semantics. Output indices may be vertices or edges;
`place` specifies the physical vertex at which each output is read. -/
def LocalAt {W I A B : Type*} (G : SimpleGraph W) (R : ℕ) (place : I → W)
    (F : (W → A) → (I → B)) : Prop :=
  ∀ x y i, (∀ v, Within G R (place i) v → x v = y v) → F x i = F y i

 theorem within_iff_dist (G : SimpleGraph V) (hconn : G.Connected)
    (R : ℕ) (a b : V) : Within G R a b ↔ G.dist a b ≤ R := by
  constructor
  · rintro ⟨p, hp⟩
    exact (SimpleGraph.dist_le p).trans hp
  · intro h
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist a b
    exact ⟨p, hp ▸ h⟩

/-- Quotient walks remain short under a physical placement of the quotient's
vertices. Unlike `walk_dist_le_mul`, the two vertex types may be different. -/
theorem placed_walk_dist_le_mul {C : Type*} (G : SimpleGraph V)
    (H : SimpleGraph C) (hconn : G.Connected) (place : C → V) (L : ℕ)
    (hedge : ∀ a b, H.Adj a b → G.dist (place a) (place b) ≤ L)
    {a b : C} (p : H.Walk a b) : G.dist (place a) (place b) ≤ p.length * L := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have ht := hconn.dist_triangle (u := place a) (v := place b) (w := place c)
    have he := hedge a b hab
    simp only [SimpleGraph.Walk.length_cons]
    nlinarith

/-- A precise conditional LOCAL simulation theorem. Advice extraction has
physical radius A; the supplied oracle has quotient radius T; quotient edges
have physical length at most L. Outputs may be edge-indexed via `anchor`.
The resulting radius is independent of the number of graph vertices. -/
theorem local_composition {C E Input Advice Output : Type*}
    (G : SimpleGraph V) (H : SimpleGraph C) (hconn : G.Connected)
    (place : C → V) (anchor : E → C) (A T L : ℕ)
    (recover : (V → Input) → (C → Advice))
    (oracle : (C → Advice) → (E → Output))
    (hrecover : LocalAt G A place recover)
    (horacle : LocalAt H T anchor oracle)
    (hedge : ∀ a b, H.Adj a b → G.dist (place a) (place b) ≤ L) :
    LocalAt G (L * T + A) (place ∘ anchor) (fun labels => oracle (recover labels)) := by
  intro x y e hagree
  apply horacle (recover x) (recover y) e
  intro c hc
  apply hrecover x y c
  intro v hv
  apply hagree v
  obtain ⟨p, hp⟩ := hc
  have hd₁ := placed_walk_dist_le_mul G H hconn place L hedge p
  have hd₂ := (within_iff_dist G hconn A (place c) v).mp hv
  have hm : p.length * L ≤ L * T := by nlinarith
  have ht := hconn.dist_triangle (u := place (anchor e)) (v := place c) (w := v)
  apply (within_iff_dist G hconn (L * T + A) (place (anchor e)) v).mpr
  omega

/-- Reading all labels in a bounded-radius cell is a LOCAL operation regardless
of how the finite block is subsequently decoded. -/
theorem cell_reader_local {C Input Output : Type*} [DecidableEq C]
    (G : SimpleGraph V) (hconn : G.Connected) (part : V → C)
    (place : C → V) (A : ℕ)
    (hcell : ∀ v, G.dist (place (part v)) v ≤ A)
    (read : (c : C) → ({v // part v = c} → Input) → Output) :
    LocalAt G A place (fun labels c => read c (fun v => labels v.val)) := by
  intro x y c hagree
  apply congrArg (read c)
  funext v
  apply hagree v.val
  apply (within_iff_dist G hconn A (place c) v.val).mpr
  have h := hcell v.val
  simpa [v.property] using h

end LocalDecompression
