module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

set_option linter.unusedSectionVars false

/-! Distance-net partitions used by the local decompression construction.
This module proves statements about actual finite simple graphs. Connectedness
is explicit: the construction is applied separately to connected components.
-/
namespace LocalDecompression
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A root wins by distance first and by identifier second. -/
def Voronoi (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ) (c v : V) : Prop :=
  c ∈ roots ∧ ∀ q ∈ roots,
    G.dist c v < G.dist q v ∨ (G.dist c v = G.dist q v ∧ id c ≤ id q)

/-- A finite distance net, stated with natural graph distances on a component. -/
def Separated (G : SimpleGraph V) (r : ℕ) (roots : Finset V) : Prop :=
  ∀ a ∈ roots, ∀ b ∈ roots, a ≠ b → 2 * r < G.dist a b

/-- Maximal separated root sets cover their component within twice the radius. -/
theorem maximal_separated_covers (G : SimpleGraph V) (r : ℕ) (roots : Finset V)
    (hsep : Separated G r roots)
    (hmax : ∀ s, Separated G r s → roots.card ≥ s.card) :
    ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r := by
  intro v
  by_contra! hv
  have hvnot : v ∉ roots := by
    intro h
    have := hv v h
    simp at this
  have hi : Separated G r (insert v roots) := by
    intro a ha b hb hab
    simp only [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact False.elim (hab rfl)
    · rw [G.dist_comm]
      exact hv b hb
    · exact hv a ha
    · exact hsep a ha b hb hab
  have := hmax _ hi
  simp [Finset.card_insert_of_notMem hvnot] at this

/-- Finite graphs admit a separated net. No distributed construction of it is needed:
it belongs to the unrestricted encoder. -/
theorem exists_separated_cover (G : SimpleGraph V) (r : ℕ) :
    ∃ roots : Finset V, Separated G r roots ∧
      ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r := by
  classical
  let candidates := Finset.univ.powerset.filter (Separated G r)
  have hempty : (∅ : Finset V) ∈ candidates := by simp [candidates, Separated]
  obtain ⟨roots, hroots, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hempty⟩
  have hsep : Separated G r roots := (Finset.mem_filter.mp hroots).2
  refine ⟨roots, hsep, maximal_separated_covers G r roots hsep ?_⟩
  intro s hs
  exact hmax s (by simp [candidates, hs])

 theorem voronoi_exists (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (v : V) : ∃ c, Voronoi G roots id c v := by
  classical
  obtain ⟨a, ha, hamin⟩ := roots.exists_min_image (fun c => G.dist c v) hne
  let nearest := roots.filter (fun c => G.dist c v = G.dist a v)
  have han : a ∈ nearest := by simp [nearest, ha]
  obtain ⟨c, hc, hcmin⟩ := nearest.exists_min_image id ⟨a, han⟩
  obtain ⟨hcr, hcd⟩ := Finset.mem_filter.mp hc
  refine ⟨c, hcr, ?_⟩
  intro q hq
  have hd : G.dist c v ≤ G.dist q v := hcd ▸ hamin q hq
  rcases lt_or_eq_of_le hd with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, hcmin q (by simp [nearest, hq, ← heq, hcd])⟩

 theorem voronoi_unique (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hinj : Function.Injective id) {a b v : V}
    (ha : Voronoi G roots id a v) (hb : Voronoi G roots id b v) : a = b := by
  have hab := ha.2 b hb.1
  have hba := hb.2 a ha.1
  apply hinj
  omega

 theorem voronoi_dist_le (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    {c v q : V} (h : Voronoi G roots id c v) (hq : q ∈ roots) :
    G.dist c v ≤ G.dist q v := by
  rcases h.2 q hq with hlt | ⟨heq, _⟩ <;> omega

 theorem voronoi_radius (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (r : ℕ) (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    {c v : V} (h : Voronoi G roots id c v) : G.dist c v ≤ 2 * r := by
  obtain ⟨q, hq, hd⟩ := hcover v
  exact (voronoi_dist_le G roots id h hq).trans hd

/-- Every geodesic from a cell root remains inside its ID-tiebroken Voronoi cell. -/
theorem voronoi_on_geodesic (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) {c v w : V}
    (hv : Voronoi G roots id c v)
    (hgeo : G.dist c v = G.dist c w + G.dist w v) : Voronoi G roots id c w := by
  refine ⟨hv.1, ?_⟩
  intro q hq
  have ht := hconn.dist_triangle (u := q) (v := w) (w := v)
  rcases hv.2 q hq with hlt | ⟨heq, hid⟩
  · exact Or.inl (by omega)
  · by_cases hlt : G.dist c w < G.dist q w
    · exact Or.inl hlt
    · exact Or.inr ⟨by omega, hid⟩

/-- A separated root owns its entire radius-r ball. -/
theorem ball_in_voronoi (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r : ℕ)
    (hsep : Separated G r roots) {c v : V} (hc : c ∈ roots)
    (hd : G.dist c v ≤ r) : Voronoi G roots id c v := by
  refine ⟨hc, ?_⟩
  intro q hq
  by_cases heq : c = q
  · subst q
    exact Or.inr ⟨rfl, le_rfl⟩
  · have hs := hsep c hc q hq heq
    have ht := hconn.dist_triangle (u := c) (v := v) (w := q)
    rw [G.dist_comm (u := v) (v := q)] at ht
    exact Or.inl (by omega)

/-- Every vertex of a shortest path lies in the cell. This is a graph-native
connectedness certificate, including the path and every vertex on it. -/
theorem voronoi_path (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) {c v : V}
    (hv : Voronoi G roots id c v) :
    ∃ p : G.Walk c v, p.IsPath ∧ p.length = G.dist c v ∧
      ∀ w ∈ p.support, Voronoi G roots id c w := by
  obtain ⟨p, hpath, hp⟩ := hconn.exists_path_of_dist c v
  refine ⟨p, hpath, hp, ?_⟩
  intro w hw
  have hleft := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hw)
  have hright := SimpleGraph.length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hw)
  have hlen := congrArg SimpleGraph.Walk.length (p.take_spec hw)
  simp only [SimpleGraph.Walk.length_append] at hlen
  apply voronoi_on_geodesic G hconn roots id hv
  omega

/-- Closed balls in a connected finite graph, represented as finite sets. -/
noncomputable def closedBall (G : SimpleGraph V) (c : V) (r : ℕ) : Finset V :=
  Finset.univ.filter (fun v => G.dist c v ≤ r)

@[simp] theorem mem_closedBall (G : SimpleGraph V) (c v : V) (r : ℕ) :
    v ∈ closedBall G c r ↔ G.dist c v ≤ r := by
  classical
  simp [closedBall]

/-- A shortest-path prefix supplies r+1 distinct vertices whenever the radius-r
ball does not already contain the whole component. -/
theorem closedBall_card_lower (G : SimpleGraph V) (hconn : G.Connected)
    (c : V) (r : ℕ) : min (r + 1) (Fintype.card V) ≤ (closedBall G c r).card := by
  classical
  by_cases hall : closedBall G c r = Finset.univ
  · simp [hall]
  · obtain ⟨v, hv⟩ : ∃ v, r < G.dist c v := by
      by_contra! h
      apply hall
      ext v
      simp [h v]
    obtain ⟨p, hpath, hp⟩ := hconn.exists_path_of_dist c v
    let q := p.take r
    have hqpath : q.IsPath := hpath.take r
    have hqlen : q.length = r := by
      simp [q, SimpleGraph.Walk.take_length, Nat.min_eq_left (by omega : r ≤ p.length)]
    have hsub : q.support.toFinset ⊆ closedBall G c r := by
      intro w hw
      have hmem : w ∈ q.support := by simpa using hw
      rw [mem_closedBall]
      exact (SimpleGraph.dist_le (q.takeUntil w hmem)).trans
        ((q.length_takeUntil_le_length hmem).trans_eq hqlen)
    have hc := Finset.card_le_card hsub
    have hcard : q.support.toFinset.card = r + 1 := by
      rw [List.toFinset_card_of_nodup hqpath.support_nodup, SimpleGraph.Walk.length_support, hqlen]
    rw [hcard] at hc
    exact (min_le_left _ _).trans hc

/-- Radius-r balls distinguish components of at most r vertices from larger ones. -/
theorem small_component_recognition (G : SimpleGraph V) (hconn : G.Connected)
    (c : V) (r : ℕ) :
    (closedBall G c r).card ≤ r ↔ Fintype.card V ≤ r := by
  constructor
  · intro h
    have hl := closedBall_card_lower G hconn c r
    omega
  · intro h
    exact (Finset.card_le_univ _).trans h

/-- The cell as a finite set. -/
noncomputable def cell (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (c : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => Voronoi G roots id c v)

@[simp] theorem mem_cell (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (c v : V) : v ∈ cell G roots id c ↔ Voronoi G roots id c v := by
  classical
  simp [cell]

/-- Every large-component cell has enough vertices for block encoding. -/
theorem cell_card_lower (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r : ℕ)
    (hsep : Separated G r roots) (hlarge : r < Fintype.card V)
    {c : V} (hc : c ∈ roots) : r + 1 ≤ (cell G roots id c).card := by
  have hsub : closedBall G c r ⊆ cell G roots id c := by
    intro v hv
    exact (mem_cell _ _ _ _ _).mpr (ball_in_voronoi G hconn roots id r hsep hc
      ((mem_closedBall G c v r).mp hv))
  have hl := closedBall_card_lower G hconn c r
  have hmin : min (r + 1) (Fintype.card V) = r + 1 := min_eq_left hlarge
  rw [hmin] at hl
  exact hl.trans (Finset.card_le_card hsub)

/-- A degree-only upper bound on ball size, sufficient for constant locality. -/
theorem closedBall_card_upper (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) (r : ℕ) :
    (closedBall G c r).card ≤ (Δ + 1) ^ r := by
  classical
  induction r with
  | zero =>
    have heq : closedBall G c 0 = {c} := by
      ext v
      simp [hconn.dist_eq_zero_iff, eq_comm]
    simp [heq]
  | succ r ih =>
    have hsub : closedBall G c (r + 1) ⊆
        (closedBall G c r).biUnion (fun w => insert w (G.neighborFinset w)) := by
      intro v hv
      have hd : G.dist v c ≤ r + 1 := by
        rw [G.dist_comm]
        exact (mem_closedBall G c v (r + 1)).mp hv
      obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist v c
      cases p with
      | nil =>
        apply Finset.mem_biUnion.mpr
        exact ⟨c, by simp, by simp⟩
      | @cons u w _ hadj p =>
        have hw : w ∈ closedBall G c r := by
          rw [mem_closedBall, G.dist_comm]
          have hp' := SimpleGraph.dist_le p
          simp only [SimpleGraph.Walk.length_cons] at hp
          omega
        apply Finset.mem_biUnion.mpr
        exact ⟨w, hw, Finset.mem_insert_of_mem
          (by simpa using hadj.symm)⟩
    calc
      (closedBall G c (r + 1)).card ≤
          ((closedBall G c r).biUnion (fun w => insert w (G.neighborFinset w))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ w ∈ closedBall G c r, (insert w (G.neighborFinset w)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ closedBall G c r, (Δ + 1) := by
        apply Finset.sum_le_sum
        intro w hw
        exact (Finset.card_insert_le _ _).trans (by simpa using Nat.add_le_add_right (hdeg w) 1)
      _ = (closedBall G c r).card * (Δ + 1) := by simp
      _ ≤ (Δ + 1) ^ r * (Δ + 1) := Nat.mul_le_mul_right _ ih
      _ = (Δ + 1) ^ (r + 1) := (pow_succ _ _).symm

 theorem cell_card_upper (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r Δ : ℕ)
    (hdeg : ∀ v, G.degree v ≤ Δ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r) (c : V) :
    (cell G roots id c).card ≤ (Δ + 1) ^ (2 * r) := by
  apply (Finset.card_le_card (show cell G roots id c ⊆ closedBall G c (2 * r) from ?_)).trans
    (closedBall_card_upper G hconn Δ hdeg c (2 * r))
  intro v hv
  exact (mem_closedBall G c v (2 * r)).mpr
    (voronoi_radius G roots id r hcover ((mem_cell _ _ _ _ _).mp hv))

/-- The complete component is visible within radius r whenever its size is at most r. -/
theorem small_component_visible (G : SimpleGraph V) (hconn : G.Connected)
    (r : ℕ) (hsmall : Fintype.card V ≤ r) (c : V) :
    closedBall G c r = Finset.univ := by
  classical
  ext v
  simp only [mem_closedBall, Finset.mem_univ, iff_true]
  obtain ⟨p, hpath, hp⟩ := hconn.exists_path_of_dist c v
  have hlen := hpath.support_nodup.length_le_card
  rw [SimpleGraph.Walk.length_support, hp] at hlen
  omega

/-- A root at distance greater than R cannot affect the winner once some root is
visible within R. The decoder therefore requires only locally visible markers. -/
theorem voronoi_local_roots (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (R : ℕ) (v : V) (hcover : ∃ q ∈ roots, G.dist q v ≤ R) (c : V) :
    Voronoi G roots id c v ↔
      Voronoi G (roots.filter (fun q => G.dist q v ≤ R)) id c v := by
  classical
  constructor
  · intro h
    have hcR : G.dist c v ≤ R := by
      obtain ⟨q, hq, hd⟩ := hcover
      exact (voronoi_dist_le G roots id h hq).trans hd
    refine ⟨Finset.mem_filter.mpr ⟨h.1, hcR⟩, ?_⟩
    intro q hq
    exact h.2 q (Finset.mem_filter.mp hq).1
  · intro h
    obtain ⟨hc, hcR⟩ := Finset.mem_filter.mp h.1
    refine ⟨hc, ?_⟩
    intro q hq
    by_cases hqR : G.dist q v ≤ R
    · exact h.2 q (Finset.mem_filter.mpr ⟨hq, hqR⟩)
    · exact Or.inl (by omega)

/-- Agreement of the visible root markers implies agreement of the decoded cell. -/
theorem voronoi_of_local_root_agreement (G : SimpleGraph V)
    (roots roots' : Finset V) (id : V → ℕ) (R : ℕ) (v : V)
    (hcover : ∃ q ∈ roots, G.dist q v ≤ R)
    (hcover' : ∃ q ∈ roots', G.dist q v ≤ R)
    (hlocal : roots.filter (fun q => G.dist q v ≤ R) =
      roots'.filter (fun q => G.dist q v ≤ R)) (c : V) :
    Voronoi G roots id c v ↔ Voronoi G roots' id c v := by
  rw [voronoi_local_roots G roots id R v hcover,
    voronoi_local_roots G roots' id R v hcover', hlocal]

/-- A radius-R view around a cell vertex is inside radius R+2r of its root. -/
theorem cell_view_containment (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r R : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    {c v w : V} (hv : Voronoi G roots id c v) (hw : G.dist v w ≤ R) :
    G.dist c w ≤ 2 * r + R := by
  have hc := voronoi_radius G roots id r hcover hv
  have ht := hconn.dist_triangle (u := c) (v := v) (w := w)
  omega

/-- The simple adjacency graph of cells. Its vertex type includes isolated nonroots. -/
def clusterGraph (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ) : SimpleGraph V where
  Adj a b := a ≠ b ∧ ∃ u v, Voronoi G roots id a u ∧ Voronoi G roots id b v ∧ G.Adj u v
  symm := ⟨by
    intro a b ⟨hab, u, v, hu, hv, huv⟩
    exact ⟨Ne.symm hab, v, u, hv, hu, huv.symm⟩⟩
  loopless := ⟨by simp⟩

/-- Adjacent cell roots can exchange messages over at most 4r+1 original edges. -/
theorem cluster_adj_dist (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    {a b : V} (hab : (clusterGraph G roots id).Adj a b) :
    G.dist a b ≤ 4 * r + 1 := by
  obtain ⟨_, u, v, hu, hv, huv⟩ := hab
  have hau := voronoi_radius G roots id r hcover hu
  have hbv := voronoi_radius G roots id r hcover hv
  have huv' := SimpleGraph.dist_eq_one_iff_adj.mpr huv
  have ht₁ := hconn.dist_triangle (u := a) (v := u) (w := v)
  have ht₂ := hconn.dist_triangle (u := a) (v := v) (w := b)
  rw [G.dist_comm (u := v) (v := b)] at ht₂
  omega

/-- A graph whose edges have physical length at most L can be simulated with
L physical hops per round. This statement supplies the complete walk bound. -/
theorem walk_dist_le_mul (G H : SimpleGraph V) (hconn : G.Connected) (L : ℕ)
    (hedge : ∀ a b, H.Adj a b → G.dist a b ≤ L)
    {a b : V} (p : H.Walk a b) : G.dist a b ≤ p.length * L := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have ht := hconn.dist_triangle (u := a) (v := b) (w := c)
    have he := hedge a b hab
    simp only [SimpleGraph.Walk.length_cons]
    nlinarith

/-- Every T-round quotient view is contained in a physical radius (4r+1)T view. -/
theorem cluster_walk_locality (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (r : ℕ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r)
    {a b : V} (p : (clusterGraph G roots id).Walk a b) :
    G.dist a b ≤ p.length * (4 * r + 1) := by
  exact walk_dist_le_mul G _ hconn _
    (fun _ _ h => cluster_adj_dist G hconn roots id r hcover h) p

/-- The encoder and decoder use the same uniquely determined owner function. -/
noncomputable def owner (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (v : V) : V :=
  Classical.choose (voronoi_exists G roots id hne v)

 theorem owner_spec (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (v : V) : Voronoi G roots id (owner G roots id hne v) v :=
  Classical.choose_spec (voronoi_exists G roots id hne v)

 theorem owner_eq_iff (G : SimpleGraph V) (roots : Finset V) (id : V → ℕ)
    (hne : roots.Nonempty) (hinj : Function.Injective id) (v c : V) :
    owner G roots id hne v = c ↔ Voronoi G roots id c v := by
  constructor
  · intro h
    rw [← h]
    exact owner_spec G roots id hne v
  · intro h
    exact voronoi_unique G roots id hinj (owner_spec G roots id hne v) h

/-- A cell has at most Δ times its size distinct neighboring cells. -/
theorem cluster_degree_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) [DecidableRel (clusterGraph G roots id).Adj]
    (Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (c : V) :
    (clusterGraph G roots id).degree c ≤ (cell G roots id c).card * Δ := by
  classical
  let boundary := (cell G roots id c).biUnion (fun u => G.neighborFinset u)
  have hsub : (clusterGraph G roots id).neighborFinset c ⊆
      boundary.image (owner G roots id hne) := by
    intro b hb
    have hab : (clusterGraph G roots id).Adj c b := by simpa using hb
    obtain ⟨_, u, v, hu, hv, huv⟩ := hab
    apply Finset.mem_image.mpr
    refine ⟨v, ?_, (owner_eq_iff G roots id hne hinj v b).mpr hv⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨u, (mem_cell _ _ _ _ _).mpr hu, by simpa using huv⟩
  calc
    (clusterGraph G roots id).degree c = ((clusterGraph G roots id).neighborFinset c).card := rfl
    _ ≤ (boundary.image (owner G roots id hne)).card := Finset.card_le_card hsub
    _ ≤ boundary.card := Finset.card_image_le
    _ ≤ ∑ u ∈ cell G roots id c, (G.neighborFinset u).card := Finset.card_biUnion_le
    _ ≤ ∑ _u ∈ cell G roots id c, Δ := by
      exact Finset.sum_le_sum (fun u _ => hdeg u)
    _ = (cell G roots id c).card * Δ := by simp

/-- The quotient degree is a constant depending only on Δ and the chosen block radius. -/
theorem cluster_degree_uniform (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) [DecidableRel (clusterGraph G roots id).Adj]
    (r Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ)
    (hcover : ∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r) (c : V) :
    (clusterGraph G roots id).degree c ≤ (Δ + 1) ^ (2 * r) * Δ := by
  exact (cluster_degree_bound G roots id hne hinj Δ hdeg c).trans
    (Nat.mul_le_mul_right Δ (cell_card_upper G hconn roots id r Δ hdeg hcover c))

/-- A complete finite partition theorem for a large connected component.
Roots are produced here, rather than assumed. Every vertex has exactly one
cell; cells have bounded radius, a size interval depending only on degree/r,
and paths from their roots staying inside the cell. -/
theorem exists_large_component_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (id : V → ℕ) (hinj : Function.Injective id)
    (r Δ : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hlarge : r < Fintype.card V) :
    ∃ roots : Finset V,
      roots.Nonempty ∧ Separated G r roots ∧
      (∀ v, ∃ c ∈ roots, G.dist c v ≤ 2 * r) ∧
      (∀ v, ∃! c, Voronoi G roots id c v) ∧
      (∀ c ∈ roots, r + 1 ≤ (cell G roots id c).card ∧
        (cell G roots id c).card ≤ (Δ + 1) ^ (2 * r)) ∧
      (∀ c v, Voronoi G roots id c v → G.dist c v ≤ 2 * r) ∧
      (∀ c v, Voronoi G roots id c v →
        ∃ p : G.Walk c v, p.IsPath ∧ p.length = G.dist c v ∧
          ∀ w ∈ p.support, Voronoi G roots id c w) := by
  classical
  obtain ⟨roots, hsep, hcover⟩ := exists_separated_cover G r
  have hne : roots.Nonempty := by
    obtain ⟨v⟩ := hconn.nonempty
    obtain ⟨c, hc, _⟩ := hcover v
    exact ⟨c, hc⟩
  refine ⟨roots, hne, hsep, hcover, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨c, hc⟩ := voronoi_exists G roots id hne v
    exact ⟨c, hc, fun _ h => voronoi_unique G roots id hinj h hc⟩
  · intro c hc
    exact ⟨cell_card_lower G hconn roots id r hsep hlarge hc,
      cell_card_upper G hconn roots id r Δ hdeg hcover c⟩
  · intro c v hv
    exact voronoi_radius G roots id r hcover hv
  · intro c v hv
    exact voronoi_path G hconn roots id hv

/-- The partition theorem applies to each actual connected component of a
possibly disconnected input, with the component's own cardinality threshold. -/
theorem component_has_large_partition (G : SimpleGraph V) (C : G.ConnectedComponent)
    [Fintype C] [DecidableEq C] [DecidableRel C.toSimpleGraph.Adj]
    (id : C → ℕ) (hinj : Function.Injective id) (r Δ : ℕ)
    (hdeg : ∀ v, C.toSimpleGraph.degree v ≤ Δ) (hlarge : r < Fintype.card C) :
    ∃ roots : Finset C, Separated C.toSimpleGraph r roots ∧
      (∀ v, ∃! c, Voronoi C.toSimpleGraph roots id c v) ∧
      ∀ c ∈ roots, r + 1 ≤ (cell C.toSimpleGraph roots id c).card ∧
        (cell C.toSimpleGraph roots id c).card ≤ (Δ + 1) ^ (2 * r) := by
  obtain ⟨roots, _, hs, _, hu, hc, _, _⟩ :=
    exists_large_component_partition C.toSimpleGraph C.connected_toSimpleGraph
      id hinj r Δ hdeg hlarge
  exact ⟨roots, hs, hu, hc⟩

/-- A root is the winner at its own vertex. -/
theorem voronoi_self (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) {c : V} (hc : c ∈ roots) :
    Voronoi G roots id c c := by
  refine ⟨hc, ?_⟩
  intro q hq
  by_cases h : q = c
  · subst q
    exact Or.inr ⟨rfl, le_rfl⟩
  · exact Or.inl (by simpa using hconn.pos_dist_of_ne h)

 theorem owner_root (G : SimpleGraph V) (hconn : G.Connected)
    (roots : Finset V) (id : V → ℕ) (hne : roots.Nonempty)
    (hinj : Function.Injective id) {c : V} (hc : c ∈ roots) :
    owner G roots id hne c = c :=
  (owner_eq_iff G roots id hne hinj c c).mpr (voronoi_self G hconn roots id hc)

end LocalDecompression
