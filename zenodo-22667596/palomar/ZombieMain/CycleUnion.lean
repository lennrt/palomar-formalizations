import ZombieMain.StructuralBase
import Mathlib.Order.Preorder.Finite

/-!
The universal cycle-union reduction. A generated subgraph is built from actual
triangles and quadrilaterals by adjoining cycles sharing an edge. No cutoff on
the ambient graph, no catalogue membership and no routing assumption occurs.
-/
namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

def IsShortCycle (C : G.Subgraph) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsCycle ∧ p.length ≤ 4 ∧ C = p.toSubgraph

inductive CycleGenerated (G : SimpleGraph V) : G.Subgraph → Prop where
  | base {C} : IsShortCycle C → CycleGenerated G C
  | attach {H C} : CycleGenerated G H → IsShortCycle C →
      (∃ u v, H.Adj u v ∧ C.Adj u v) → CycleGenerated G (H ⊔ C)

theorem CycleGenerated.nonempty {H : G.Subgraph} (h : CycleGenerated G H) :
    H.verts.Nonempty := by
  induction h with
  | base hc =>
    obtain ⟨v, p, _, _, rfl⟩ := hc
    exact ⟨v, p.start_mem_verts_toSubgraph⟩
  | attach _ _ _ ih =>
    exact ih.mono Set.subset_union_left

theorem CycleGenerated.vertex_cycle {H : G.Subgraph} (h : CycleGenerated G H)
    {v : V} (hv : v ∈ H.verts) :
    ∃ C : G.Subgraph, IsShortCycle C ∧ C ≤ H ∧ v ∈ C.verts := by
  induction h with
  | base hc => exact ⟨_, hc, le_rfl, hv⟩
  | @attach H C hH hC hedge ih =>
    rcases hv with hv | hv
    · obtain ⟨D, hD, hle, hv⟩ := ih hv
      exact ⟨D, hD, hle.trans le_sup_left, hv⟩
    · exact ⟨C, hC, le_sup_right, hv⟩

theorem cycleGenerated_shared_edge [Fintype V] [DecidableRel G.Adj]
    (hdeg : ∀ v, G.degree v ≤ 3) {H C : G.Subgraph}
    (hH : CycleGenerated G H) (hC : IsShortCycle C)
    {v : V} (hvH : v ∈ H.verts) (hvC : v ∈ C.verts) :
    ∃ u w, H.Adj u w ∧ C.Adj u w := by
  classical
  obtain ⟨D, hD, hDH, hvD⟩ := hH.vertex_cycle hvH
  obtain ⟨a, p, hp, _, rfl⟩ := hD
  obtain ⟨b, q, hq, _, rfl⟩ := hC
  obtain ⟨w, hpw, hqw⟩ := ZombieStructure.cycles_share_edge G hdeg p q hp hq
    (p.mem_verts_toSubgraph.mp hvD) (q.mem_verts_toSubgraph.mp hvC)
  exact ⟨v, w, hDH.2 hpw, hqw⟩

/-- In a connected subcubic graph whose edges all belong to short cycles,
the whole graph has an edge-sharing short-cycle construction. -/
theorem cycleGenerated_top [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hdeg : ∀ v, G.degree v ≤ 3)
    (hedge : ∃ u v, G.Adj u v)
    (hshort : ∀ u v, G.Adj u v → ∃ C : G.Subgraph,
      IsShortCycle C ∧ C.Adj u v) :
    CycleGenerated G ⊤ := by
  classical
  have hex : {H : G.Subgraph | CycleGenerated G H}.Nonempty := by
    obtain ⟨u, v, huv⟩ := hedge
    obtain ⟨C, hC, _⟩ := hshort u v huv
    exact ⟨C, CycleGenerated.base hC⟩
  obtain ⟨H, hH, hmax⟩ := (Set.toFinite {H : G.Subgraph | CycleGenerated G H}).exists_maximal hex
  have hclosed : ∀ u v, u ∈ H.verts → G.Adj u v → H.Adj u v := by
    intro u v hu huv
    obtain ⟨C, hC, hCu⟩ := hshort u v huv
    have hshare := cycleGenerated_shared_edge hdeg hH hC hu hCu.fst_mem
    have hgen := CycleGenerated.attach hH hC hshare
    have hle : H ⊔ C ≤ H := hmax hgen le_sup_left
    exact hle.2 (Or.inr hCu)
  obtain ⟨root, hroot⟩ := hH.nonempty
  have hall : ∀ v, v ∈ H.verts := by
    intro v
    obtain ⟨p⟩ := hconn.preconnected root v
    have propagate : ∀ {a b : V}, G.Walk a b → a ∈ H.verts → b ∈ H.verts := by
      intro a b walk
      induction walk with
      | nil => exact id
      | cons hab tail ih => exact fun ha => ih (hclosed _ _ ha hab).snd_mem
    exact propagate p hroot
  have htop : H = ⊤ := by
    apply le_antisymm le_top
    exact ⟨fun v _ => hall v, fun u v huv => hclosed u v (hall u) huv⟩
  exact htop ▸ hH

end ZombieMain
