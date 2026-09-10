import MainSolution
import ZombieDamage
import ZombieMain.NumericalConjecture

/-! Faithful renderer-compatible interfaces for thirteen existing results.
The four transparent helpers spell ordinary degree, vertex pairs, and equality
decisions. Every theorem below is proved directly by the original theorem;
there are no new hypotheses, weakened conclusions, or additional axioms.
This avoids the trusted renderer's alias-proxy issue (PalomarSubmission #134).
-/


noncomputable def PalomarVerified.degree {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Nat := G.degree v


namespace ZombieDamage.DiamondRing


def _root_.PalomarVerified.diamondVertex (k : Nat) (i : Fin (k + 3)) (r : Role) : Vertex k := (i, r)

theorem _root_.PalomarVerified.central_pair_sensor (k : Nat) (S : Vertex k → Prop) (h : Nat) (hh : 1 ≤ h) (hrec : (graph k).Recovers S h) (i
    : Fin (k + 3)) : S (PalomarVerified.diamondVertex k i .a) ∨ S (PalomarVerified.diamondVertex k i .b) := by
  exact ZombieDamage.DiamondRing.central_pair_sensor k S h hh hrec i


end ZombieDamage.DiamondRing
namespace ZombieDamage.OpenStrip
open FullGame Cyclic
variable (m : Nat) (hm : 2≤m) (left right : Bool)


def _root_.PalomarVerified.portEq (p q : Port) : Bool := decide (p = q)

def _root_.PalomarVerified.portNe (p q : Port) : Bool := decide (p ≠ q)

theorem _root_.PalomarVerified.metric_exit_contract (entry q : Port) (hin : Active left right entry) (hq : Active left right q) (hne :
    q≠entry) : (task m left right none (fun p => PalomarVerified.portEq p q)).MetricForcesWithin (task_good m hm left right none
    (fun p => PalomarVerified.portEq p q)) (2*m) ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  exact ZombieDamage.OpenStrip.metric_exit_contract m hm left right entry q hin hq hne

theorem _root_.PalomarVerified.metric_target_contract (entry : Port) (hin : Active left right entry) (x : Fin (2*m+8)) (hx : Internal m left
    right x) : (task m left right (some x) (fun p => PalomarVerified.portNe p entry)).MetricForcesWithin (task_good m hm left right
    (some x) (fun p => PalomarVerified.portNe p entry)) (2*m) ⟨false,portStub m entry,portVertex m hm entry⟩ := by
  exact ZombieDamage.OpenStrip.metric_target_contract m hm left right entry hin x hx


end ZombieDamage.OpenStrip
namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]


theorem _root_.PalomarVerified.full_damage_within_iff (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v →
    ¬G.IsBridge s(u,v)) : FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) ↔ ¬IsException G := by
  exact ZombieMain.full_damage_within_iff hconn hcubic hbridge

theorem _root_.PalomarVerified.full_damage_iff (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge
    s(u,v)) : FullDamage (gameGraph G) ↔ ¬IsException G := by
  exact ZombieMain.full_damage_iff hconn hcubic hbridge

theorem _root_.PalomarVerified.davila_conjecture_24 (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge
    s(u,v)) (hn : 10≤Fintype.card V) : FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) := by
  exact ZombieMain.davila_conjecture_24 hconn hcubic hbridge hn

theorem _root_.PalomarVerified.full_damage_of_clean_edge (hconn : G.Connected) (hcubic : ∀v,PalomarVerified.degree G v=3) (hbridge : ∀u v,G.Adj u v →
    ¬G.IsBridge s(u,v)) (hclean : ∃p q,(gameGraph G).Clean p q) : FullDamageWithin (gameGraph G) (2*Fintype.card
    V*(Fintype.card V+1)) := by
  exact ZombieMain.full_damage_of_clean_edge hconn hcubic hbridge hclean

theorem _root_.PalomarVerified.recurrent_coverage_of_clean_edge {W : Type} {H : SimpleGraph W} [Fintype W] [DecidableRel H.Adj] (hconn :
    H.Connected) (hcubic : ∀v,PalomarVerified.degree H v=3) (hbridge : ∀u v,H.Adj u v → ¬H.IsBridge s(u,v)) (hclean : ∃p q,(gameGraph
    H).Clean p q) : RecurrentCoverageWithin (gameGraph H) (2*Fintype.card W) := by
  exact ZombieMain.recurrent_coverage_of_clean_edge hconn hcubic hbridge hclean

theorem _root_.PalomarVerified.four_boundary_edges (H : G.Subgraph) (hconn : H.coe.Connected) (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard)
    (hmax : ∀v,PalomarVerified.degree G v≤3) (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v) :
    (cutPairs G H.verts).ncard≤4 := by
  exact ZombieMain.four_boundary_edges H hconn hmin hmax hshort

theorem _root_.PalomarVerified.short_component_expansion (H : G.Subgraph) (hconn : H.coe.Connected) (hmin : ∀v∈H.verts,2≤(H.neighborSet
    v).ncard) (hmax : ∀v,PalomarVerified.degree G v≤3) (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v)
    (η : ℝ) (hη : 0<η) (hex : HasEdgeExpansion G η) : ((min H.verts.ncard (Fintype.card V-H.verts.ncard) : Nat) :
    ℝ)≤4/η := by
  exact ZombieMain.short_component_expansion H hconn hmin hmax hshort η hη hex

theorem _root_.PalomarVerified.davila_conjecture_24_damage_number (hconn : G.Connected) (hcubic : ∀ v, PalomarVerified.degree G v = 3) (hbridge : ∀ u v,
    G.Adj u v → ¬G.IsBridge s(u,v)) (hn : 10 ≤ Fintype.card V) : zombieDamageNumber (gameGraph G) = Fintype.card V := by
  exact ZombieMain.davila_conjecture_24_damage_number hconn hcubic hbridge hn


section Structural
variable {W : Type*} [Fintype W] {H : SimpleGraph W} [DecidableRel H.Adj]


theorem _root_.PalomarVerified.four_port_principle (hconn : H.Connected) (hmin : ∀v,2≤PalomarVerified.degree H v) (hmax : ∀v,PalomarVerified.degree H v≤3) (hshort : ∀u
    v,H.Adj u v → ∃C : H.Subgraph,IsShortCycle C ∧ C.Adj u v) : (∑v,(3-PalomarVerified.degree H v))≤4 ∧ (Finset.univ.filter (fun v =>
    PalomarVerified.degree H v=2)).card≤4 := by
  exact ZombieMain.four_port_principle hconn hmin hmax hshort

theorem _root_.PalomarVerified.cycle_union_classification (hconn : H.Connected) (hmin : ∀v,2≤PalomarVerified.degree H v) (hmax : ∀v,PalomarVerified.degree H v≤3) (hshort :
    ∀u v,H.Adj u v → ∃C : H.Subgraph,IsShortCycle C ∧ C.Adj u v) : ClassifiedSubgraph (⊤ : H.Subgraph) := by
  exact ZombieMain.cycle_union_classification hconn hmin hmax hshort

end Structural
end ZombieMain
