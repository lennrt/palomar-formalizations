import ZombieMain.RoutedPresentation
import ZombieMain.PreciseAmbientExit

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Routing statements expressed solely in the original graph and game.
The prescribed exit retains both endpoints of the oriented clean edge. -/
structure ComponentRouting (G : SimpleGraph V) (K : (shortGraph G).ConnectedComponent)
    (cost : Nat) : Prop where
  exit_route : ∀ s : State V, (gameGraph G).Clean s.zombie s.survivor → s.survivor∈K.supp →
    ∀ q w, q∈K.supp → (gameGraph G).Clean q w → (q≠s.survivor ∨ w≠s.zombie) →
    ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
      t.zombie=q ∧ t.survivor=w) cost .survivor s
  target_route : ∀ s : State V, (gameGraph G).Clean s.zombie s.survivor → s.survivor∈K.supp →
    ∀ x, x∈K.supp → ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
      (gameGraph G).Clean t.zombie t.survivor ∧ t.zombie∈K.supp ∧
      (t.zombie≠s.survivor ∨ t.survivor≠s.zombie) ∧ t.damaged x) cost .survivor s

theorem component_entry_port {D : Diagram} (K : (shortGraph G).ConnectedComponent)
    [Nontrivial K] (e : D.Embedding (shortComponent G K)) (hcubic : ∀ v,G.degree v=3)
    (i : Fin D.order) {z : V} (hc : (gameGraph G).Clean (e.vertices i) z) : D.degree i.val=2 := by
  rw [e.degree]
  exact new_edge_endpoint_degree (shortComponent_min_degree K _ (e.mem i))
    (by rw [hcubic]) hc.1 (shortComponent_clean_missing K hc)

namespace RoutedPresentation
variable {D : Diagram} (R : RoutedPresentation D)
variable (K : (shortGraph G).ConnectedComponent) [Nontrivial K]
variable (e : D.Embedding (shortComponent G K)) (hcubic : ∀ v,G.degree v=3)
include R e hcubic

/-- A prescribed exit in the actual ambient graph, with no assumed model. -/
theorem ambient_exit (s : State V) (hc : (gameGraph G).Clean s.zombie s.survivor)
    (hs : s.survivor∈K.supp) (q w : V) (hq : q∈K.supp)
    (hqw : (gameGraph G).Clean q w) (hne : q≠s.survivor) :
    ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
      t.zombie=q ∧ t.survivor=w) (2*D.order) .survivor s := by
  classical
  obtain ⟨i,hi⟩ := e.exists_label hs
  obtain ⟨j,hj⟩ := e.exists_label hq
  have hci : (gameGraph G).Clean (e.vertices i) s.zombie := by
    rw [hi]; exact (gameGraph G).clean_symm hc
  have hcj : (gameGraph G).Clean (e.vertices j) w := by rw [hj]; exact hqw
  obtain ⟨a,ha,hia⟩ := (R.presentation.port_stub i).mp (component_entry_port K e hcubic i hci)
  obtain ⟨b,hb,hjb⟩ := (R.presentation.port_stub j).mp (component_entry_port K e hcubic j hcj)
  let P := R.presentation.retarget none (fun v => decide (v=b))
  let M := P.ambientModel K e hcubic s.survivor
  have hiM := P.ambientModel_entry K e hcubic s.survivor i a ha hia hci
  have hjM := P.ambientModel_entry K e hcubic s.survivor j b hb hjb hcj
  have hne' : R.presentation.internal i≠R.presentation.internal j := by
    intro he
    have hij := R.presentation.internal_injective he
    exact hne (hj.symm.trans ((congrArg e.vertices hij).symm.trans hi))
  have hr := R.exit_route _ a _ b (R.presentation.internal_inside i)
    (R.presentation.internal_inside j) ha hb hia hjb hne'
  have ht := M.metricForcesWithin_precise P.good hr s.damaged (by intro h; cases h)
  have hstate : M.state ⟨false,a,R.presentation.internal i⟩ s.damaged=s := by
    change (⟨M.map a,M.map (P.internal i),s.damaged⟩ : State V)=s
    rw [hiM.1,hiM.2,hi]
  rw [hstate] at ht
  apply ht.mono
  intro phase t h
  obtain ⟨u,v,hu,hv,huv,hvallow,hz,hsur⟩ := h.2.2.1
  have hvb : v=b := of_decide_eq_true hvallow
  subst v
  have hub : u=P.internal j := P.boundary_leaves b hb u (P.internal j)
    (by rw [P.good.1]; exact huv) (by rw [P.good.1]; exact hjb)
  refine ⟨h.1,?_,?_⟩
  · rw [hz,hub,hjM.1,hj]
  · rw [hsur,hjM.2]

/-- Target service in the actual ambient graph, leaving by a nonentry port. -/
theorem ambient_target (s : State V) (hc : (gameGraph G).Clean s.zombie s.survivor)
    (hs : s.survivor∈K.supp) (x : V) (hx : x∈K.supp) :
    ForcesWithin (gameGraph G) (fun phase t => phase=.survivor ∧
      (gameGraph G).Clean t.zombie t.survivor ∧ t.zombie∈K.supp ∧
      t.zombie≠s.survivor ∧ t.damaged x) (2*D.order) .survivor s := by
  classical
  obtain ⟨i,hi⟩ := e.exists_label hs
  obtain ⟨k,hk⟩ := e.exists_label hx
  have hci : (gameGraph G).Clean (e.vertices i) s.zombie := by
    rw [hi]; exact (gameGraph G).clean_symm hc
  obtain ⟨a,ha,hia⟩ := (R.presentation.port_stub i).mp (component_entry_port K e hcubic i hci)
  let P := R.presentation.retarget (some (R.presentation.internal k)) (fun v => decide (v≠a))
  let M := P.ambientModel K e hcubic s.survivor
  have hiM := P.ambientModel_entry K e hcubic s.survivor i a ha hia hci
  have hkM : M.map (R.presentation.internal k)=x :=
    (P.ambientMap_internal e hcubic s.survivor k).trans hk
  have hr := R.target_route _ a _ (R.presentation.internal_inside i) ha hia
    (R.presentation.internal_inside k)
  have ht := M.metricForcesWithin_precise P.good hr s.damaged (by intro h; cases h)
  have hstate : M.state ⟨false,a,R.presentation.internal i⟩ s.damaged=s := by
    change (⟨M.map a,M.map (P.internal i),s.damaged⟩ : State V)=s
    rw [hiM.1,hiM.2,hi]
  rw [hstate] at ht
  apply ht.mono
  intro phase t h
  obtain ⟨u,v,hu,hv,huv,hvallow,hz,hsur⟩ := h.2.2.1
  refine ⟨h.1,h.2.1,?_,?_,?_⟩
  · rw [hz]
    change P.ambientMap e hcubic s.survivor u∈K.supp
    rw [P.ambientMap_inside e hcubic s.survivor u hu]
    exact e.mem _
  · intro he
    have he' : M.map u=M.map (P.internal i) := by rw [← hz,he,hiM.1,hi]
    have hui : u=P.internal i := M.internal_injective _ _ hu (P.internal_inside i) he'
    have hva : v=a := P.one_stub v (P.internal i) a (P.internal_inside i) hv ha
      (by rw [← hui,P.good.1]; exact huv) hia
    exact (of_decide_eq_true hvallow) hva
  · have hd := h.2.2.2 (R.presentation.internal k) rfl
    rwa [hkM] at hd

/-- Both ambient routing obligations follow from the exact local presentation. -/
theorem ambient : ComponentRouting G K (2*D.order) where
  exit_route := by
    intro s hc hs q w hq hqw hne
    apply R.ambient_exit K e hcubic s hc hs q w hq hqw
    intro he
    have hw : w=s.zombie := new_neighbors_subsingleton
      (shortComponent_min_degree K _ hq) (by rw [hcubic])
      ⟨hqw.1,shortComponent_clean_missing K hqw⟩
      (by rw [he]; exact ⟨hc.1.symm,shortComponent_clean_missing K ((gameGraph G).clean_symm hc)⟩)
    exact hne.elim (fun h => h he) (fun h => h hw)
  target_route := by
    intro s hc hs x hx
    apply (R.ambient_target K e hcubic s hc hs x hx).mono
    intro phase t h
    exact ⟨h.1,h.2.1,h.2.2.1,Or.inl h.2.2.2.1,h.2.2.2.2⟩

end RoutedPresentation
end ZombieMain
