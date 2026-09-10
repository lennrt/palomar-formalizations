import ZombieMain.SingletonRouting
import ZombieMain.FamilyRoutes

namespace ZombieMain
open SimpleGraph ZombieDamage
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Complete ambient routing for every actual component that can be entered
along a clean edge. The hypotheses mention only the original cubic graph. -/
theorem component_routing_at (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    (K : (shortGraph G).ConnectedComponent) {p z : V} (hp : p∈K.supp)
    (hclean : (gameGraph G).Clean z p) : ComponentRouting G K (2*K.supp.ncard) := by
  classical
  rcases subsingleton_or_nontrivial K with hsub | hnon
  · letI := hsub
    exact singleton_component_routing K hcubic
  · letI := hnon
    obtain ⟨f,hf,⟨e⟩⟩ := shortComponent_catalogue hcubic hbridge K
    obtain ⟨i,hi⟩ := e.exists_label hp
    have hci : (gameGraph G).Clean (e.vertices i) z := by
      rw [hi]; exact (gameGraph G).clean_symm hclean
    obtain ⟨R⟩ := f.routes_of_port hf ⟨i,component_entry_port K e hcubic i hci⟩
    have h := R.ambient K e hcubic
    have hc : K.supp.ncard=f.diagram.order := e.vertex_count
    rwa [hc]

end ZombieMain
