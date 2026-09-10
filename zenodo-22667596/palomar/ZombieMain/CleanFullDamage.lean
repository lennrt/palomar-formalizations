import ZombieMain.CleanInitialization
import ZombieDamage.Covering

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The complete clean-edge branch of the main theorem: actual initial
placement, every zombie reply, all target departures and the stated budget. -/
theorem full_damage_of_clean_edge (hconn : G.Connected) (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    (hclean : ∃ p q,(gameGraph G).Clean p q) :
    FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) := by
  classical
  obtain ⟨p,q,hpq⟩ := hclean
  let targets := (Finset.univ : Finset V).toList
  have hevery : ∀ v,v∈targets := by intro v; simp [targets]
  have hlen : targets.length=Fintype.card V := by simp [targets]
  have hr := fullDamage_of_contract (gameGraph G)
    (fun s => (gameGraph G).Clean s.zombie s.survivor)
    (2*Fintype.card V) (2*Fintype.card V) targets hevery
    (target_contract hconn hcubic hbridge)
    (clean_initialization hconn hcubic hbridge p q hpq)
  rwa [hlen,twice_order_bound] at hr

end ZombieMain
