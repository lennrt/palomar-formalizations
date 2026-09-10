import ZombieMain.RecurrentDefinitions
import ZombieMain.InfiniteProgress
import ZombieMain.CyclicRequests
import ZombieMain.CleanInitialization

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame
variable {V : Type} {G : SimpleGraph V} {f : Nat → V} {B : Nat}

noncomputable def routeController (route : RouteMemory.RoutingAvailable G B)
    (f : Nat → V) : SurvivorController (gameGraph G) where
  Memory := RouteMemory G f B
  zombie := fun m => m.state.zombie
  survivor := fun m => m.state.survivor
  move := fun m => m.plan.move
  live := fun m => m.plan.live
  legal := fun m => m.plan.legal
  replies := fun m => m.plan.replies
  safe := fun m => m.plan.safe
  next := RouteMemory.advance route
  next_zombie := fun m y h => (RouteMemory.advance_facts route m y h).1
  next_survivor := fun m y h => (RouteMemory.advance_facts route m y h).2.1

theorem routeController_recurrent (route : RouteMemory.RoutingAvailable G B)
    (hrequest : ∀ x N, ∃ i, N ≤ i ∧ f i = x) :
    (routeController route f).Recurrent := by
  intro m h x N
  exact RouteMemory.recurrent_departures route hrequest h x N

/-- The infinite-play form of the clean-edge theorem. No component model,
local contract, initialization, or progress premise is assumed. -/
theorem recurrent_coverage_of_clean_edge [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hcubic : ∀ v, G.degree v = 3)
    (hbridge : ∀ u v, G.Adj u v → ¬G.IsBridge s(u,v))
    (hclean : ∃ p q, (gameGraph G).Clean p q) :
    RecurrentCoverageWithin (gameGraph G) (2*Fintype.card V) := by
  classical
  obtain ⟨p,q,hpq⟩ := hclean
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨p⟩
  let route : RouteMemory.RoutingAvailable G (2*Fintype.card V) :=
    target_contract hconn hcubic hbridge
  let f := cyclicRequest (V:=V) hn
  refine ⟨routeController route f, routeController_recurrent route (cyclicRequest_cofinal hn), ?_⟩
  intro z
  obtain ⟨v,hv,hi⟩ := clean_initialization hconn hcubic hbridge p q hpq z
  refine ⟨v,hv,hi.mono ?_⟩
  intro phase s hs
  exact ⟨hs.1,RouteMemory.fresh route f 0 s.zombie s.survivor hs.2,rfl,rfl⟩

end ZombieMain
