import ZombieMain.MainTheorem
import ZombieMain.GameValue

/-! Randy Davila's Conjecture 24 in its numerical form. This is a direct
corollary of the existing complete proof and the formal damage-value bridge. -/
namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem davila_conjecture_24_damage_number
    (hconn : G.Connected) (hcubic : ∀ v, G.degree v = 3)
    (hbridge : ∀ u v, G.Adj u v → ¬G.IsBridge s(u,v))
    (hn : 10 ≤ Fintype.card V) :
    zombieDamageNumber (gameGraph G) = Fintype.card V := by
  apply (zombieDamageNumber_eq_card_iff (by omega)).mpr
  exact ⟨_, davila_conjecture_24 hconn hcubic hbridge hn⟩

end ZombieMain
