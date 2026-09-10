import ZombieMain.ShortCycles
import ZombieDamage.Exceptions
import ZombieDamage.Isomorphism

namespace ZombieMain
open ZombieDamage

/-- The four explicit graph-isomorphism exceptions, without a game premise. -/
def IsException {V : Type} (G : SimpleGraph V) : Prop :=
  ∃ kind : Exceptions.Kind,Nonempty (GraphIso (Exceptions.graph kind) (gameGraph G))


end ZombieMain
