import ZombieMain.PortedPresentation

namespace ZombieDamage.Task
variable {N : Nat} {T : Task N} {hg : T.GoodGraph}

/-- Enlarging the permitted exit set preserves every metric strategy. -/
theorem MetricForcesWithin.allowed_mono {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (allowed : Fin N → Bool)
    (ha : ∀ w, T.allowedExit w=true → allowed w=true) :
    ({T with allowedExit := allowed} : Task N).MetricForcesWithin hg b s := by
  induction h with
  | exit budget s w hb hs he =>
    exact .exit budget s w hb hs ⟨he.1,ha w he.2.1,he.2.2⟩
  | step budget s w hs hi hex hn ih =>
    exact .step budget s w hs hi hex ih

/-- Unused survivor-move budget can be added without changing a strategy. -/
theorem MetricForcesWithin.pad {b : Nat} {s : Position N}
    (h : T.MetricForcesWithin hg b s) (c : Nat) :
    T.MetricForcesWithin hg (b+c) s := by
  induction h with
  | exit budget s w hb hs he => exact .exit _ s w (by omega) hs he
  | step budget s w hs hi hex hn ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      MetricForcesWithin.step (budget+c) s w hs hi hex ih

end ZombieDamage.Task
