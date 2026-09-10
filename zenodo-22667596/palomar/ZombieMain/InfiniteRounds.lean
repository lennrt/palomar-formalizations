import ZombieMain.QuotientRouting

namespace ZombieMain
open ZombieDamage ZombieDamage.FullGame
variable {V : Type} {G : SimpleGraph V}

/-- One genuine survivor move and all ensuing zombie replies extracted from
a finite target-service proof whose objective has not yet been reached. -/
structure RoundPlan (x : V) (budget : Nat) (s : State V) where
  remaining : Nat
  move : V
  decreases : remaining<budget
  live : s.zombie≠s.survivor
  legal : LegalSurvivor (gameGraph G) s move
  replies : ∃y,(gameGraph G).GeodesicReply s.zombie move y
  safe : ∀y,(gameGraph G).GeodesicReply s.zombie move y → y≠move
  continuation : ∀y,(gameGraph G).GeodesicReply s.zombie move y →
    ForcesWithin (gameGraph G) (TargetEntry G x) remaining .survivor
      ((s.survivorTo move).zombieTo y)

theorem roundPlan_exists {x : V} {b : Nat} {s : State V}
    (h : ForcesWithin (gameGraph G) (TargetEntry G x) b .survivor s)
    (hn : ¬TargetEntry G x .survivor s) : Nonempty (RoundPlan (G:=G) x b s) := by
  cases h with
  | done _ _ _ hp => exact False.elim (hn hp)
  | survivor k _ w hl hw hnext =>
    cases hnext with
    | done _ _ _ hp => cases hp.1
    | zombie _ _ _ hex hcap hcont =>
      exact ⟨⟨k,w,Nat.lt_succ_self k,hl,hw,hex,hcap,hcont⟩⟩

/-- Private controller memory. The damage set records only the current
service interval and is reset at its completion; positions remain actual. -/
structure RouteMemory (G : SimpleGraph V) (f : Nat → V) (B : Nat) where
  stage : Nat
  state : State V
  budget : Nat
  bounded : budget≤B
  certificate : ForcesWithin (gameGraph G) (TargetEntry G (f stage)) budget .survivor state
  unfinished : ¬TargetEntry G (f stage) .survivor state

namespace RouteMemory
variable {f : Nat → V} {B : Nat}
noncomputable def plan (m : RouteMemory G f B) : RoundPlan (G:=G) (f m.stage) m.budget m.state :=
  Classical.choice (roundPlan_exists m.certificate m.unfinished)

def RoutingAvailable (G : SimpleGraph V) (B : Nat) : Prop :=
  ∀s : State V,(gameGraph G).Clean s.zombie s.survivor → ∀x,
    ForcesWithin (gameGraph G) (TargetEntry G x) B .survivor s

noncomputable def fresh (route : RoutingAvailable G B) (f : Nat → V) (stage : Nat)
    (z p : V) (hc : (gameGraph G).Clean z p) : RouteMemory G f B where
  stage := stage
  state := initial z p
  budget := B
  bounded := le_rfl
  certificate := route (initial z p) hc (f stage)
  unfinished := fun h => h.2.2

noncomputable def advance (route : RoutingAvailable G B) (m : RouteMemory G f B)
    (y : V) (hy : (gameGraph G).GeodesicReply m.state.zombie m.plan.move y) : RouteMemory G f B := by
  classical
  let t := (m.state.survivorTo m.plan.move).zombieTo y
  exact if ht : TargetEntry G (f m.stage) .survivor t then
    fresh route f (m.stage+1) t.zombie t.survivor ht.2.1
  else
    { stage := m.stage
      state := t
      budget := m.plan.remaining
      bounded := (Nat.le_of_lt m.plan.decreases).trans m.bounded
      certificate := m.plan.continuation y hy
      unfinished := ht }

def Next (route : RoutingAvailable G B) (m n : RouteMemory G f B) : Prop :=
  ∃ y,∃hy : (gameGraph G).GeodesicReply m.state.zombie m.plan.move y,
    advance route m y hy=n

theorem next_exists (route : RoutingAvailable G B) (m : RouteMemory G f B) : ∃n,Next route m n := by
  obtain ⟨y,hy⟩ := m.plan.replies
  exact ⟨advance route m y hy,y,hy,rfl⟩

theorem advance_facts (route : RoutingAvailable G B) (m : RouteMemory G f B)
    (y : V) (hy : (gameGraph G).GeodesicReply m.state.zombie m.plan.move y) :
    let n := advance route m y hy
    n.state.zombie=y ∧ n.state.survivor=m.plan.move ∧
      ((n.stage=m.stage ∧ n.budget<m.budget) ∨
        (n.stage=m.stage+1 ∧ n.budget=B ∧
          (m.state.damaged (f m.stage) ∨ f m.stage=m.state.survivor) ∧
          ∀x,¬n.state.damaged x)) ∧
      (∀x,n.state.damaged x → m.state.damaged x ∨ x=m.state.survivor) := by
  classical
  dsimp [advance]
  split_ifs with ht
  · exact ⟨rfl,rfl,Or.inr ⟨rfl,rfl,ht.2.2,fun x h => h⟩,fun x h => False.elim h⟩
  · exact ⟨rfl,rfl,Or.inl ⟨rfl,m.plan.decreases⟩,fun _ h => h⟩

theorem next_facts (route : RoutingAvailable G B) {m n : RouteMemory G f B}
    (h : Next route m n) :
    (∃y,(gameGraph G).GeodesicReply m.state.zombie m.plan.move y ∧
      n.state.zombie=y ∧ n.state.survivor=m.plan.move) ∧
    ((n.stage=m.stage ∧ n.budget<m.budget) ∨
      (n.stage=m.stage+1 ∧ n.budget=B ∧
        (m.state.damaged (f m.stage) ∨ f m.stage=m.state.survivor) ∧
        ∀x,¬n.state.damaged x)) ∧
    (∀x,n.state.damaged x → m.state.damaged x ∨ x=m.state.survivor) := by
  obtain ⟨y,hy,rfl⟩ := h
  have h := advance_facts route m y hy
  exact ⟨⟨y,hy,h.1,h.2.1⟩,h.2.2.1,h.2.2.2⟩

end RouteMemory
end ZombieMain
