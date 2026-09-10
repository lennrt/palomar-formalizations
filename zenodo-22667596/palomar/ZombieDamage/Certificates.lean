import ZombieDamage.Graph

namespace ZombieDamage

structure Position (N : Nat) where
  seen : Bool
  zombie : Fin N
  survivor : Fin N
  deriving DecidableEq, Repr

structure Task (N : Nat) where
  adj : Fin N → Fin N → Bool
  inside : Fin N → Bool
  target : Option (Fin N)
  allowedExit : Fin N → Bool

namespace Task
variable {N : Nat}

def GoodGraph (T : Task N) : Prop :=
  (∀ u v, T.adj u v = T.adj v u) ∧ ∀ u, T.adj u u = false

instance (T : Task N) : Decidable T.GoodGraph := by
  unfold GoodGraph
  infer_instance

def graph (T : Task N) (h : T.GoodGraph) : Graph (Fin N) where
  adj u v := T.adj u v = true
  symm := by
    intro u v huv
    rw [← h.1 u v]
    exact huv
  loopless := by
    intro v hv
    rw [h.2 v] at hv
    cases hv

/-- Targets are credited on departure from the SOURCE survivor vertex. -/
def afterSeen (T : Task N) (s : Position N) : Bool :=
  s.seen || match T.target with
    | none => true
    | some t => decide (s.survivor = t)

def next (T : Task N) (s : Position N) (w z : Fin N) : Position N :=
  ⟨T.afterSeen s, z, w⟩

def Safe (T : Task N) (s : Position N) (w : Fin N) : Prop :=
  T.inside s.survivor = true ∧
  T.adj s.zombie s.survivor = true ∧
  T.adj s.survivor w = true ∧
  s.zombie ≠ w ∧ T.adj s.zombie w = false

def Reply (T : Task N) (s : Position N) (w z : Fin N) : Prop :=
  T.adj s.zombie z = true ∧ T.adj z w = true

def Exit (T : Task N) (s : Position N) (w : Fin N) : Prop :=
  T.inside w = false ∧ T.allowedExit w = true ∧ T.afterSeen s = true

instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Safe s w) := by unfold Safe; infer_instance
instance (T : Task N) (s : Position N) (w z : Fin N) :
    Decidable (T.Reply s w z) := by unfold Reply; infer_instance
instance (T : Task N) (s : Position N) (w : Fin N) :
    Decidable (T.Exit s w) := by unfold Exit; infer_instance

theorem safe_twoApart (T : Task N) (hg : T.GoodGraph)
    {s : Position N} {w : Fin N} (hs : T.Safe s w) :
    (T.graph hg).TwoApart s.zombie w := by
  rcases hs with ⟨_, huv, hvw, hne, hno⟩
  refine ⟨hne, ?_, s.survivor, huv, hvw⟩
  change ¬ T.adj s.zombie w = true
  rw [hno]
  decide

theorem safe_replies_are_geodesic (T : Task N) (hg : T.GoodGraph)
    {s : Position N} {w z : Fin N} (hs : T.Safe s w) :
    T.Reply s w z ↔ (T.graph hg).GeodesicReply s.zombie w z := by
  exact ((T.graph hg).geodesicReply_iff_commonNeighbor
    (T.safe_twoApart hg hs)).symm

/-- A finite survivor strategy tree. The step constructor quantifies over
EVERY legal zombie response. Exit is permitted only after the target flag is
true. The ambient-component transfer theorem is NOT formalized here. -/
inductive Forces (T : Task N) : Position N → Prop where
  | exit (s : Position N) (w : Fin N) :
      T.Safe s w → T.Exit s w → Forces T s
  | step (s : Position N) (w : Fin N) :
      T.Safe s w → T.inside w = true →
      (∃ z, T.Reply s w z) →
      (∀ z, T.Reply s w z → Forces T (T.next s w z)) → Forces T s


/-- The same finite forcing objective, now stated with actual shortest-walk
geodesic replies in the graph rather than the common-neighbor abbreviation. -/
inductive MetricForces (T : Task N) (hg : T.GoodGraph) : Position N → Prop where
  | exit (s : Position N) (w : Fin N) :
      T.Safe s w → T.Exit s w → MetricForces T hg s
  | step (s : Position N) (w : Fin N) :
      T.Safe s w → T.inside w = true →
      (∃ z, (T.graph hg).GeodesicReply s.zombie w z) →
      (∀ z, (T.graph hg).GeodesicReply s.zombie w z →
        MetricForces T hg (T.next s w z)) → MetricForces T hg s

theorem forces_metric (T : Task N) (hg : T.GoodGraph)
    {s : Position N} (h : T.Forces s) : T.MetricForces hg s := by
  induction h with
  | exit s w hs he => exact MetricForces.exit _ _ hs he
  | step s w hs hi hn hc ih =>
    apply MetricForces.step _ _ hs hi
    · obtain ⟨z, hz⟩ := hn
      exact ⟨z, (T.safe_replies_are_geodesic hg hs).1 hz⟩
    · intro z hz
      exact ih z ((T.safe_replies_are_geodesic hg hs).2 hz)

/-- Finite-horizon forcing in the shortest-walk metric. `budget` counts survivor
moves including the exit; an early exit may leave some budget unused.
The step constructor includes all geodesic replies and requires at least one,
so a position with no replies is not a vacuous winning position. -/
inductive MetricForcesWithin (T : Task N) (hg : T.GoodGraph) :
    Nat → Position N → Prop where
  | exit (budget : Nat) (s : Position N) (w : Fin N) :
      0 < budget → T.Safe s w → T.Exit s w →
      MetricForcesWithin T hg budget s
  | step (budget : Nat) (s : Position N) (w : Fin N) :
      T.Safe s w → T.inside w = true →
      (∃ z, (T.graph hg).GeodesicReply s.zombie w z) →
      (∀ z, (T.graph hg).GeodesicReply s.zombie w z →
        MetricForcesWithin T hg budget (T.next s w z)) →
      MetricForcesWithin T hg (Nat.succ budget) s

structure Row (N : Nat) where
  state : Position N
  move : Fin N
  rank : Nat
  deriving DecidableEq, Repr

def RowValid {K : Nat} (T : Task N) (rows : Fin K → Row N)
    (i : Fin K) : Prop :=
  let r := rows i
  0 < r.rank ∧ T.Safe r.state r.move ∧
  (T.Exit r.state r.move ∨
    (T.inside r.move = true ∧
      (∃ z, T.Reply r.state r.move z) ∧
      ∀ z, T.Reply r.state r.move z →
        ∃ j : Fin K, (rows j).state = T.next r.state r.move z ∧
          (rows j).rank < r.rank))

instance {K : Nat} (T : Task N) (rows : Fin K → Row N) (i : Fin K) :
    Decidable (T.RowValid rows i) := by
  unfold RowValid
  infer_instance

/-- Soundness of ranked local strategy certificates by ordinary induction.
There is no search oracle or evaluator axiom in this proof. -/
theorem certificate_sound {K : Nat} (T : Task N) (rows : Fin K → Row N)
    (valid : ∀ i, T.RowValid rows i) :
    ∀ i, T.Forces (rows i).state := by
  have bounded : ∀ b : Nat, ∀ i : Fin K,
      (rows i).rank < b → T.Forces (rows i).state := by
    intro b
    induction b with
    | zero =>
      intro i hi
      exact False.elim (Nat.not_lt_zero _ hi)
    | succ b ih =>
      intro i hi
      obtain ⟨_, hs, hfinish⟩ := valid i
      rcases hfinish with hexit | ⟨hinside, hnonempty, hnext⟩
      · exact Forces.exit _ _ hs hexit
      · apply Forces.step _ _ hs hinside hnonempty
        intro z hz
        obtain ⟨j, hstate, hrank⟩ := hnext z hz
        have hj := ih j (Nat.lt_of_lt_of_le hrank (Nat.le_of_lt_succ hi))
        rw [hstate] at hj
        exact hj
  intro i
  exact bounded (Nat.succ (rows i).rank) i (Nat.lt_succ_self _)


/-- Extensional equality of tasks; used to bridge raw certificate data to
independently specified graph families, rather than advertising raw rows. -/
theorem ext {T U : Task N}
    (ha : ∀ u v, T.adj u v = U.adj u v)
    (hi : ∀ v, T.inside v = U.inside v)
    (ht : T.target = U.target)
    (he : ∀ v, T.allowedExit v = U.allowedExit v) : T = U := by
  cases T with
  | mk ta ti tt te =>
    cases U with
    | mk ua ui ut ue =>
      have h1 : ta = ua := funext (fun u => funext (ha u))
      have h2 : ti = ui := funext hi
      have h3 : tt = ut := ht
      have h4 : te = ue := funext he
      cases h1
      cases h2
      cases h3
      cases h4
      rfl

/-- A validated rank is a genuine survivor-move bound, not merely evidence
of some terminating play. Every possible geodesic reply is included. -/
theorem certificate_bounded {K : Nat} (T : Task N) (hg : T.GoodGraph)
    (rows : Fin K → Row N) (valid : ∀ i, T.RowValid rows i) :
    ∀ budget (i : Fin K), (rows i).rank ≤ budget →
      T.MetricForcesWithin hg budget (rows i).state := by
  intro budget
  induction budget with
  | zero =>
    intro i hi
    have hp := (valid i).1
    exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hp hi))
  | succ budget ih =>
    intro i hi
    obtain ⟨hp, hs, hf⟩ := valid i
    rcases hf with hexit | ⟨hinside, hnonempty, hnext⟩
    · exact MetricForcesWithin.exit _ _ _ (Nat.zero_lt_succ _) hs hexit
    · apply MetricForcesWithin.step _ _ _ hs hinside
      · obtain ⟨z, hz⟩ := hnonempty
        exact ⟨z, (T.safe_replies_are_geodesic hg hs).1 hz⟩
      · intro z hz
        have hr := (T.safe_replies_are_geodesic hg hs).2 hz
        obtain ⟨j, hstate, hj⟩ := hnext z hr
        have hle : (rows j).rank ≤ budget :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hj hi)
        have hw := ih j hle
        rw [hstate] at hw
        exact hw

/-- Transport preserves the exact metric game, target, exits, and move bound. -/
theorem metric_within_transport (T U : Task N) (heq : T = U)
    (hg : T.GoodGraph) (budget : Nat) (s : Position N)
    (h : T.MetricForcesWithin hg budget s) :
    ∃ hu : U.GoodGraph, U.MetricForcesWithin hu budget s := by
  cases heq
  exact ⟨hg, h⟩

end Task
end ZombieDamage
