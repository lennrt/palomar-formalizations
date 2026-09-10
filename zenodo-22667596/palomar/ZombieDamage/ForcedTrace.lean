import ZombieDamage.OriginalGameChecks

/-! All-length forced-trace theorem, corresponding to Davila's Lemma 12.
Each finite prefix is proved in the actual full game. Trace existence in an
arbitrary minimum-degree-two graph is a separate graph-theoretic obligation.
-/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

/-- A short-cycle-free nonbacktracking trace has all zombie replies forced. -/
theorem clean_trace_reply (f : Nat → V)
    (he : ∀ i, G.adj (f i) (f (i+1)))
    (hc : ∀ i, G.Clean (f (i+1)) (f (i+2)))
    (hn : ∀ i, f i ≠ f (i+2)) (i : Nat) (z : V) :
    G.GeodesicReply (f i) (f (i+2)) z ↔ z = f (i+1) :=
  G.cleanEdge_forces_reply (hc i) (he i) (hn i)

/-- A general two-step forced trace. This also supports closed families whose
edges need not be clean, provided the exact two-step calculation is proved. -/
def ForcedTrace (f : Nat → V) : Prop :=
  (∀ i, G.adj (f i) (f (i+1))) ∧
  (∀ i, G.TwoApart (f i) (f (i+2))) ∧
  (∀ i z, G.GeodesicReply (f i) (f (i+2)) z → z = f (i+1))

theorem clean_forcedTrace (f : Nat → V)
    (he : ∀ i, G.adj (f i) (f (i+1)))
    (hc : ∀ i, G.Clean (f (i+1)) (f (i+2)))
    (hn : ∀ i, f i ≠ f (i+2)) : ForcedTrace G f :=
  ⟨he, fun i => G.cleanEdge_twoApart (hc i) (he i) (hn i),
    fun i z => (clean_trace_reply G f he hc hn i z).1⟩

theorem forced_trace_suffix (f : Nat → V) (hf : ForcedTrace G f)
    (count : Nat) (i : Nat) (s : State V)
    (hz : s.zombie = f (i+1)) (hs : s.survivor = f (i+2)) :
    ForcesWithin G (fun _ t => ∀ k, k < count → t.damaged (f (i+2+k)))
      count .survivor s := by
  induction count generalizing i s with
  | zero =>
    apply ForcesWithin.done
    intro k hk
    omega
  | succ count ih =>
    have huv : G.adj s.zombie s.survivor := by
      rw [hz, hs]
      exact hf.1 (i+1)
    have hvw : G.adj s.survivor (f (i+3)) := by
      rw [hs]
      exact hf.1 (i+2)
    have htwo : G.TwoApart s.zombie (f (i+3)) := by
      rw [hz]
      exact hf.2.1 (i+1)
    apply safe_step G s (f (i+3)) huv hvw htwo
    intro z hreply
    have hz' : z = f (i+2) := hf.2.2 (i+1) z (hz ▸ hreply)
    let t := (s.survivorTo (f (i+3))).zombieTo z
    have ht := ih (i+1) t hz' rfl
    have hD : t.damaged (f (i+2)) := Or.inr hs.symm
    have hkeep := ht.preserve_set (fun v => v = f (i+2))
      (fun v hv => hv ▸ hD)
    apply hkeep.mono
    intro _ u hu k hk
    cases k with
    | zero => exact hu.2 _ rfl
    | succ k =>
      have hlt : k < count := by omega
      have hdk := hu.1 k hlt
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hdk

/-- Starting placement and the first zombie move are included. Every listed
source vertex is damaged; the final source is not confused with arrival. -/
theorem forced_trace_prefix (f : Nat → V) (hf : ForcedTrace G f)
    (count : Nat) :
    ForcesWithin G (fun _ t => ∀ k, k < count → t.damaged (f (2+k)))
      count .zombie (initial (f 0) (f 2)) := by
  have ht := hf.2.1 0
  apply ForcesWithin.zombie count _ ht.1 (twoApart_zombie_turn G ht).1
    (twoApart_zombie_turn G ht).2
  intro z hz
  have hz' := hf.2.2 0 z hz
  exact forced_trace_suffix G f hf count 0 _ hz' rfl

/-- If forced traces of bounded covering length exist from every zombie
start, they prove full damage in the original game. No such trace is assumed
without an explicit covering witness. -/
theorem fullDamage_of_forced_traces (count : Nat)
    (htrace : ∀ z, ∃ f : Nat → V, f 0 = z ∧ ForcedTrace G f ∧
      ∀ v, ∃ k, k < count ∧ f (2+k) = v) : FullDamageWithin G count := by
  intro z
  obtain ⟨f, hz, hf, hcover⟩ := htrace z
  refine ⟨f 2, ?_, ?_⟩
  · exact hz ▸ (hf.2.1 0).1
  · have h := forced_trace_prefix G f hf count
    rw [hz] at h
    apply h.mono
    intro _ t ht v
    obtain ⟨k, hk, hv⟩ := hcover v
    exact hv ▸ ht k hk

end ZombieDamage.FullGame
