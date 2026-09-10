import ZombieMain.InfiniteRounds

namespace ZombieMain.RouteMemory
open ZombieDamage ZombieDamage.FullGame
variable {V : Type} {G : SimpleGraph V} {f : Nat → V} {B : Nat}

/-- An infinite play of the fixed survivor controller, with an arbitrary
legal zombie reply at every round. -/
def Runs (route : RoutingAvailable G B) (m : Nat → RouteMemory G f B) : Prop :=
  ∀t,Next route (m t) (m (t+1))

theorem run_exists (route : RoutingAvailable G B) (start : RouteMemory G f B) :
    ∃m : Nat → RouteMemory G f B,m 0=start ∧ Runs route m := by
  classical
  let next : RouteMemory G f B → RouteMemory G f B := fun m => Classical.choose (next_exists route m)
  let m : Nat → RouteMemory G f B := fun n => Nat.rec start (fun _ s => next s) n
  refine ⟨m,rfl,?_⟩
  intro t
  exact Classical.choose_spec (next_exists route (m t))

def score (m : RouteMemory G f B) : Nat := (B+1)*m.stage+(B-m.budget)

theorem next_score (route : RoutingAvailable G B) {m n : RouteMemory G f B}
    (h : Next route m n) : m.score<n.score := by
  have hf := (next_facts route h).2.1
  have hb := m.bounded
  rcases hf with ⟨hs,hb'⟩ | ⟨hs,hb',_⟩
  · dsimp [score]
    rw [hs]
    omega
  · dsimp [score]
    rw [hs,hb']
    simp only [Nat.mul_add,Nat.mul_one,Nat.sub_self,Nat.add_zero]
    omega

theorem score_bound (m : RouteMemory G f B) : m.score≤(B+1)*(m.stage+1) := by
  simp only [score,Nat.mul_add,Nat.mul_one]
  omega

theorem stage_mono (route : RoutingAvailable G B) {m : Nat → RouteMemory G f B}
    (h : Runs route m) : Monotone (fun t => (m t).stage) := by
  apply monotone_nat_of_le_succ
  intro t
  have hf := (next_facts route (h t)).2.1
  rcases hf with ⟨hs,_⟩ | ⟨hs,_⟩ <;> omega

theorem stage_unbounded (route : RoutingAvailable G B) {m : Nat → RouteMemory G f B}
    (h : Runs route m) (i : Nat) : ∃ t, i<(m t).stage := by
  have hlo : ∀t,t≤(m t).score := by
    intro t
    induction t with
    | zero => omega
    | succ t ih => have hs := next_score route (h t); omega
  let t := (B+1)*(i+1)+1
  refine ⟨t,?_⟩
  have hl := hlo t
  have hu := score_bound (m t)
  by_contra hn
  have hh : (B+1)*((m t).stage+1)≤(B+1)*(i+1) := Nat.mul_le_mul_left _ (by omega)
  dsimp [t] at hl hu hh
  omega

/-- A counter increasing by zero or one, with no finite upper bound, completes
every future service stage. This excludes a hidden infinite unfinished route. -/
theorem stage_completion_after (route : RoutingAvailable G B)
    {m : Nat → RouteMemory G f B} (h : Runs route m) (S i : Nat) (hi : (m S).stage≤ i) :
    ∃ t, S≤t ∧ (m t).stage=i ∧ (m (t+1)).stage=i+1 := by
  classical
  have hm := stage_mono route h
  have hex : ∃k,i<(m (S+k)).stage := by
    obtain ⟨t,ht⟩ := stage_unbounded route h i
    exact ⟨t,ht.trans_le (hm (by omega : t≤S+t))⟩
  let k := Nat.find hex
  have hk : i<(m (S+k)).stage := Nat.find_spec hex
  have hpos : 0<k := by
    by_contra hn
    have he : k=0 := by omega
    rw [he,Nat.add_zero] at hk
    omega
  have hprev : ¬i<(m (S+(k-1))).stage := Nat.find_min hex (by change k-1<k; omega)
  let t := S+(k-1)
  have ht : t+1=S+k := by dsimp [t]; omega
  have hf := (next_facts route (h t)).2.1
  have hstep : (m (t+1)).stage≤(m t).stage+1 := by
    rcases hf with ⟨hs,_⟩ | ⟨hs,_⟩ <;> omega
  have hcurr : (m t).stage≤ i := by dsimp [t]; omega
  rw [← ht] at hk
  exact ⟨t,by dsimp [t]; omega,by omega,by omega⟩

theorem next_reset (route : RoutingAvailable G B) {m n : RouteMemory G f B}
    (h : Next route m n) (hi : m.stage<n.stage) : ∀x,¬n.state.damaged x := by
  rcases (next_facts route h).2.1 with ⟨hs,_⟩ | ⟨_,_,_,hd⟩
  · omega
  · exact hd

/-- Every cofinally requested vertex is an actual departure source infinitely
often, on every infinite play of the fixed controller. -/
theorem recurrent_departures (route : RoutingAvailable G B)
    (hrequest : ∀ x N, ∃ i,  N≤ i ∧ f i=x)
    {m : Nat → RouteMemory G f B} (h : Runs route m) (x : V) (N : Nat) :
    ∃ t, N≤t ∧ (m t).state.survivor=x := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨t0,ht0,hstage0,hstage1⟩ := stage_completion_after route h N (m N).stage le_rfl
  let S := t0+1
  have hstart : ¬(m S).state.damaged x := next_reset route (h t0) (by omega) x
  have hd : ∀k,¬(m (S+k)).state.damaged x := by
    intro k
    induction k with
    | zero => simpa using hstart
    | succ k ih =>
      intro hD
      have hp := (next_facts route (h (S+k))).2.2 x hD
      rcases hp with hp | hp
      · exact ih hp
      · exact hn (S+k) (by dsimp [S]; omega) hp.symm
  obtain ⟨i,hi,hix⟩ := hrequest x (m S).stage
  obtain ⟨t,ht,hst,hst'⟩ := stage_completion_after route h S i hi
  have hcred : (m t).state.damaged x ∨ x=(m t).state.survivor := by
    have hf := (next_facts route (h t)).2.1
    rcases hf with ⟨hs,_⟩ | ⟨_,_,hc,_⟩
    · omega
    · rwa [hst,hix] at hc
  rcases hcred with hD | he
  · have hxfalse := hd (t-S)
    rw [Nat.add_sub_of_le ht] at hxfalse
    exact hxfalse hD
  · exact hn t (by dsimp [S] at ht; omega) he.symm

end ZombieMain.RouteMemory
