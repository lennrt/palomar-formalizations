import ZombieDamage.Graph

/-!
Shortest-walk distance histograms for finite populations (lists modulo
permutation). This source supports the fixed-sensor involution lemma in the
paper. Execution evidence is recorded separately in VERIFICATION.md.
The graph metric is the actual minimum walk length, not an abstract oracle.
-/

-- BEGIN OBSERVATION DEFINITIONS
namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

/-- Multiplicity of radius r in the distance histogram of a finite population.
Order is ignored and repeated vertices are retained. -/
noncomputable def shellCount (r : Nat) (s : V) (population : List V) : Nat := by
  classical
  exact (population.filter (fun v => decide (G.Distance r s v))).length

/-- Sensor identities are retained; target labels and cross-sensor matching
are not. Equality is required at every nonnegative integral radius. -/
def SameShellData (S : V → Prop) (xs ys : List V) : Prop :=
  ∀ s, S s → ∀ r, G.shellCount r s xs = G.shellCount r s ys

/-- Recovery of all populations of mass at most h, including multiplicities
and the empty population. Equality of populations is list permutation. -/
def Recovers (S : V → Prop) (h : Nat) : Prop :=
  ∀ xs ys : List V, xs.length ≤ h → ys.length ≤ h →
    G.SameShellData S xs ys → xs.Perm ys

end ZombieDamage.Graph
-- END OBSERVATION DEFINITIONS

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

theorem walk_map (f : V → V)
    (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    {r : Nat} {u v : V} (h : G.Walk r u v) :
    G.Walk r (f u) (f v) := by
  induction h with
  | nil v => exact Walk.nil (f v)
  | cons huv _ ih => exact Walk.cons (hmap _ _ huv) ih

theorem distance_map_involution (f : V → V)
    (hinv : ∀ v, f (f v) = v)
    (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    {r : Nat} {u v : V} (h : G.Distance r u v) :
    G.Distance r (f u) (f v) := by
  constructor
  · exact G.walk_map f hmap h.1
  · intro j hj
    have back : G.Walk j u v := by
      simpa only [hinv] using G.walk_map f hmap hj
    exact h.2 j back

/-- The graph-walk bridge: a fixed sensor cannot distinguish vertices swapped
by an adjacency-preserving involution, at any shortest-path radius. -/
theorem fixed_sensor_distance (f : V → V)
    (hinv : ∀ v, f (f v) = v)
    (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    {s a b : V} (hs : f s = s) (hab : f a = b) (r : Nat) :
    G.Distance r s a ↔ G.Distance r s b := by
  have hba : f b = a := by rw [← hab, hinv]
  constructor
  · intro h
    simpa only [hs, hab] using G.distance_map_involution f hinv hmap h
  · intro h
    simpa only [hs, hba] using G.distance_map_involution f hinv hmap h

/-- Paper: fixed-sensor involution obstruction. This proves an actual
histogram collision and failure of bounded population recovery, not merely
an equality of vertex names or a certificate-validity condition. -/
theorem involution_blocks_recovery (f : V → V)
    (hinv : ∀ v, f (f v) = v)
    (hmap : ∀ u v, G.adj u v → G.adj (f u) (f v))
    (S : V → Prop) (hfix : ∀ s, S s → f s = s)
    (a b : V) (hne : a ≠ b) (hab : f a = b)
    (h : Nat) (hh : 1 ≤ h) : ¬ G.Recovers S h := by
  classical
  intro hrec
  have data : G.SameShellData S [a] [b] := by
    intro s hs r
    have hd := G.fixed_sensor_distance f hinv hmap (hfix s hs) hab r
    by_cases ha : G.Distance r s a
    · have hb : G.Distance r s b := hd.mp ha
      simp [shellCount, ha, hb]
    · have hb : ¬ G.Distance r s b := fun hb => ha (hd.mpr hb)
      simp [shellCount, ha, hb]
  have hp : ([a] : List V).Perm [b] :=
    hrec [a] [b] (by simpa using hh) (by simpa using hh) data
  have hb : a ∈ ([b] : List V) := hp.mem_iff.mp (by simp)
  exact hne (by simpa using hb)

end ZombieDamage.Graph
