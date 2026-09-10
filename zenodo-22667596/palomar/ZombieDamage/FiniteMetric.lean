import ZombieDamage.FullGame

/-!
A finitely checkable distance-table certificate. Its local conditions imply
actual shortest-walk distances, so an executable reply test cannot silently
substitute a different metric for the game definition.
-/
namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

structure MetricCertificate where
  value : V → V → Nat
  zero_self : ∀ u, value u u = 0
  zero_eq : ∀ u v, value u v = 0 → u = v
  edge_bound : ∀ u x v, G.adj u x → value u v ≤ value x v + 1
  descent : ∀ u v, 0 < value u v →
    ∃ x, G.adj u x ∧ value u v = value x v + 1

namespace MetricCertificate
variable {G} (M : G.MetricCertificate)

theorem walk_bound {k : Nat} {u v : V} (h : G.Walk k u v) :
    M.value u v ≤ k := by
  induction h with
  | nil u => simp [M.zero_self]
  | @cons k u x v hux _ ih =>
    exact Nat.le_trans (M.edge_bound u x v hux) (Nat.succ_le_succ ih)

theorem realizes : ∀ k u v, M.value u v = k → G.Walk k u v := by
  intro k
  induction k with
  | zero =>
    intro u v h
    have he := M.zero_eq u v h
    subst v
    exact Walk.nil u
  | succ k ih =>
    intro u v h
    have hp : 0 < M.value u v := by omega
    obtain ⟨x, hux, hx⟩ := M.descent u v hp
    have hk : M.value x v = k := by omega
    exact Walk.cons hux (ih x v hk)

theorem distance (u v : V) : G.Distance (M.value u v) u v :=
  ⟨M.realizes _ u v rfl, fun _ h => M.walk_bound h⟩

theorem distance_iff (k : Nat) (u v : V) :
    G.Distance k u v ↔ k = M.value u v := by
  constructor
  · intro h
    exact Nat.le_antisymm (h.2 _ (M.distance u v).1) (M.walk_bound h.1)
  · intro h
    subst k
    exact M.distance u v

/-- The executable distance-decrement rule is exactly the original
shortest-walk geodesic relation, including at distances other than two. -/
theorem geodesicReply_iff (u v x : V) :
    G.GeodesicReply u v x ↔
      G.adj u x ∧ M.value u v = M.value x v + 1 := by
  constructor
  · rintro ⟨hux, d, hud, hxd⟩
    have hu := (M.distance_iff (d + 1) u v).1 hud
    have hx := (M.distance_iff d x v).1 hxd
    exact ⟨hux, by omega⟩
  · rintro ⟨hux, he⟩
    refine ⟨hux, M.value x v, ?_, M.distance x v⟩
    exact (M.distance_iff _ u v).2 he.symm

end MetricCertificate
end ZombieDamage.Graph
