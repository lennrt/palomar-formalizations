import ZombieDamage.ExecutableGame

/-! Transparent semantic bridge for the actual executable input format.
`Good` is checked by ordinary kernel reduction on the retained fixtures.
The native optimal-value evaluations remain labelled regression checks. -/
namespace ZombieDamage.ExecutableGame.Input
open FullGame

def Good (g : Input) : Prop :=
  0 < g.order ∧ g.adjacent.size = g.order * g.order ∧
  g.distances.size = g.order * g.order ∧
  (∀ u v : Fin g.order, g.edge u.val v.val = g.edge v.val u.val) ∧
  (∀ u : Fin g.order, g.edge u.val u.val = false) ∧
  (∀ u : Fin g.order, g.dist u.val u.val = 0) ∧
  (∀ u v : Fin g.order, g.dist u.val v.val = 0 → u = v) ∧
  (∀ u x v : Fin g.order, g.edge u.val x.val = true →
    g.dist u.val v.val ≤ g.dist x.val v.val + 1) ∧
  (∀ u v : Fin g.order, 0 < g.dist u.val v.val →
    ∃ x : Fin g.order, g.edge u.val x.val = true ∧
      g.dist u.val v.val = g.dist x.val v.val + 1)

instance (g : Input) : Decidable g.Good := by unfold Good; infer_instance

def graph (g : Input) (h : g.Good) : Graph (Fin g.order) where
  adj u v := g.edge u.val v.val = true
  symm := by
    intro u v huv
    rw [← h.2.2.2.1 u v]
    exact huv
  loopless := by
    intro v hv
    rw [h.2.2.2.2.1 v] at hv
    contradiction

def metric (g : Input) (h : g.Good) : (g.graph h).MetricCertificate where
  value u v := g.dist u.val v.val
  zero_self := h.2.2.2.2.2.1
  zero_eq := h.2.2.2.2.2.2.1
  edge_bound := h.2.2.2.2.2.2.2.1
  descent := h.2.2.2.2.2.2.2.2

theorem reply_semantics (g : Input) (h : g.Good) (z s x : Fin g.order) :
    g.reply false z.val s.val x.val = true ↔
    (g.graph h).GeodesicReply z s x := by
  rw [(g.metric h).geodesicReply_iff]
  simp [reply, graph, metric]

theorem survivor_semantics (g : Input) (h : g.Good)
    (z s w : Fin g.order) (D : Fin g.order → Prop) :
    g.survivor z.val s.val w.val = true ↔
    LegalSurvivor (g.graph h) ⟨z,s,D⟩ w := by
  simp [survivor, LegalSurvivor, graph, Fin.val_inj]

end ZombieDamage.ExecutableGame.Input
