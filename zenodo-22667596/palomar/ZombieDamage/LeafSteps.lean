import ZombieDamage.ShortGraph
import ZombieDamage.FullGame

namespace ZombieDamage.Graph
variable {V : Type} (G : Graph V)

theorem leaf_clean {a b : V} (hab : G.adj a b)
    (ha : ∀ x, G.adj a x → x=b) : G.Clean a b := by
  refine ⟨hab,?_,?_⟩
  · intro c hc
    have he := ha c (G.symm hc.2)
    exact G.loopless b (he ▸ hc.1)
  · intro c d _ hbd hc
    exact hbd (ha d (G.symm hc.2.2)).symm

end ZombieDamage.Graph
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

/-- A clean entering edge forces the next post-zombie state, recording the
actual source departure. This is independent of a component classification. -/
theorem clean_entry_step {P : Phase → State V → Prop} {b : Nat}
    (s : State V) (w : V) (hc : G.Clean s.zombie s.survivor)
    (hw : G.adj s.survivor w) (hne : s.zombie≠w)
    (hnext : ForcesWithin G P b .survivor ((s.survivorTo w).zombieTo s.survivor)) :
    ForcesWithin G P (b+1) .survivor s := by
  apply safe_step G s w hc.1 hw (G.clean_first_twoApart hc hw hne)
  intro z hz
  have he := G.clean_first_reply hc hw hne hz
  exact he ▸ hnext

/-- Exiting to a leaf forces the zombie to the departure port and credits
that port, so a completed local exit already has the next entry phase. -/
theorem leaf_exit_step (s : State V) (w : V) (huv : G.adj s.zombie s.survivor)
    (hvw : G.adj s.survivor w) (hw : ∀ x, G.adj w x → x=s.survivor)
    (hne : s.zombie≠w) :
    ForcesWithin G (fun p t => p=.survivor ∧ t.zombie=s.survivor ∧
      t.survivor=w ∧ t.damaged s.survivor) 1 .survivor s := by
  have hc := G.clean_symm (G.leaf_clean (G.symm hvw) hw)
  apply safe_step G s w huv hvw (G.cleanEdge_twoApart hc huv hne)
  intro z hz
  have he := (G.cleanEdge_forces_reply hc huv hne).1 hz
  exact .done 0 .survivor _ ⟨rfl,he,rfl,Or.inr rfl⟩

end ZombieDamage.FullGame
