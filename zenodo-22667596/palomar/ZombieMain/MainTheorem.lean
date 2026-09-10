import ZombieMain.CleanFullDamage
import ZombieMain.ClosedLabels
import ZombieMain.ExceptionLabels

/-! Source conjecture: Randy Davila, "The Zombie Damage Number of a Graph",
arXiv:2607.16382v1, Conjecture 24. The zombie damage parameter and game are
Davila's source theory. The complete proof and Lean formalization here are
developed by Lennart Rudolph with the AI assistance disclosed in the paper.
The four-exception characterization and explicit bound strengthen the source
conjecture; they are not attributed to Davila as previously proved results. -/

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Exact closed-family branch, using graph isomorphisms of the literal
classification diagrams and the full-game prism and Möbius strategies. -/
theorem full_damage_without_clean (hconn : G.Connected) (hcubic : ∀v,G.degree v=3)
    (hn : ¬∃p q,(gameGraph G).Clean p q) (hex : ¬IsException G) :
    FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) := by
  classical
  obtain ⟨f,hf,hclosed,⟨e⟩⟩ := no_clean_classification hconn hcubic hn
  cases f with
  | ladder m | singleCap m | doubleCap m | k23 | k33e | p3e | q3v | q3e => cases hclosed
  | k4 =>
    exact False.elim (hex ⟨.k4,⟨e.gameIso (Exceptions.graph .k4) (Equiv.refl _) k4_exception_adj⟩⟩)
  | k33 =>
    exact False.elim (hex ⟨.k33,⟨e.gameIso (Exceptions.graph .k33) (Equiv.refl _) k33_exception_adj⟩⟩)
  | prism m =>
    by_cases hm3 : m=3
    · subst m
      exact False.elim (hex ⟨.prism3,⟨e.gameIso (Exceptions.graph .prism3)
        prism3ExceptionLabels prism3_exception_adj⟩⟩)
    by_cases hm4 : m=4
    · subst m
      exact False.elim (hex ⟨.cube,⟨e.gameIso (Exceptions.graph .cube)
        cubeExceptionLabels cube_exception_adj⟩⟩)
    have hm : 5≤m := by change 3≤m at hf; omega
    let F := e.gameIso (PrismGame.graph hm) (prismLabels m) (prism_labels_adj m hm)
    have h := F.fullDamageWithin (PrismGame.full_damage hm)
    have he : 2*m=Fintype.card V := e.whole_order
    intro z
    obtain ⟨v,hne,hv⟩ := h z
    refine ⟨v,hne,hv.budget_mono ?_⟩
    rw [he]
    nlinarith
  | mobius m =>
    by_cases hm3 : m=3
    · subst m
      exact False.elim (hex ⟨.k33,⟨e.gameIso (Exceptions.graph .k33)
        mobius3ExceptionLabels mobius3_exception_adj⟩⟩)
    have hm : 4≤m := by change 3≤m at hf; omega
    let F := e.gameIso (MobiusGame.graph hm) (mobiusLabels m) (mobius_labels_adj m hm)
    have h := F.fullDamageWithin (MobiusGame.full_damage hm)
    have he : 2*m=Fintype.card V := e.whole_order
    intro z
    obtain ⟨v,hne,hv⟩ := h z
    refine ⟨v,hne,hv.budget_mono ?_⟩
    rw [he]
    nlinarith

/-- Main theorem, with the original graph hypotheses and no assumed
classification, ambient model, local strategy, quotient or initialization. -/
theorem full_damage_within_iff (hconn : G.Connected) (hcubic : ∀v,G.degree v=3)
    (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge s(u,v)) :
    FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) ↔ ¬IsException G := by
  classical
  constructor
  · intro h
    exact full_damage_not_exception ⟨_,h⟩
  · intro h
    by_cases hc : ∃p q,(gameGraph G).Clean p q
    · exact full_damage_of_clean_edge hconn hcubic hbridge hc
    · exact full_damage_without_clean hconn hcubic hc h

/-- A connected bridgeless cubic graph has full zombie damage exactly when
it is not isomorphic to K₄, K₃,₃, the triangular prism, or the cube. -/
theorem full_damage_iff (hconn : G.Connected) (hcubic : ∀v,G.degree v=3)
    (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge s(u,v)) :
    FullDamage (gameGraph G) ↔ ¬IsException G := by
  constructor
  · exact full_damage_not_exception
  · intro h
    exact ⟨_,(full_damage_within_iff hconn hcubic hbridge).mpr h⟩

/-- Davila's Conjecture 24, under the exact finite simple connected
bridgeless cubic hypotheses and order threshold of the original statement. -/
theorem davila_conjecture_24 (hconn : G.Connected) (hcubic : ∀v,G.degree v=3)
    (hbridge : ∀u v,G.Adj u v → ¬G.IsBridge s(u,v)) (hn : 10≤Fintype.card V) :
    FullDamageWithin (gameGraph G) (2*Fintype.card V*(Fintype.card V+1)) :=
  (full_damage_within_iff hconn hcubic hbridge).mpr (order_ten_not_exception hn)

end ZombieMain
