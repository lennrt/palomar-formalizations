import ZombieMain.QuotientRouting
import ZombieMain.GameMetric
import ZombieMain.DamageIrrelevance
import ZombieDamage.FullGameBounds

namespace ZombieMain
open SimpleGraph ZombieDamage ZombieDamage.FullGame
variable {V : Type} {G : SimpleGraph V}

def CleanEntry (G : SimpleGraph V) (phase : Phase) (s : State V) : Prop :=
  phase=.survivor ∧ (gameGraph G).Clean s.zombie s.survivor

/-- Wait at the closer endpoint of a clean edge. Every shortest-path reply
preserves the distance comparison, so the eventual crossing is safe. -/
theorem wait_then_cross (hconn : G.Connected) (p q : V)
    (hpq : (gameGraph G).Clean p q) (d : Nat) (s : State V)
    (hs : s.survivor=p) (hd : G.dist s.zombie p=d) (h2 : 2≤d)
    (hcloser : G.dist s.zombie p≤G.dist s.zombie q) :
    ForcesWithin (gameGraph G) (CleanEntry G) d .zombie s := by
  induction d using Nat.strong_induction_on generalizing s with
  | h d ih =>
    have hne : s.zombie≠s.survivor := by
      intro he
      have hz : G.dist s.zombie p=0 := hconn.dist_eq_zero_iff.mpr (he.trans hs)
      omega
    apply ForcesWithin.zombie d s hne
    · exact exists_game_reply hconn hne
    · intro y hy he
      have hdy := reply_dist_eq hconn hy
      have hy0 : G.dist y s.survivor=0 := hconn.dist_eq_zero_iff.mpr he
      rw [hs] at hdy hy0
      omega
    · intro y hy
      have hdy := reply_dist_eq hconn hy
      rw [hs] at hdy
      have hzy : G.dist s.zombie y=1 := dist_eq_one_iff_adj.mpr hy.1
      have htri : G.dist s.zombie q≤G.dist s.zombie y+G.dist y q := hconn.dist_triangle
      have hcomp : G.dist y p≤G.dist y q := by omega
      have hyp : y≠p := by
        intro he
        have hz : G.dist y p=0 := hconn.dist_eq_zero_iff.mpr he
        omega
      let t := s.zombieTo y
      by_cases hone : G.dist y p=1
      · have hadj : (gameGraph G).adj t.zombie t.survivor := by
          change G.Adj y s.survivor
          rw [hs]
          exact dist_eq_one_iff_adj.mp hone
        have hyq : y≠q := by
          intro he
          have hz : G.dist y q=0 := hconn.dist_eq_zero_iff.mpr he
          omega
        have he : (gameGraph G).Clean t.survivor q := by change (gameGraph G).Clean s.survivor q; rw [hs]; exact hpq
        have hr : ForcesWithin (gameGraph G) (CleanEntry G) 1 .survivor t := by
          apply safe_step (gameGraph G) t q hadj he.1 ((gameGraph G).cleanEdge_twoApart he hadj hyq)
          intro r hr
          have hrp := ((gameGraph G).cleanEdge_forces_reply he hadj hyq).mp hr
          exact .done 0 .survivor _ ⟨rfl,hrp ▸ he⟩
        exact hr.budget_mono (by omega)
      · have hd' : 2≤G.dist y p := by
          have hpos := hconn.pos_dist_of_ne hyp
          omega
        have hr := ih (G.dist y p) (by omega) (t.survivorTo p) rfl rfl hd' hcomp
        have hpass : ForcesWithin (gameGraph G) (CleanEntry G) (G.dist y p+1) .survivor t :=
          .survivor _ t p (by change y≠s.survivor; rw [hs]; exact hyp)
            ⟨Ne.symm hyp,Or.inl hs.symm⟩ hr
        have he : G.dist y p+1=d := by omega
        rwa [he] at hpass

/-- If the zombie starts next to one endpoint, starting at the other gives
an immediate forced clean entry on the zombie's first turn. -/
theorem initial_across_clean {z p q : V} (hpq : (gameGraph G).Clean p q)
    (hzp : G.Adj z p) (hzq : z≠q) :
    ForcesWithin (gameGraph G) (CleanEntry G) 0 .zombie (initial z q) := by
  have ht := (gameGraph G).cleanEdge_twoApart hpq hzp hzq
  have hr := twoApart_zombie_turn (gameGraph G) ht
  apply ForcesWithin.zombie 0 _ hzq hr.1 hr.2
  intro y hy
  have he := ((gameGraph G).cleanEdge_forces_reply hpq hzp hzq).mp hy
  exact .done 0 .survivor _ ⟨rfl,he ▸ hpq⟩

/-- When the zombie itself occupies an endpoint, use the first move of a
checked route to choose the survivor's start, then erase the hypothetical
initial departure from the damage record. -/
theorem initial_at_clean_endpoint [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    {z p : V} (hc : (gameGraph G).Clean z p) :
    ∃ w,z≠w ∧ ForcesWithin (gameGraph G) (CleanEntry G)
      (2*Fintype.card V) .zombie (initial z w) := by
  have hr := target_contract hconn hcubic hbridge (initial z p) hc p
  obtain ⟨k,w,hk,hw,hnext⟩ := first_survivor_move hr (by intro h; exact h.2.2)
  refine ⟨w,Ne.symm hw.1,?_⟩
  have hpos := hnext.mono (Q := CleanEntry G) (fun phase t ht => ⟨ht.1,ht.2.1⟩)
  have herase := ForcesWithin.damage_irrelevant
    (P := fun phase z v => phase=.survivor ∧ (gameGraph G).Clean z v) hpos (fun _ => False)
  exact herase.budget_mono (Nat.le_of_lt hk)

/-- Every original zombie start admits initialization within twice the order
whenever the graph has a clean edge. Passes and the first zombie turn are explicit. -/
theorem clean_initialization [Fintype V] [DecidableRel G.Adj]
    (hconn : G.Connected) (hcubic : ∀ v,G.degree v=3)
    (hbridge : ∀ u v,G.Adj u v → ¬G.IsBridge s(u,v))
    (p q : V) (hpq : (gameGraph G).Clean p q) (z : V) :
    ∃ w,z≠w ∧ ForcesWithin (gameGraph G) (CleanEntry G)
      (2*Fintype.card V) .zombie (initial z w) := by
  by_cases hzp : z=p
  · subst z; exact initial_at_clean_endpoint hconn hcubic hbridge hpq
  by_cases hzq : z=q
  · subst z; exact initial_at_clean_endpoint hconn hcubic hbridge ((gameGraph G).clean_symm hpq)
  by_cases hap : G.Adj z p
  · exact ⟨q,hzq,(initial_across_clean hpq hap hzq).budget_mono (Nat.zero_le _)⟩
  by_cases haq : G.Adj z q
  · exact ⟨p,hzp,(initial_across_clean ((gameGraph G).clean_symm hpq) haq hzp).budget_mono (Nat.zero_le _)⟩
  by_cases hdist : G.dist z p≤G.dist z q
  · refine ⟨p,hzp,?_⟩
    have hr := wait_then_cross hconn p q hpq (G.dist z p) (initial z p) rfl rfl
      (hconn.one_lt_dist_of_ne_of_not_adj hzp hap) hdist
    exact hr.budget_mono (by have h := graph_dist_lt_card hconn z p; omega)
  · refine ⟨q,hzq,?_⟩
    have hr := wait_then_cross hconn q p ((gameGraph G).clean_symm hpq) (G.dist z q)
      (initial z q) rfl rfl (hconn.one_lt_dist_of_ne_of_not_adj hzq haq) (by change G.dist z q≤G.dist z p; omega)
    exact hr.budget_mono (by have h := graph_dist_lt_card hconn z q; omega)

end ZombieMain
