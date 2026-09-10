import ZombieDamage.FullGame

/-! Relabelling invariance of the FULL game, including arbitrary geodesic
replies, starting positions, damage sets, and survivor-move budgets. -/
namespace ZombieDamage

structure GraphIso {V W : Type} (G : Graph V) (H : Graph W) where
  toFun : V → W
  invFun : W → V
  left_inv : ∀ v, invFun (toFun v)=v
  right_inv : ∀ w, toFun (invFun w)=w
  adjacency : ∀ u v, G.adj u v ↔ H.adj (toFun u) (toFun v)

namespace GraphIso
variable {V W : Type} {G : Graph V} {H : Graph W} (F : GraphIso G H)

def symm : GraphIso H G where
  toFun := F.invFun
  invFun := F.toFun
  left_inv := F.right_inv
  right_inv := F.left_inv
  adjacency := by
    intro u v
    have h := F.adjacency (F.invFun u) (F.invFun v)
    simpa [F.right_inv] using h.symm

theorem injective {u v : V} (h : F.toFun u=F.toFun v) : u=v := by
  have hi := congrArg F.invFun h
  simpa [F.left_inv] using hi

theorem walk {k : Nat} {u v : V} (h : G.Walk k u v) :
    H.Walk k (F.toFun u) (F.toFun v) := by
  induction h with
  | nil u => exact .nil _
  | cons huv _ ih => exact .cons ((F.adjacency _ _).1 huv) ih

theorem distance {k : Nat} {u v : V} (h : G.Distance k u v) :
    H.Distance k (F.toFun u) (F.toFun v) := by
  refine ⟨F.walk h.1,?_⟩
  intro j hj
  have hw := F.symm.walk hj
  simp only [symm,F.left_inv] at hw
  exact h.2 j hw

theorem reply {u v x : V} (h : G.GeodesicReply u v x) :
    H.GeodesicReply (F.toFun u) (F.toFun v) (F.toFun x) := by
  obtain ⟨hux,d,hud,hxd⟩ := h
  exact ⟨(F.adjacency _ _).1 hux,d,F.distance hud,F.distance hxd⟩

def state (s : FullGame.State V) : FullGame.State W :=
  ⟨F.toFun s.zombie,F.toFun s.survivor,fun w => s.damaged (F.invFun w)⟩

theorem inv_eq_iff (w : W) (v : V) : F.invFun w=v ↔ w=F.toFun v := by
  constructor
  · intro h
    have hh := congrArg F.toFun h
    simpa [F.right_inv] using hh
  · intro h
    rw [h,F.left_inv]

theorem survivorTo (s : FullGame.State V) (v : V) :
    F.state (s.survivorTo v) = (F.state s).survivorTo (F.toFun v) := by
  unfold state FullGame.State.survivorTo
  congr 1
  funext w
  apply propext
  change (s.damaged (F.invFun w) ∨ F.invFun w=s.survivor) ↔
    (s.damaged (F.invFun w) ∨ w=F.toFun s.survivor)
  rw [F.inv_eq_iff]

theorem forcesWithin {P : FullGame.Phase → FullGame.State V → Prop}
    {Q : FullGame.Phase → FullGame.State W → Prop}
    {b : Nat} {p : FullGame.Phase} {s : FullGame.State V}
    (h : FullGame.ForcesWithin G P b p s)
    (hPQ : ∀ p s, P p s → Q p (F.state s)) :
    FullGame.ForcesWithin H Q b p (F.state s) := by
  induction h with
  | done b p s hp => exact .done b p (F.state s) (hPQ p s hp)
  | zombie b s hne hex hcap hnext ih =>
    apply FullGame.ForcesWithin.zombie b (F.state s)
    · intro he
      exact hne (F.injective he)
    · obtain ⟨x,hx⟩ := hex
      exact ⟨F.toFun x,F.reply hx⟩
    · intro y hy he
      have hpre := F.symm.reply hy
      simp only [state,symm,F.left_inv] at hpre
      apply hcap (F.invFun y) hpre
      have hh := congrArg F.invFun he
      simpa [state,F.left_inv] using hh
    · intro y hy
      have hpre := F.symm.reply hy
      simp only [state,symm,F.left_inv] at hpre
      have hn := ih (F.invFun y) hpre
      simpa [state,FullGame.State.zombieTo,F.right_inv] using hn
  | survivor b s w hne hlegal hnext ih =>
    apply FullGame.ForcesWithin.survivor b (F.state s) (F.toFun w)
    · intro he
      exact hne (F.injective he)
    · constructor
      · intro he
        exact hlegal.1 (F.injective he)
      · rcases hlegal.2 with he | he
        · exact Or.inl (congrArg F.toFun he)
        · exact Or.inr ((F.adjacency _ _).1 he)
    · rw [← F.survivorTo]
      exact ih

include F in
theorem fullDamageWithin {b : Nat} (h : FullGame.FullDamageWithin G b) :
    FullGame.FullDamageWithin H b := by
  intro z
  obtain ⟨v,hne,hwin⟩ := h (F.invFun z)
  refine ⟨F.toFun v,?_,?_⟩
  · intro he
    have hh := congrArg F.invFun he
    exact hne (by simpa [F.left_inv] using hh)
  · have hm := F.forcesWithin hwin (Q := fun _ => FullGame.AllDamaged)
      (fun _ s hs w => hs (F.invFun w))
    simpa [state,FullGame.initial,F.right_inv] using hm

include F in
theorem fullDamage_iff : FullGame.FullDamage G ↔ FullGame.FullDamage H := by
  constructor
  · rintro ⟨b,h⟩
    exact ⟨b,F.fullDamageWithin h⟩
  · rintro ⟨b,h⟩
    exact ⟨b,F.symm.fullDamageWithin h⟩

end GraphIso
end ZombieDamage
