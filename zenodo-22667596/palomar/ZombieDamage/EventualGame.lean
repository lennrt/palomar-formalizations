import ZombieDamage.FullGame

/-!
Unbounded eventual forcing and its equivalence to a uniform survivor-move
bound on a finite graph. Infinite plays that never reach the objective are
losing: `ForcesEventually` is the inductive (least-attractor) interpretation of
forcing eventual damage. Thus the bounded formal model does not assume a
stronger finite-horizon variant when the original graph is finite.
-/
namespace ZombieDamage.FullGame
variable {V : Type} (G : Graph V)

inductive ForcesEventually (goal : Phase → State V → Prop) : Phase → State V → Prop where
  | done (p : Phase) (s : State V) : goal p s → ForcesEventually goal p s
  | zombie (s : State V) : s.zombie ≠ s.survivor →
      (∃ z, LegalZombie G s z) →
      (∀ z, LegalZombie G s z → z ≠ s.survivor) →
      (∀ z, LegalZombie G s z → ForcesEventually goal .survivor (s.zombieTo z)) →
      ForcesEventually goal .zombie s
  | survivor (s : State V) (w : V) : s.zombie ≠ s.survivor →
      LegalSurvivor G s w → ForcesEventually goal .zombie (s.survivorTo w) →
      ForcesEventually goal .survivor s

namespace ForcesWithin
variable {G} {P : Phase → State V → Prop} {b c : Nat} {p : Phase} {s : State V}

theorem mono_budget (h : ForcesWithin G P b p s) (hbc : b≤c) :
    ForcesWithin G P c p s := by
  have hp := h.pad (c-b)
  have he : b+(c-b)=c := by omega
  rw [he] at hp
  exact hp

theorem eventually (h : ForcesWithin G P b p s) : ForcesEventually G P p s := by
  induction h with
  | done b p s hp => exact .done p s hp
  | zombie b s hn he hc _ ih => exact .zombie s hn he hc ih
  | survivor b s w hn hl _ ih => exact .survivor s w hn hl ih
end ForcesWithin

/-- Finite choice of one common bound, with monotone bound predicates. -/
theorem uniform_bound (vs : List V) (P : Nat → V → Prop)
    (mono : ∀ b c, b≤c → ∀ v, P b v → P c v)
    (hex : ∀ v, v ∈ vs → ∃ b, P b v) :
    ∃ b, ∀ v, v ∈ vs → P b v := by
  induction vs with
  | nil => exact ⟨0,by simp⟩
  | cons v vs ih =>
    obtain ⟨b,hb⟩ := hex v (by simp)
    obtain ⟨c,hc⟩ := ih (fun w hw => hex w (by simp [hw]))
    refine ⟨b+c,?_⟩
    intro w hw
    rcases List.mem_cons.mp hw with he | ht
    · subst w
      exact mono b (b+c) (by omega) v hb
    · exact mono c (b+c) (by omega) w (hc w ht)

theorem ForcesEventually.bounded {P : Phase → State V → Prop}
    {p : Phase} {s : State V} (h : ForcesEventually G P p s)
    (vs : List V) (hevery : ∀ v, v ∈ vs) :
    ∃ b, ForcesWithin G P b p s := by
  induction h with
  | done p s hp => exact ⟨0,.done 0 p s hp⟩
  | zombie s hn he hc _ ih =>
    have hb := uniform_bound vs
      (fun b z => LegalZombie G s z → ForcesWithin G P b .survivor (s.zombieTo z))
      (fun b c hbc z hb hz => (hb hz).mono_budget hbc) (fun z _ => by
        classical
        by_cases hz : LegalZombie G s z
        · obtain ⟨b,hb⟩ := ih z hz
          exact ⟨b,fun _ => hb⟩
        · exact ⟨0,fun h => False.elim (hz h)⟩)
    obtain ⟨b,hb⟩ := hb
    exact ⟨b,.zombie b s hn he hc (fun z hz => hb z (hevery z) hz)⟩
  | survivor s w hn hl _ ih =>
    obtain ⟨b,hb⟩ := ih
    exact ⟨b+1,.survivor b s w hn hl hb⟩

def EventualFullDamage : Prop := ∀ z, ∃ v, z≠v ∧
  ForcesEventually G (fun _ => AllDamaged) .zombie (initial z v)

/-- On finite graphs, allowing an unspecified eventual completion horizon
has exactly the same full-damage meaning as existence of a uniform bound. -/
theorem fullDamage_iff_eventual (vs : List V) (hevery : ∀ v, v ∈ vs) :
    FullDamage G ↔ EventualFullDamage G := by
  constructor
  · rintro ⟨b,h⟩ z
    obtain ⟨v,hne,hw⟩ := h z
    exact ⟨v,hne,hw.eventually⟩
  · intro h
    have hb := uniform_bound vs
      (fun b z => ∃ v, z≠v ∧ ForcesWithin G (fun _ => AllDamaged) b .zombie (initial z v))
      (fun b c hbc z hb => by
        obtain ⟨v,hne,hw⟩ := hb
        exact ⟨v,hne,hw.mono_budget hbc⟩) (fun z _ => by
        obtain ⟨v,hne,hw⟩ := h z
        obtain ⟨b,hb⟩ := ForcesEventually.bounded G hw vs hevery
        exact ⟨b,v,hne,hb⟩)
    obtain ⟨b,hb⟩ := hb
    exact ⟨b,fun z => hb z (hevery z)⟩

end ZombieDamage.FullGame
