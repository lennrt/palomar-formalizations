import ZombieMain.Families

namespace ZombieMain

abbrev AttachmentOutcome := Option (Family × Diagram.Certificate)

def AttachmentOutcome.Valid (o : AttachmentOutcome) (D : Diagram) : Prop :=
  match o with
  | none => D.portCount = 1
  | some (f, c) => f.Admissible ∧ c.Valid D f.diagram

instance (o : AttachmentOutcome) (D : Diagram) : Decidable (o.Valid D) := by
  cases o with
  | none => unfold AttachmentOutcome.Valid; infer_instance
  | some p => cases p; unfold AttachmentOutcome.Valid; infer_instance

theorem AttachmentOutcome.sound {o : AttachmentOutcome} {D : Diagram}
    (h : o.Valid D) : D.Classified := by
  cases o with
  | none => exact Or.inl h
  | some p => exact Or.inr ⟨p.1, h.1, ⟨Diagram.Certificate.toIso h.2⟩⟩

structure AEntry where
  source : Family
  p : Nat
  q : Nat
  r : Nat
  outcome : AttachmentOutcome

def AEntry.diagram (e : AEntry) := e.source.diagram.adjoinPath e.p e.q e.r
def AEntry.matches (e : AEntry) (f : Family) (p q r : Nat) : Bool :=
  decide (e.source = f ∧ e.p = p ∧ e.q = q ∧ e.r = r)

def ACoverage (entries : List AEntry) (f : Family) : Prop :=
  ∀ p q : Fin f.diagram.order, ∀ r : Fin 3,
    f.diagram.LegalPath p.val q.val (r.val+1) →
    entries.any (fun e => e.matches f p.val q.val (r.val+1)) = true

instance (entries : List AEntry) (f : Family) : Decidable (ACoverage entries f) := by
  unfold ACoverage
  infer_instance

theorem ACoverage.sound {entries : List AEntry} {f : Family}
    (hv : entries.all (fun e => decide (e.outcome.Valid e.diagram)) = true)
    (hc : ACoverage entries f) {p q r : Nat}
    (h : f.diagram.LegalPath p q r) : (f.diagram.adjoinPath p q r).Classified := by
  have hcopy := h
  rcases hcopy with ⟨hp, hq, _, _, _, hr1, hr3, _, _⟩
  have hr : r-1+1 = r := by omega
  have covered := hc ⟨p, hp⟩ ⟨q, hq⟩ ⟨r-1, by omega⟩ (by simpa [hr] using h)
  simp only [hr] at covered
  obtain ⟨e, he, hm⟩ := List.any_eq_true.mp covered
  have hevalid := of_decide_eq_true (List.all_eq_true.mp hv e he)
  have hs := AttachmentOutcome.sound hevalid
  obtain ⟨hf, hp', hq', hr'⟩ := of_decide_eq_true hm
  simpa [AEntry.diagram, hf, hp', hq', hr'] using hs

structure BEntry where
  source : Family
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  outcome : AttachmentOutcome

def BEntry.diagram (e : BEntry) := e.source.diagram.adjoinMatching e.a e.b e.c e.d
def BEntry.matches (e : BEntry) (f : Family) (a b c d : Nat) : Bool :=
  decide (e.source = f ∧ e.a = a ∧ e.b = b ∧ e.c = c ∧ e.d = d)

def BCoverage (entries : List BEntry) (f : Family) : Prop :=
  ∀ a b c d : Fin f.diagram.order,
    f.diagram.LegalMatching a.val b.val c.val d.val →
    entries.any (fun e => e.matches f a.val b.val c.val d.val) = true

instance (entries : List BEntry) (f : Family) : Decidable (BCoverage entries f) := by
  unfold BCoverage
  infer_instance

theorem BCoverage.sound {entries : List BEntry} {f : Family}
    (hv : entries.all (fun e => decide (e.outcome.Valid e.diagram)) = true)
    (hc : BCoverage entries f) {a b c d : Nat}
    (h : f.diagram.LegalMatching a b c d) : (f.diagram.adjoinMatching a b c d).Classified := by
  have covered := hc ⟨a, h.1⟩ ⟨b, h.2.1⟩ ⟨c, h.2.2.1⟩ ⟨d, h.2.2.2.1⟩ h
  obtain ⟨e, he, hm⟩ := List.any_eq_true.mp covered
  have hevalid := of_decide_eq_true (List.all_eq_true.mp hv e he)
  have hs := AttachmentOutcome.sound hevalid
  obtain ⟨hf, ha, hb, hc', hd⟩ := of_decide_eq_true hm
  simpa [BEntry.diagram, hf, ha, hb, hc', hd] using hs

end ZombieMain
