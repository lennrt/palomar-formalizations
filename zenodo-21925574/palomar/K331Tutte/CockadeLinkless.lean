/-
Paper: Simpler Graph Conditions for Embedding Tetrahedral Meshes
Formalization authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925574
-/

import Mathlib

/-!
# The safe clique-sum mechanism over mathlib simple graphs

Section 5 of the paper: Lemma 5.2 (attachments do not merge old components)
and Proposition 5.3 (the safe clique-sum induction making every suitably
separated MP1-cockade linklessly embeddable).  The Holst-Lovasz-Schrijver
four-clique rule (Corollary 2.5) and the separator bound (Theorem 4.4) enter
as explicit hypotheses; the graphs are actual mathlib `SimpleGraph`s.
-/

namespace K331Tutte.Cockades

open SimpleGraph

variable {V : Type*}

/-- Delete a vertex set: keep only edges with both endpoints outside `S`. -/
def deleteVerts (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ u ∉ S ∧ v ∉ S
  symm := fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩
  loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩

/-- All edges of `G` lie inside the vertex set `s`. -/
def EdgesWithin (G : SimpleGraph V) (s : Set V) : Prop :=
  ∀ ⦃u v : V⦄, G.Adj u v → u ∈ s ∧ v ∈ s

/-- `R` is a four-clique of `G`. -/
def IsFourClique (G : SimpleGraph V) (R : Finset V) : Prop :=
  R.card = 4 ∧ G.IsClique (↑R : Set V)

/-- After deleting `S`, the vertices of `s` fall into at most two connected
components: of any three, some two are joined. -/
def TwoComponentsAfterDeletion (G : SimpleGraph V) (s : Set V) (S : Set V) : Prop :=
  ∀ u ∈ s, ∀ v ∈ s, ∀ w ∈ s, u ∉ S → v ∉ S → w ∉ S →
    ((deleteVerts G S).Reachable u v ∨ (deleteVerts G S).Reachable u w ∨
      (deleteVerts G S).Reachable v w)

/-- A K₄-attachment: the new part `A` (supported on `t`) meets the old part `X`
(supported on `s`) exactly in a four-clique `R` of both. This is the
disjoint-copies-before-identification clique-sum step of Definition 2.3. -/
structure K4Attachment (X A : SimpleGraph V) (s t : Set V) (R : Finset V) : Prop where
  edgesX : EdgesWithin X s
  edgesA : EdgesWithin A t
  inter : s ∩ t = (↑R : Set V)
  cliqueX : IsFourClique X R
  cliqueA : IsFourClique A R

/-- MP₁-cockades over an abstract atom family: recursively generated from atoms
by K₄-attachments (Definition 2.3 / Jørgensen). -/
inductive IsCockade (Atom : SimpleGraph V → Set V → Prop) :
    SimpleGraph V → Set V → Prop
  | atom {A : SimpleGraph V} {s : Set V} : Atom A s → IsCockade Atom A s
  | glue {X A : SimpleGraph V} {s t : Set V} {R : Finset V} :
      IsCockade Atom X s → Atom A t → K4Attachment X A s t R →
      IsCockade Atom (X ⊔ A) (s ∪ t)

/-- Adjacency in the vertex-deleted graph, unfolded. -/
theorem deleteVerts_adj {G : SimpleGraph V} {S : Set V} {u v : V} :
    (deleteVerts G S).Adj u v ↔ G.Adj u v ∧ u ∉ S ∧ v ∉ S := Iff.rfl

/-- Two distinct members of a four-clique are adjacent. -/
theorem IsFourClique.adj {G : SimpleGraph V} {R : Finset V}
    (h : IsFourClique G R) {x y : V} (hx : x ∈ (↑R : Set V))
    (hy : y ∈ (↑R : Set V)) (hxy : x ≠ y) : G.Adj x y :=
  h.2 hx hy hxy

/-- Lemma 5.2 (attachments do not merge old components): a K₄-attachment
cannot create new connections between vertices of the old support, even after
an arbitrary vertex set has been deleted.  Any walk in the glued graph between
deleted-graph survivors of `s` can be rerouted through `X` alone, replacing
each excursion through `A` by an edge of the shared clique `R`. -/
theorem attachment_reachable_transfer_source
    (X A : SimpleGraph V) (s t : Set V) (R : Finset V)
    (h : K4Attachment X A s t R) (S : Set V) {u v : V}
    (hu : u ∈ s) (hv : v ∈ s) (hus : u ∉ S) (hvs : v ∉ S)
    (hreach : (deleteVerts (X ⊔ A) S).Reachable u v) :
    (deleteVerts X S).Reachable u v := by
  have aux : ∀ a b : V, (deleteVerts (X ⊔ A) S).Walk a b → b ∈ s → b ∉ S →
      ((a ∈ s → a ∉ S → (deleteVerts X S).Reachable a b) ∧
        (a ∈ t → a ∉ s →
          ∃ r, r ∈ (↑R : Set V) ∧ r ∉ S ∧ (deleteVerts X S).Reachable r b)) := by
    intro a b w
    induction w with
    | nil =>
      intro hb _
      exact ⟨fun _ _ => Reachable.refl _, fun _ hns => absurd hb hns⟩
    | @cons a c b hac p ih =>
      intro hb hbs
      obtain ⟨hsup, haS, hcS⟩ := deleteVerts_adj.mp hac
      have ihc := ih hb hbs
      constructor
      · -- (i) the walk starts in `s` outside `S`
        intro has haS'
        rcases (sup_adj X A a c).mp hsup with hXe | hAe
        · -- an X-edge stays inside `s` and survives the deletion
          have hcs : c ∈ s := (h.edgesX hXe).2
          exact (deleteVerts_adj.mpr ⟨hXe, haS, hcS⟩).reachable.trans (ihc.1 hcs hcS)
        · -- an A-edge leaving `s` must start in the shared clique `R`
          have hat : a ∈ t := (h.edgesA hAe).1
          have hct : c ∈ t := (h.edgesA hAe).2
          have haR : a ∈ (↑R : Set V) := by
            rw [← h.inter]; exact ⟨has, hat⟩
          by_cases hcs : c ∈ s
          · -- the edge stays over `R`, so it is also an X-edge
            have hcR : c ∈ (↑R : Set V) := by
              rw [← h.inter]; exact ⟨hcs, hct⟩
            have hXac : X.Adj a c := h.cliqueX.adj haR hcR hsup.ne
            exact (deleteVerts_adj.mpr ⟨hXac, haS, hcS⟩).reachable.trans (ihc.1 hcs hcS)
          · -- the tail dives into `A`; it must resurface through `R`
            obtain ⟨r, hrR, hrS, hrb⟩ := ihc.2 hct hcs
            rcases eq_or_ne a r with rfl | har
            · exact hrb
            · have hXar : X.Adj a r := h.cliqueX.adj haR hrR har
              exact (deleteVerts_adj.mpr ⟨hXar, haS, hrS⟩).reachable.trans hrb
      · -- (ii) the walk starts strictly inside the new part
        intro hat hans
        have hAe : A.Adj a c := by
          rcases (sup_adj X A a c).mp hsup with hXe | hAe
          · exact absurd (h.edgesX hXe).1 hans
          · exact hAe
        have hct : c ∈ t := (h.edgesA hAe).2
        by_cases hcs : c ∈ s
        · -- first return to `s` happens on the clique `R`
          have hcR : c ∈ (↑R : Set V) := by
            rw [← h.inter]; exact ⟨hcs, hct⟩
          exact ⟨c, hcR, hcS, ihc.1 hcs hcS⟩
        · exact ihc.2 hct hcs
  obtain ⟨w⟩ := hreach
  exact (aux u v w hv hvs).1 hu hus

/-- The strengthened induction behind Proposition 5.3: a cockade whose final
graph satisfies the separator property is `nIL`, and its support carries at
least five vertices (inherited from any atom). The separator property is kept
in the conclusion so that the cockade induction can vary it. -/
theorem cockade_strong_induction
    (Atom : SimpleGraph V → Set V → Prop) (nIL : SimpleGraph V → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph V) (s : Set V), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph V) (s : Set V), Atom A s →
      ∃ T : Finset V, (↑T : Set V) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph V) (s t : Set V) (R : Finset V),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set V) → nIL (X ⊔ A))
    {G : SimpleGraph V} {s : Set V} (hG : IsCockade Atom G s) :
    (∀ R : Finset V, IsFourClique G R → (∃ x ∈ s, x ∉ (↑R : Set V)) →
      TwoComponentsAfterDeletion G s (↑R : Set V)) →
    nIL G ∧ ∃ T : Finset V, (↑T : Set V) ⊆ s ∧ 5 ≤ T.card := by
  induction hG with
  | @atom A₀ s₀ hA₀ =>
    intro _
    exact ⟨hatom_nIL A₀ s₀ hA₀, hatom_big A₀ s₀ hA₀⟩
  | @glue X A s t R hX hA hK ih =>
    intro hsep
    -- (a) the separator property descends from `(X ⊔ A, s ∪ t)` to `(X, s)`
    have hsepX : ∀ R' : Finset V, IsFourClique X R' →
        (∃ x ∈ s, x ∉ (↑R' : Set V)) →
        TwoComponentsAfterDeletion X s (↑R' : Set V) := by
      intro R' hR' hx
      have hR'sup : IsFourClique (X ⊔ A) R' :=
        ⟨hR'.1, IsClique.mono le_sup_left hR'.2⟩
      obtain ⟨x, hxs, hxR⟩ := hx
      have houter := hsep R' hR'sup ⟨x, Set.mem_union_left t hxs, hxR⟩
      intro p₁ hp₁ p₂ hp₂ p₃ hp₃ hS₁ hS₂ hS₃
      rcases houter p₁ (Set.mem_union_left t hp₁) p₂ (Set.mem_union_left t hp₂)
          p₃ (Set.mem_union_left t hp₃) hS₁ hS₂ hS₃ with h₁ | h₁ | h₁
      · exact Or.inl (attachment_reachable_transfer_source X A s t R hK
          (↑R' : Set V) hp₁ hp₂ hS₁ hS₂ h₁)
      · exact Or.inr (Or.inl (attachment_reachable_transfer_source X A s t R hK
          (↑R' : Set V) hp₁ hp₃ hS₁ hS₃ h₁))
      · exact Or.inr (Or.inr (attachment_reachable_transfer_source X A s t R hK
          (↑R' : Set V) hp₂ hp₃ hS₂ hS₃ h₁))
    -- (b) inductive hypothesis for the old part
    obtain ⟨hnX, T, hTs, hT5⟩ := ih hsepX
    -- (c) the new atom is nIL
    have hnA : nIL A := hatom_nIL A t hA
    -- (d) the gluing clique separates the glued graph into at most two pieces
    have hRsup : IsFourClique (X ⊔ A) R :=
      ⟨hK.cliqueX.1, IsClique.mono le_sup_left hK.cliqueX.2⟩
    have hex : ∃ x ∈ s ∪ t, x ∉ (↑R : Set V) := by
      by_contra hcon
      have hTR : T ⊆ R := by
        intro x hxT
        by_contra hxR
        exact hcon ⟨x, Set.mem_union_left t (hTs (Finset.mem_coe.mpr hxT)),
          fun hmem => hxR (Finset.mem_coe.mp hmem)⟩
      have hcard : T.card ≤ R.card := Finset.card_le_card hTR
      have h₄ : R.card = 4 := hK.cliqueX.1
      omega
    have h2c := hsep R hRsup hex
    -- (e) the Holst-Lovasz-Schrijver four-clique rule closes the induction
    refine ⟨hHLS X A s t R hK hnX hnA h2c, T, ?_, hT5⟩
    exact fun x hx => Set.mem_union_left t (hTs hx)

/-- Proposition 5.3 (the safe clique-sum induction): every MP₁-cockade whose
four-cliques all leave at most two components on the support is `nIL`, given
that the atoms are `nIL` and the Holst-Lovasz-Schrijver four-clique rule
(`hHLS`, paper Corollary 2.5) is available; `hsep` is the separator bound
(paper Theorem 4.4) for the final graph. -/
theorem safe_cockade_linkless_source
    (Atom : SimpleGraph V → Set V → Prop) (nIL : SimpleGraph V → Prop)
    (hatom_nIL : ∀ (A : SimpleGraph V) (s : Set V), Atom A s → nIL A)
    (hatom_big : ∀ (A : SimpleGraph V) (s : Set V), Atom A s →
      ∃ T : Finset V, (↑T : Set V) ⊆ s ∧ 5 ≤ T.card)
    (hHLS : ∀ (X A : SimpleGraph V) (s t : Set V) (R : Finset V),
      K4Attachment X A s t R → nIL X → nIL A →
      TwoComponentsAfterDeletion (X ⊔ A) (s ∪ t) (↑R : Set V) → nIL (X ⊔ A))
    {G : SimpleGraph V} {s : Set V} (hG : IsCockade Atom G s)
    (hsep : ∀ R : Finset V, IsFourClique G R → (∃ x ∈ s, x ∉ (↑R : Set V)) →
      TwoComponentsAfterDeletion G s (↑R : Set V)) :
    nIL G :=
  (cockade_strong_induction Atom nIL hatom_nIL hatom_big hHLS hG hsep).1

#print axioms attachment_reachable_transfer_source
#print axioms safe_cockade_linkless_source

end K331Tutte.Cockades
