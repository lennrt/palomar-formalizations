import ZombieMain.EmbeddingFacts
import ZombieMain.Families
import ZombieMain.ClassificationDefinitions

namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {H : G.Subgraph} {D : Diagram}

theorem Diagram.Embedding.port_count (e : D.Embedding H) :
    D.portCount = (portVertices H).ncard := by
  classical
  let ports := Finset.univ.filter (fun u : Fin D.order => D.degree u.val = 2)
  have hset : (↑(ports.image e.vertices) : Set V) = portVertices H := by
    ext v
    simp only [Finset.mem_coe, Finset.mem_image]
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨e.mem u, (e.degree u).symm.trans (Finset.mem_filter.mp hu).2⟩
    · rintro ⟨hv,hdeg⟩
      obtain ⟨u,rfl⟩ := e.exists_label hv
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (e.degree u).trans hdeg⟩, rfl⟩
  rw [← hset, Set.ncard_coe_finset, Finset.card_image_of_injective _ e.injective]
  rfl

theorem Diagram.Embedding.classified (e : D.Embedding H) (h : D.Classified) :
    ClassifiedSubgraph H := by
  rcases h with hp | ⟨f,hf,⟨iso⟩⟩
  · exact Or.inl (e.port_count.symm.trans hp)
  · exact Or.inr ⟨f,hf,⟨e.relabel iso.symm⟩⟩

/-- Every finite subgraph has an exact labelled copy; this is also used
for the unspecified one-port terminal class. -/
noncomputable def canonicalDiagram [Fintype V] (H : G.Subgraph) : Diagram := by
  classical
  let labels := Fintype.equivFin H.verts
  exact
    { order := Fintype.card H.verts
      adj u v := if hu : u < Fintype.card H.verts then
        if hv : v < Fintype.card H.verts then
          decide (H.Adj (labels.symm ⟨u,hu⟩).val (labels.symm ⟨v,hv⟩).val)
        else false
      else false }

noncomputable def canonicalEmbedding [Fintype V] (H : G.Subgraph) :
    (canonicalDiagram H).Embedding H := by
  classical
  let labels := Fintype.equivFin H.verts
  refine ⟨fun u => (labels.symm u).val,
    Subtype.val_injective.comp labels.symm.injective, ?_, ?_⟩
  · ext v
    constructor
    · rintro ⟨u,rfl⟩
      exact (labels.symm u).property
    · intro hv
      refine ⟨labels ⟨v,hv⟩, ?_⟩
      simp
  · intro u v
    have hu : u.val < Fintype.card H.verts := u.isLt
    have hv : v.val < Fintype.card H.verts := v.isLt
    simp only [canonicalDiagram, dif_pos hu, dif_pos hv, decide_eq_true_eq, labels]
    rfl

theorem Diagram.no_path_of_one_port {D : Diagram} (hp : D.portCount ≤ 1)
    {p q r : Nat} : ¬ D.LegalPath p q r := by
  intro h
  let u : Fin D.order := ⟨p,h.1⟩
  let v : Fin D.order := ⟨q,h.2.1⟩
  have hu : u ∈ Finset.univ.filter (fun i : Fin D.order => D.degree i.val = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.2.1⟩
  have hv : v ∈ Finset.univ.filter (fun i : Fin D.order => D.degree i.val = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.2.2.1⟩
  have he := Finset.card_le_one.mp hp u hu v hv
  exact h.2.2.1 (congrArg Fin.val he)

theorem Diagram.no_matching_of_one_port {D : Diagram} (hp : D.portCount ≤ 1)
    {a b c d : Nat} : ¬ D.LegalMatching a b c d := by
  intro h
  let u : Fin D.order := ⟨a,h.1⟩
  let v : Fin D.order := ⟨b,h.2.1⟩
  have hu : u ∈ Finset.univ.filter (fun i : Fin D.order => D.degree i.val = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.2.2.2.1⟩
  have hv : v ∈ Finset.univ.filter (fun i : Fin D.order => D.degree i.val = 2) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2.2.2.2.2.1⟩
  have he := congrArg Fin.val (Finset.card_le_one.mp hp u hu v hv)
  have hd := h.2.2.2.2.1
  have hab : a ≠ b := by
    intro heq
    exact (List.nodup_cons.mp hd).1 (by simp [heq])
  exact hab he

end ZombieMain
