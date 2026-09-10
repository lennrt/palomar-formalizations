import ZombieMain.TriangleRealization
import ZombieMain.SquareRealization
import ZombieMain.BaseCycles
import ZombieMain.AttachmentClosure

namespace ZombieMain
open SimpleGraph
variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {H C J : G.Subgraph} {D : Diagram}

theorem shortCycle_realized (e : D.Embedding H)
    (hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard)
    (hmax : ∀ v, G.degree v ≤ 3) (hC : IsShortCycle C)
    (hshare : ∃ a b, H.Adj a b ∧ C.Adj a b) :
    RealizedAttachment D H (H ⊔ C) := by
  obtain ⟨a,b,hab,hCab⟩ := hshare
  obtain ht | hs := hC.frame hCab
  · obtain ⟨c,hf⟩ := ht
    exact triangle_realized e hmin hmax hf hab
  · obtain ⟨c,d,hf⟩ := hs
    exact square_realized e hmin hmax hf hab

theorem RealizedAttachment.eq_of_one_port (h : RealizedAttachment D H J)
    (hp : D.portCount ≤ 1) : J=H := by
  rcases h with h | ⟨p,q,r,hl,_⟩ | ⟨a,b,c,d,hl,_⟩
  · exact h
  · exact False.elim (Diagram.no_path_of_one_port hp hl)
  · exact False.elim (Diagram.no_matching_of_one_port hp hl)

theorem Family.attachment_classifies (f : Family) (hf : f.Admissible)
    (e : f.diagram.Embedding H) (h : RealizedAttachment f.diagram H J) :
    ClassifiedSubgraph J := by
  rcases h with rfl | ⟨p,q,r,hl,⟨eJ⟩⟩ | ⟨a,b,c,d,hl,⟨eJ⟩⟩
  · exact Or.inr ⟨f,hf,⟨e⟩⟩
  · exact eJ.classified (f.path_classified hf hl)
  · exact eJ.classified (f.matching_classified hf hl)

/-- Universal short-cycle classification. The induction ranges over actual
edge-sharing cycles in an arbitrary finite subcubic ambient graph; the
attachment table is derived, not assumed, at every step. -/
theorem CycleGenerated.classified (hH : CycleGenerated G H)
    (hmax : ∀ v, G.degree v ≤ 3) : ClassifiedSubgraph H := by
  classical
  induction hH with
  | base hC => exact hC.classified
  | @attach H C hH hC hshare ih =>
    have hmin : ∀ v ∈ H.verts, 2 ≤ (H.neighborSet v).ncard :=
      fun _ hv => hH.minimum_degree hv
    rcases ih with hp | ⟨f,hf,⟨e⟩⟩
    · let e := canonicalEmbedding H
      have hr := shortCycle_realized e hmin hmax hC hshare
      have hports : (canonicalDiagram H).portCount ≤ 1 := by
        rw [e.port_count, hp]
      have heq := hr.eq_of_one_port hports
      rw [heq]
      exact Or.inl hp
    · exact f.attachment_classifies hf e (shortCycle_realized e hmin hmax hC hshare)

/-- Every connected finite simple graph of minimum degree two and maximum
degree three whose edges lie on triangles or quadrilaterals is either the
one-port terminal case or is exactly a member of the stated catalogue. -/
theorem cycle_union_classification
    (hconn : G.Connected) (hmin : ∀ v, 2 ≤ G.degree v)
    (hmax : ∀ v, G.degree v ≤ 3)
    (hshort : ∀ u v, G.Adj u v → ∃ C : G.Subgraph, IsShortCycle C ∧ C.Adj u v) :
    ClassifiedSubgraph (⊤ : G.Subgraph) := by
  classical
  have hedge : ∃ u v, G.Adj u v := by
    obtain ⟨u⟩ := hconn.nonempty
    have hpos : 0 < (G.neighborFinset u).card := lt_of_lt_of_le (by decide : 0 < 2) (hmin u)
    obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
    exact ⟨u,v,(G.mem_neighborFinset u v).mp hv⟩
  exact (cycleGenerated_top hconn hmax hedge hshort).classified hmax

end ZombieMain
