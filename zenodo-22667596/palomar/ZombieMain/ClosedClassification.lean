import ZombieMain.FamilyRoutes

namespace ZombieMain
open SimpleGraph ZombieDamage
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Family.Closed : Family → Prop
  | .prism _ | .mobius _ | .k4 | .k33 => True
  | _ => False

theorem Family.closed_or_port (f : Family) (hf : f.Admissible) :
    f.Closed ∨ ∃i : Fin f.diagram.order,f.diagram.degree i.val=2 := by
  cases f with
  | prism m | mobius m | k4 | k33 => exact Or.inl trivial
  | ladder m =>
    right
    refine ⟨⟨0,by change 0<2*m+0; change 2≤m at hf; omega⟩,?_⟩
    apply (strip_port_iff m 0 0 hf (by omega) (by change 2≤m at hf; omega)).mpr
    simp [StripPort]
    change 2≤m at hf
    omega
  | singleCap m =>
    right
    by_cases hm : m=1
    · subst m; exact (by decide)
    have hm' : 2≤m := by change 1≤m at hf; omega
    refine ⟨⟨2*m,by change 2*m<2*m+1; omega⟩,?_⟩
    apply (strip_port_iff m 1 (2*m) hm' (by omega) (by omega)).mpr
    exact Or.inr (by omega)
  | doubleCap m =>
    right
    by_cases hm : m=1
    · subst m; exact (by decide)
    have hm' : 2≤m := by change 1≤m at hf; omega
    refine ⟨⟨2*m,by change 2*m<2*m+2; omega⟩,?_⟩
    apply (strip_port_iff m 2 (2*m) hm' (by omega) (by omega)).mpr
    exact Or.inr (by omega)
  | k23 | k33e | p3e | q3v | q3e => right; decide

theorem top_degree_cubic (hcubic : ∀ v,G.degree v=3) (v : V) :
    ((⊤ : G.Subgraph).neighborSet v).ncard=3 := by
  change (G.neighborSet v).ncard=3
  rw [← Set.fintypeCard_eq_ncard,G.card_neighborSet_eq_degree,hcubic]

/-- With no clean edge, the actual graph is exactly one of the closed
families; this is derived from the universal short-cycle classification. -/
theorem no_clean_classification (hconn : G.Connected) (hcubic : ∀ v,G.degree v=3)
    (hn : ¬∃p q,(gameGraph G).Clean p q) :
    ∃f : Family,f.Admissible ∧ f.Closed ∧ Nonempty (f.diagram.Embedding (⊤ : G.Subgraph)) := by
  classical
  have hshort : ∀u v,G.Adj u v → ∃C : G.Subgraph,IsShortCycle C ∧ C.Adj u v := by
    intro u v huv
    have hs := (shortEdge_iff_gameShort G u v).mpr ⟨huv,fun h => hn ⟨u,v,h⟩⟩
    exact shortEdge_iff_cycle.mp hs
  obtain hp | ⟨f,hf,⟨e⟩⟩ := cycle_union_classification hconn
    (fun v => by rw [hcubic]; omega) (fun v => by rw [hcubic]) hshort
  · have hempty : portVertices (⊤ : G.Subgraph)=∅ := by
      ext v
      simp only [portVertices,Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
      intro h
      have hd := top_degree_cubic hcubic v
      omega
    rw [hempty,Set.ncard_empty] at hp
    omega
  · have hclosed : f.Closed := by
      obtain h | ⟨i,hi⟩ := f.closed_or_port hf
      · exact h
      · have he := (e.degree i).trans (top_degree_cubic hcubic (e.vertices i))
        omega
    exact ⟨f,hf,hclosed,⟨e⟩⟩

end ZombieMain
