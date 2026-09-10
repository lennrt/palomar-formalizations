import ZombieMain.CycleFrames
import ZombieMain.PortTransport
import Mathlib.Data.Fin.VecNotation

namespace ZombieMain
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {C : G.Subgraph}
set_option maxHeartbeats 1000000

def TriangleFrame.embedding {a b c : V} (h : TriangleFrame C a b c) :
    (stripDiagram 1 1).Embedding C := by
  have hn := h.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true, not_or] at hn
  refine ⟨![a,b,c], ?_, ?_, ?_⟩
  · intro i j hij
    change Fin 3 at i j
    fin_cases i <;> fin_cases j <;> simp_all
  · ext v
    rw [h.verts]
    constructor
    · rintro ⟨i,rfl⟩
      change Fin 3 at i
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      · exact ⟨⟨0,by decide⟩,rfl⟩
      · exact ⟨⟨1,by decide⟩,rfl⟩
      · exact ⟨⟨2,by decide⟩,rfl⟩
  · intro i j
    change Fin 3 at i j
    rw [h.adjacency]
    fin_cases i <;> fin_cases j <;>
      simp [stripDiagram, stripAdj, hn.1.1, hn.1.2, hn.2,
        (Ne.symm hn.1.1), (Ne.symm hn.1.2), (Ne.symm hn.2)]

def SquareFrame.embedding {a b c d : V} (h : SquareFrame C a b c d) :
    (stripDiagram 2 0).Embedding C := by
  have hn := h.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true, not_or] at hn
  refine ⟨![a,b,d,c], ?_, ?_, ?_⟩
  · intro i j hij
    change Fin 4 at i j
    fin_cases i <;> fin_cases j <;> simp_all
  · ext v
    rw [h.verts]
    constructor
    · rintro ⟨i,rfl⟩
      change Fin 4 at i
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨⟨0,by decide⟩,rfl⟩
      · exact ⟨⟨1,by decide⟩,rfl⟩
      · exact ⟨⟨3,by decide⟩,rfl⟩
      · exact ⟨⟨2,by decide⟩,rfl⟩
  · intro i j
    change Fin 4 at i j
    rw [h.adjacency]
    fin_cases i <;> fin_cases j <;>
      simp [stripDiagram, stripAdj, hn.1.1, hn.1.2.1, hn.1.2.2,
        hn.2.1.1, hn.2.1.2, hn.2.2, (Ne.symm hn.1.1), (Ne.symm hn.1.2.1),
        (Ne.symm hn.1.2.2), (Ne.symm hn.2.1.1), (Ne.symm hn.2.1.2), (Ne.symm hn.2.2)]

theorem IsShortCycle.classified (h : IsShortCycle C) : ClassifiedSubgraph C := by
  have hc := h
  obtain ⟨v,p,hp,hlen,rfl⟩ := hc
  have hpn : ¬ p.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    have hh := hp.three_le_length
    omega
  obtain ht | hs := h.frame (p.toSubgraph_adj_snd hpn)
  · obtain ⟨c,hc⟩ := ht
    exact Or.inr ⟨.singleCap 1, by decide, ⟨hc.embedding⟩⟩
  · obtain ⟨c,d,hc⟩ := hs
    exact Or.inr ⟨.ladder 2, by decide, ⟨hc.embedding⟩⟩

end ZombieMain
