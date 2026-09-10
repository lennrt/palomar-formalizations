import ZombieMain.MatchingRestrictions

namespace ZombieMain
set_option maxHeartbeats 1000000

/-- Closing the two distinct end rungs gives either the prism or the
twisted ladder, on exactly the same labelled vertex set. -/
theorem endPairs_matching_closed {m a b c d : Nat}
    (h1 : EndPair m a b) (h2 : EndPair m c d)
    (hd : [a,b,c,d].Nodup) :
    ∃ twisted : Bool,
      Nonempty (((stripDiagram m 0).adjoinMatching a b c d).Iso
        (closedDiagram m twisted)) := by
  rcases h1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals rcases h2 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    List.nodup_nil, not_false_eq_true, and_true, not_or, not_true_eq_false,
    true_or, false_and, and_false] at hd
  all_goals first
    | contradiction
    | (refine ⟨false, ⟨Diagram.isoOfNat _ _ id id (fun _ h => h)
        (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl) ?_⟩⟩
       intro u v _ _
       apply Bool.eq_iff_iff.mpr
       simp [Diagram.adjoinMatching, closedDiagram, stripDiagram]
       tauto)
    | (refine ⟨true, ⟨Diagram.isoOfNat _ _ id id (fun _ h => h)
        (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl) ?_⟩⟩
       intro u v _ _
       apply Bool.eq_iff_iff.mpr
       simp [Diagram.adjoinMatching, closedDiagram, stripDiagram]
       tauto)

theorem large_ladder_matching_classified {m a b c d : Nat} (hm : 3 ≤ m)
    (h : (stripDiagram m 0).LegalMatching a b c d) :
    ((stripDiagram m 0).adjoinMatching a b c d).Classified := by
  obtain ⟨h1,h2⟩ := ladder_matching_endPairs hm h
  obtain ⟨twisted, he⟩ := endPairs_matching_closed h1 h2 h.2.2.2.2.1
  cases twisted
  · exact Or.inr ⟨.prism m, hm, he⟩
  · exact Or.inr ⟨.mobius m, hm, he⟩

end ZombieMain
