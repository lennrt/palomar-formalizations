import ZombieMain.StripTailRestrictions

namespace ZombieMain
set_option maxHeartbeats 1000000

theorem capped_no_matching {m caps a b c d : Nat} (hm : 2 ≤ m)
    (hc : 1 ≤ caps) (hc' : caps ≤ 2) :
    ¬ (stripDiagram m caps).LegalMatching a b c d := by
  intro h
  rcases h with ⟨ha, hb, hcc, hd, hdistinct, had, hbd, hcd, hdd, _⟩
  have ha' : a < 2*m+caps := ha
  have hb' : b < 2*m+caps := hb
  have hc'' : c < 2*m+caps := hcc
  have hd' : d < 2*m+caps := hd
  have hap := (strip_port_iff m caps a hm hc' ha).mp had
  have hbp := (strip_port_iff m caps b hm hc' hb).mp hbd
  have hcp := (strip_port_iff m caps c hm hc' hcc).mp hcd
  have hdp := (strip_port_iff m caps d hm hc' hd).mp hdd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_false_eq_true, and_true, not_or] at hdistinct
  unfold StripPort at hap hbp hcp hdp
  omega

theorem ladder_matching_endPairs {m a b c d : Nat} (hm : 3 ≤ m)
    (h : (stripDiagram m 0).LegalMatching a b c d) :
    EndPair m a b ∧ EndPair m c d := by
  rcases h with ⟨ha, hb, hcc, hd, _, had, hbd, hcd, hdd, hab, hcd', _⟩
  have ha' : a < 2*m := ha
  have hb' : b < 2*m := hb
  have hc' : c < 2*m := hcc
  have hd' : d < 2*m := hd
  have hap := (strip_port_iff m 0 a (by omega) (by omega) ha).mp had
  have hbp := (strip_port_iff m 0 b (by omega) (by omega) hb).mp hbd
  have hcp := (strip_port_iff m 0 c (by omega) (by omega) hcc).mp hcd
  have hdp := (strip_port_iff m 0 d (by omega) (by omega) hd).mp hdd
  have hab' : stripAdj m 0 a b := of_decide_eq_true hab
  have hcd'' : stripAdj m 0 c d := of_decide_eq_true hcd'
  unfold StripPort at hap hbp hcp hdp
  unfold stripAdj at hab' hcd''
  unfold EndPair
  omega

end ZombieMain
