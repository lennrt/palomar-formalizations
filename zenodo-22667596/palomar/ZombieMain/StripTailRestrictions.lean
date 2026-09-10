import ZombieMain.StripStructure

namespace ZombieMain

def EndPair (m p q : Nat) : Prop :=
  (p=0 ∧ q=1) ∨ (p=1 ∧ q=0) ∨
  (p=2*m-2 ∧ q=2*m-1) ∨ (p=2*m-1 ∧ q=2*m-2)

theorem endPair_adj {m caps p q : Nat} (hm : 2 ≤ m) (h : EndPair m p q) :
    (stripDiagram m caps).adj p q = true := by
  apply decide_eq_true
  unfold EndPair at h
  unfold stripAdj
  omega

theorem endPair_path_length {m caps p q r : Nat} (hm : 2 ≤ m)
    (h : (stripDiagram m caps).LegalPath p q r) (hpq : EndPair m p q) :
    r=2 ∨ r=3 := by
  have hcopy := h
  rcases hcopy with ⟨_, _, _, _, _, hlow, hhigh, _, hnew⟩
  have hn : r ≠ 1 := by
    intro hr
    have hno := hnew hr
    have hyes := endPair_adj (caps := caps) hm hpq
    rw [hno] at hyes
    cases hyes
  omega

/-- Beyond the four finite ladder rows, a short attachment joins one end rung. -/
theorem large_ladder_path_restriction {m p q r : Nat} (hm : 5 ≤ m)
    (h : (stripDiagram m 0).LegalPath p q r) :
    EndPair m p q ∧ (r=2 ∨ r=3) := by
  have hcopy := h
  rcases hcopy with ⟨hp, hq, hpq, hpd, hqd, hr1, hr3, hreach, _⟩
  have hp' : p < 2*m := by simpa [stripDiagram] using hp
  have hq' : q < 2*m := by simpa [stripDiagram] using hq
  have hpp := (strip_port_iff m 0 p (by omega) (by omega) hp).mp hpd
  have hqp := (strip_port_iff m 0 q (by omega) (by omega) hq).mp hqd
  have hcoord := strip_reach_coordinate m 0 (4-r) p q (by omega) (by omega) hp hq hreach
  simp only [stripCoordinate, if_pos hp', if_pos hq'] at hcoord
  have hend : EndPair m p q := by
    unfold StripPort at hpp hqp
    unfold EndPair
    omega
  exact ⟨hend, endPair_path_length (by omega) h hend⟩

/-- A sufficiently long singly capped ladder can only grow at its open rung. -/
theorem large_singleCap_path_restriction {m p q r : Nat} (hm : 4 ≤ m)
    (h : (stripDiagram m 1).LegalPath p q r) :
    ((p=2*m-2 ∧ q=2*m-1) ∨ (p=2*m-1 ∧ q=2*m-2)) ∧ (r=2 ∨ r=3) := by
  have hcopy := h
  rcases hcopy with ⟨hp, hq, hpq, hpd, hqd, hr1, hr3, hreach, _⟩
  have hp' : p < 2*m+1 := hp
  have hq' : q < 2*m+1 := hq
  have hpp := (strip_port_iff m 1 p (by omega) (by omega) hp).mp hpd
  have hqp := (strip_port_iff m 1 q (by omega) (by omega) hq).mp hqd
  have hcoord := strip_reach_coordinate m 1 (4-r) p q (by omega) (by omega) hp hq hreach
  have hend : (p=2*m-2 ∧ q=2*m-1) ∨ (p=2*m-1 ∧ q=2*m-2) := by
    unfold StripPort at hpp hqp
    dsimp [stripCoordinate] at hcoord
    split_ifs at hcoord <;> omega
  have hpq' : EndPair m p q := Or.inr (Or.inr hend)
  exact ⟨hend, endPair_path_length (by omega) h hpq'⟩

/-- The two remaining ports are too far apart to form a triangle or square. -/
theorem large_doubleCap_no_path {m p q r : Nat} (hm : 3 ≤ m) :
    ¬ (stripDiagram m 2).LegalPath p q r := by
  intro h
  have hcopy := h
  rcases hcopy with ⟨hp, hq, hpq, hpd, hqd, hr1, hr3, hreach, _⟩
  have hp' : p < 2*m+2 := hp
  have hq' : q < 2*m+2 := hq
  have hpp := (strip_port_iff m 2 p (by omega) (by omega) hp).mp hpd
  have hqp := (strip_port_iff m 2 q (by omega) (by omega) hq).mp hqd
  have hcoord := strip_reach_coordinate m 2 (4-r) p q (by omega) (by omega) hp hq hreach
  unfold StripPort at hpp hqp
  dsimp [stripCoordinate] at hcoord
  split_ifs at hcoord <;> omega

end ZombieMain
