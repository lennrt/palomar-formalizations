import ZombieDamage.OpenStrip
import ZombieDamage.ShortGraph

namespace ZombieDamage.OpenStrip
open FullGame
variable (m : Nat) (left right : Bool)

def Forward (i : Nat) (hi : i<m) (b : Bool) (s : State (Fin (2*m+8))) : Prop :=
  s.survivor=rail m b i hi ∧
  ((∃ j, ∃ hj : j<m, j+1=i ∧ s.zombie=rail m b j hj) ∨
    s.zombie=rail m (!b) i hi)

theorem forward_step (hm : 2≤m) (i : Nat) (hi : i+1<m) (b : Bool)
    (s : State (Fin (2*m+8))) (hf : Forward m i (by omega) b s) :
    (graph m left right hm).adj s.zombie s.survivor ∧
    (graph m left right hm).adj s.survivor (rail m b (i+1) hi) ∧
    (graph m left right hm).TwoApart s.zombie (rail m b (i+1) hi) ∧
    ∀ z, (graph m left right hm).GeodesicReply s.zombie (rail m b (i+1) hi) z →
      Forward m (i+1) hi b ((s.survivorTo (rail m b (i+1) hi)).zombieTo z) := by
  obtain ⟨hs,hz⟩ := hf
  have he : (graph m left right hm).adj s.survivor (rail m b (i+1) hi) := by
    rw [hs]
    change Adj m left right _ _
    cases b <;> simp [rail,Adj] <;> omega
  rcases hz with ⟨j,hj,hji,hz⟩ | hz
  · have hstep := rail_step m left right hm b j (by omega)
    have hji2 : j+2=i+1 := by omega
    simp only [hji2] at hstep
    have he0 : (graph m left right hm).adj s.zombie s.survivor := by
      rw [hz,hs]
      change Adj m left right _ _
      cases b <;> simp [rail,Adj] <;> omega
    refine ⟨he0,he,hz ▸ hstep.1,?_⟩
    intro z hrep
    rw [hz] at hrep
    have hz' := hstep.2 z hrep
    refine ⟨rfl,Or.inl ⟨i,by omega,rfl,?_⟩⟩
    simpa [hji,State.zombieTo] using hz'
  · have he0 : (graph m left right hm).adj s.zombie s.survivor := by
      rw [hz,hs]
      change Adj m left right _ _
      cases b <;> simp [rail,Adj] <;> omega
    have hstep := rung_step m left right hm b i hi
    refine ⟨he0,he,hz ▸ hstep.1,?_⟩
    intro z hrep
    rw [hz] at hrep
    rcases hstep.2 z hrep with ht | hr
    · exact ⟨rfl,Or.inl ⟨i,by omega,rfl,ht⟩⟩
    · exact ⟨rfl,Or.inr hr⟩

/-- Any finite segment, at arbitrary ladder length, with all geodesic ties
retained. Endpoint configuration and exact departure interval are preserved. -/
theorem forward_route (hm : 2≤m) (count i : Nat) (hi : i+count<m)
    (b : Bool) (s : State (Fin (2*m+8))) (hf : Forward m i (by omega) b s) :
    ForcesWithin (graph m left right hm)
      (fun p t => p=.survivor ∧ Forward m (i+count) hi b t ∧
        ∀ k, ∀ hk : k<count, t.damaged (rail m b (i+k) (by omega)))
      count .survivor s := by
  induction count generalizing i s with
  | zero =>
    apply ForcesWithin.done
    refine ⟨rfl,hf,?_⟩
    intro k hk
    omega
  | succ count ih =>
    obtain ⟨huv,hvw,ht,hn⟩ := forward_step m left right hm i (by omega) b s hf
    apply safe_step (graph m left right hm) s (rail m b (i+1) (by omega)) huv hvw ht
    intro z hz
    let t := (s.survivorTo (rail m b (i+1) (by omega))).zombieTo z
    have h := ih (i+1) (by omega) t (hn z hz)
    have hD : t.damaged (rail m b i (by omega)) := Or.inr hf.1.symm
    apply (h.preserve_set (fun v => v=rail m b i (by omega)) (fun v hv => hv ▸ hD)).mono
    intro p u hu
    have hsum : i+1+count=i+(count+1) := by omega
    refine ⟨hu.1.1,?_,?_⟩
    · simpa only [hsum] using hu.1.2.1
    · intro k hk
      cases k with
      | zero => exact hu.2 _ rfl
      | succ k =>
        have hd := hu.1.2.2 k (by omega)
        have hsum' : i+1+k=i+(k+1) := by omega
        simpa only [hsum'] using hd

/-- Every active right open-end stub has only its own endpoint as neighbor. -/
theorem right_stub_neighbor (hm : 2≤m) (b : Bool) (x : Fin (2*m+8))
    (h : (graph m left false hm).adj (stub m true b) x) :
    x=rail m b (m-1) (by omega) := by
  apply Fin.ext
  change Adj m left false _ _ at h
  cases b <;> simp [stub,rail,Adj] at * <;> omega

theorem open_exit (hm : 2≤m) (b : Bool) (s : State (Fin (2*m+8)))
    (hf : Forward m (m-1) (by omega) b s) :
    ForcesWithin (graph m left false hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (m-1) (by omega) ∧
        t.survivor=stub m true b ∧ t.damaged (rail m b (m-1) (by omega)))
      1 .survivor s := by
  obtain ⟨hs,hz⟩ := hf
  have huv : (graph m left false hm).adj s.zombie s.survivor := by
    rw [hs]
    rcases hz with ⟨j,hj,hji,hz⟩ | hz
    · rw [hz]
      change Adj m left false _ _
      cases b <;> simp [rail,Adj] <;> omega
    · rw [hz]
      change Adj m left false _ _
      cases b <;> simp [rail,Adj] <;> omega
  have hvw : (graph m left false hm).adj s.survivor (stub m true b) := by
    rw [hs]
    change Adj m left false _ _
    cases b <;> simp [rail,stub,Adj] <;> omega
  have hne : s.zombie≠stub m true b := by
    intro he
    rcases hz with ⟨j,hj,_,hz⟩ | hz
    · have hval := congrArg Fin.val (hz.symm.trans he)
      cases b <;> simp [rail,stub] at hval <;> omega
    · have hval := congrArg Fin.val (hz.symm.trans he)
      cases b <;> simp [rail,stub] at hval <;> omega
  have ht : (graph m left false hm).TwoApart s.zombie (stub m true b) := by
    refine ⟨hne,?_,s.survivor,huv,hvw⟩
    intro h
    have he := right_stub_neighbor m left hm b s.zombie ((graph m left false hm).symm h)
    have he' : s.zombie=s.survivor := he.trans hs.symm
    exact (graph m left false hm).loopless _ (he' ▸ huv)
  apply safe_step (graph m left false hm) s (stub m true b) huv hvw ht
  intro z hz'
  have hrep := ((graph m left false hm).geodesicReply_iff_commonNeighbor ht).1 hz'
  have he := right_stub_neighbor m left hm b z ((graph m left false hm).symm hrep.2)
  exact .done 0 .survivor _ ⟨rfl,he,rfl,Or.inr hs.symm⟩

/-- A whole suffix and its clean exit, including the last source departure. -/
theorem open_route (hm : 2≤m) (i : Nat) (hi : i<m) (b : Bool)
    (s : State (Fin (2*m+8))) (hf : Forward m i hi b s) :
    ForcesWithin (graph m left false hm)
      (fun p t => p=.survivor ∧ t.zombie=rail m b (m-1) (by omega) ∧
        t.survivor=stub m true b ∧
        ∀ j, ∀ hj : j<m, i≤j → t.damaged (rail m b j hj)) (m-i) .survivor s := by
  have hcount : i+(m-1-i)=m-1 := by omega
  have first := forward_route m left false hm (m-1-i) i (by omega) b s hf
  have hbudget : m-i=(m-1-i)+1 := by omega
  rw [hbudget]
  apply first.bind 1
  intro phase t ht
  obtain ⟨hp,hf',hD⟩ := ht
  subst phase
  have hf'' : Forward m (m-1) (by omega) b t := by simpa only [hcount] using hf'
  apply ((open_exit m left hm b t hf'').preserve_set t.damaged (fun _ h => h)).mono
  intro p u hu
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2.1,?_⟩
  intro j hj hij
  by_cases he : j=m-1
  · subst j
    exact hu.1.2.2.2
  · have hji : i+(j-i)=j := by omega
    have hd := hD (j-i) (by omega)
    have hd' : t.damaged (rail m b j hj) := by simpa only [hji] using hd
    exact hu.2 _ hd'

end ZombieDamage.OpenStrip
