import ZombieDamage.FullGame

/-! Literal open ladder with optional caps and individual port stubs. Inactive
boundary slots are isolated and are not counted as internal vertices. -/
namespace ZombieDamage.OpenStrip
variable (m : Nat) (left right : Bool)

def Adj (u v : Nat) : Prop :=
  (u<m ∧ v<m ∧ (u+1=v ∨ v+1=u)) ∨
  (m≤u ∧ u<2*m ∧ m≤v ∧ v<2*m ∧ (u+1=v ∨ v+1=u)) ∨
  (u<m ∧ v=u+m) ∨ (v<m ∧ u=v+m) ∨
  (left=true ∧ ((u=2*m ∧ (v=0 ∨ v=m ∨ v=2*m+6)) ∨
                 (v=2*m ∧ (u=0 ∨ u=m ∨ u=2*m+6)))) ∨
  (right=true ∧ ((u=2*m+1 ∧ (v=m-1 ∨ v=2*m-1 ∨ v=2*m+7)) ∨
                  (v=2*m+1 ∧ (u=m-1 ∨ u=2*m-1 ∨ u=2*m+7)))) ∨
  (left=false ∧ ((u=0 ∧ v=2*m+2) ∨ (v=0 ∧ u=2*m+2) ∨
                  (u=m ∧ v=2*m+3) ∨ (v=m ∧ u=2*m+3))) ∨
  (right=false ∧ ((u=m-1 ∧ v=2*m+4) ∨ (v=m-1 ∧ u=2*m+4) ∨
                   (u=2*m-1 ∧ v=2*m+5) ∨ (v=2*m-1 ∧ u=2*m+5)))

instance (u v : Nat) : Decidable (Adj m left right u v) := by unfold Adj; infer_instance

def graph (hm : 2≤m) : Graph (Fin (2*m+8)) where
  adj u v := Adj m left right u.val v.val
  symm := by
    intro u v h
    rcases h with h | h | h | h | h | h | h | h
    · exact Or.inl ⟨h.2.1,h.1,h.2.2.symm⟩
    · exact Or.inr (Or.inl ⟨h.2.2.1,h.2.2.2.1,h.1,h.2.1,h.2.2.2.2.symm⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,h.2.symm⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.1,h.2.symm⟩)))))
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inl
      refine ⟨h.1,?_⟩
      rcases h.2 with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
    · apply Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr ∘ Or.inr
      refine ⟨h.1,?_⟩
      rcases h.2 with h | h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr (Or.inl h))
  loopless := by intro u h; unfold Adj at h; omega

def rail (b : Bool) (i : Nat) (hi : i<m) : Fin (2*m+8) :=
  ⟨if b then m+i else i,by split <;> omega⟩
def cap (b : Bool) : Fin (2*m+8) := ⟨if b then 2*m+1 else 2*m,by split <;> omega⟩
def stub (side b : Bool) : Fin (2*m+8) :=
  ⟨2*m+2+(if side then 2 else 0)+(if b then 1 else 0),by split <;> split <;> omega⟩
def capStub (side : Bool) : Fin (2*m+8) := ⟨2*m+6+(if side then 1 else 0),by split <;> omega⟩

theorem rail_inj {b c : Bool} {i j : Nat} {hi : i<m} {hj : j<m}
    (h : rail m b i hi=rail m c j hj) : b=c ∧ i=j := by
  have he := congrArg Fin.val h
  cases b <;> cases c <;> simp [rail] at he ⊢ <;> omega

/-- Advancing two rail edges has a unique middle vertex. Neither cap nor a
port stub supplies an additional geodesic. -/
theorem rail_step (hm : 2≤m) (b : Bool) (i : Nat) (hi : i+2<m) :
    (graph m left right hm).TwoApart (rail m b i (by omega)) (rail m b (i+2) hi) ∧
    ∀ x, (graph m left right hm).GeodesicReply (rail m b i (by omega))
      (rail m b (i+2) hi) x → x=rail m b (i+1) (by omega) := by
  have ht : (graph m left right hm).TwoApart (rail m b i (by omega)) (rail m b (i+2) hi) := by
    refine ⟨?_,?_,rail m b (i+1) (by omega),?_,?_⟩
    · intro he
      have hval := congrArg Fin.val he
      cases b <;> simp [rail] at hval
    · change ¬ Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
    · change Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
    · change Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
  refine ⟨ht,?_⟩
  intro x hx
  obtain ⟨h1,h2⟩ := ((graph m left right hm).geodesicReply_iff_commonNeighbor ht).1 hx
  apply Fin.ext
  change Adj m left right _ _ at h1 h2
  cases b <;> simp [rail] at * <;> unfold Adj at * <;> omega

/-- A forward step from a rung position permits only a trailing reply or
another rung reply. This includes the ends and either choice of caps. -/
theorem rung_step (hm : 2≤m) (b : Bool) (i : Nat) (hi : i+1<m) :
    (graph m left right hm).TwoApart (rail m (!b) i (by omega)) (rail m b (i+1) hi) ∧
    ∀ x, (graph m left right hm).GeodesicReply (rail m (!b) i (by omega))
      (rail m b (i+1) hi) x →
      x=rail m b i (by omega) ∨ x=rail m (!b) (i+1) hi := by
  have ht : (graph m left right hm).TwoApart (rail m (!b) i (by omega)) (rail m b (i+1) hi) := by
    refine ⟨?_,?_,rail m b i (by omega),?_,?_⟩
    · intro he
      have hval := congrArg Fin.val he
      cases b <;> simp [rail] at hval <;> omega
    · change ¬ Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
    · change Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
    · change Adj m left right _ _
      cases b <;> simp [rail] <;> unfold Adj <;> omega
  refine ⟨ht,?_⟩
  intro x hx
  obtain ⟨h1,h2⟩ := ((graph m left right hm).geodesicReply_iff_commonNeighbor ht).1 hx
  change Adj m left right _ _ at h1 h2
  have he : x.val=(rail m b i (by omega)).val ∨ x.val=(rail m (!b) (i+1) hi).val := by
    cases b <;> simp [rail] at * <;> unfold Adj at * <;> omega
  exact he.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))

end ZombieDamage.OpenStrip
