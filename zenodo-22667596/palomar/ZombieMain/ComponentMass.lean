import ZombieMain.ComponentQuotient

namespace ZombieMain
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V}

noncomputable def componentMass (L : List (shortGraph G).ConnectedComponent) : Nat :=
  (L.map (fun K => K.supp.ncard)).sum

@[simp] theorem componentMass_nil : componentMass (G:=G) []=0 := rfl
@[simp] theorem componentMass_cons (K : (shortGraph G).ConnectedComponent) (L : List _) :
    componentMass (K::L)=K.supp.ncard+componentMass L := rfl

/-- A simple quotient path charges each original vertex at most once. -/
theorem componentMass_le (L : List (shortGraph G).ConnectedComponent) (hL : L.Nodup) :
    componentMass L ≤ Fintype.card V := by
  classical
  let S := L.toFinset
  have hdisj : (↑S : Set (shortGraph G).ConnectedComponent).PairwiseDisjoint
      (fun K => K.supp.toFinset) := by
    intro K _ J _ hne
    apply Finset.disjoint_left.mpr
    intro v hvK hvJ
    exact hne (ConnectedComponent.eq_of_common_vertex
      (Set.mem_toFinset.mp hvK) (Set.mem_toFinset.mp hvJ))
  calc
    componentMass L = ∑ K∈S,K.supp.toFinset.card := by
      rw [show (∑ K∈S,K.supp.toFinset.card)=(L.map (fun K => K.supp.toFinset.card)).sum from
        List.sum_toFinset (fun K => K.supp.toFinset.card) hL]
      simp [componentMass,Set.ncard_eq_toFinset_card']
    _ = (S.biUnion (fun K => K.supp.toFinset)).card := (Finset.card_biUnion hdisj).symm
    _ ≤ Fintype.card V := Finset.card_le_univ _

end ZombieMain
