import ZombieMain.Boundary
import Mathlib.Data.Real.Basic

namespace ZombieMain
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem cutPairs_compl (S : Set V) : (cutPairs G Sᶜ).ncard=(cutPairs G S).ncard := by
  classical
  have hs : Prod.swap '' cutPairs G S=cutPairs G Sᶜ := by
    ext p
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv,ha⟩,rfl⟩
      exact ⟨hv,by simpa using hu,ha.symm⟩
    · rintro ⟨hu,hv,ha⟩
      exact ⟨p.swap,⟨by simpa using hv,hu,ha.symm⟩,Prod.swap_swap p⟩
  rw [← hs,Set.ncard_image_of_injective _ Prod.swap_injective]

/-- Every cut of size at most four bounds its smaller side by 4/η. -/
theorem expansion_small_side (η : ℝ) (hη : 0<η) (hex : HasEdgeExpansion G η)
    (S : Set V) (hcut : (cutPairs G S).ncard≤4) :
    ((min S.ncard (Fintype.card V-S.ncard) : Nat) : ℝ) ≤ 4/η := by
  classical
  have hn : Sᶜ.ncard=Fintype.card V-S.ncard := by
    rw [Set.ncard_compl]
    simp only [Nat.card_eq_fintype_card]
  have hS : S.ncard≤Fintype.card V := by simpa [Nat.card_eq_fintype_card] using Set.ncard_le_card S
  apply (le_div_iff₀ hη).mpr
  by_cases hs : 2*S.ncard≤Fintype.card V
  · rw [min_eq_left (by omega)]
    by_cases hpos : S.Nonempty
    · have h := hex S hpos hs
      have hcut' : ((cutPairs G S).ncard : ℝ)≤4 := by exact_mod_cast hcut
      nlinarith
    · have hz : S.ncard=0 := by rw [Set.not_nonempty_iff_eq_empty.mp hpos,Set.ncard_empty]
      simp [hz]
  · rw [min_eq_right (by omega),← hn]
    by_cases hpos : Sᶜ.Nonempty
    · have h := hex Sᶜ hpos (by omega)
      rw [cutPairs_compl] at h
      have hcut' : ((cutPairs G S).ncard : ℝ)≤4 := by exact_mod_cast hcut
      nlinarith
    · have hz : Sᶜ.ncard=0 := by rw [Set.not_nonempty_iff_eq_empty.mp hpos,Set.ncard_empty]
      simp [hz]

/-- The paper's expansion consequence for every proper short-cycle subgraph
in every finite subcubic ambient graph with a positive expansion lower bound. -/
theorem short_component_expansion (H : G.Subgraph) (hconn : H.coe.Connected)
    (hmin : ∀v∈H.verts,2≤(H.neighborSet v).ncard) (hmax : ∀v,G.degree v≤3)
    (hshort : ∀u v,H.coe.Adj u v → ∃C : H.coe.Subgraph,IsShortCycle C ∧ C.Adj u v)
    (η : ℝ) (hη : 0<η) (hex : HasEdgeExpansion G η) :
    ((min H.verts.ncard (Fintype.card V-H.verts.ncard) : Nat) : ℝ)≤4/η :=
  expansion_small_side η hη hex H.verts (four_boundary_edges H hconn hmin hmax hshort)

end ZombieMain
