module

public import ShellObservability.Robust
public import ShellObservability.RectangleGeometry

@[expose] public section

/-! Erasure reconstruction of additive rectangular fields. This elementary
coding mechanism is included to make the geometric first-moment consequence
precise; the general minimum-distance principle is not a novelty claim. -/
namespace ShellObservability.AdditiveFields
open Finset

variable {R C A : Type*} [Fintype R] [Fintype C] [AddCommGroup A] [DecidableEq A]

/-- A rectangular field is a sum of one potential on each coordinate family. -/
def IsAdditive (f : R × C → A) : Prop :=
  ∃ a : R → A, ∃ b : C → A, ∀ r c, f (r,c) = a r+b c

theorem zero_isAdditive : IsAdditive (fun _ : R × C => (0 : A)) :=
  ⟨fun _ => 0, fun _ => 0, by simp⟩

theorem IsAdditive.sub {f g : R × C → A} (hf : IsAdditive f) (hg : IsAdditive g) :
    IsAdditive (fun p => f p-g p) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨fun r => a r-c r, fun s => b s-d s,?_⟩
  intro r s
  dsimp only
  rw [hf,hg]
  abel

/-- A nonzero additive field has at least the shorter side many nonzero entries. -/
theorem support_lower {f : R × C → A} (hf : IsAdditive f)
    (hne : f ≠ fun _ => 0) :
    min (Fintype.card R) (Fintype.card C) ≤
      (univ.filter (fun p => f p ≠ 0)).card := by
  classical
  let D := univ.filter (fun p : R × C => f p ≠ 0)
  by_cases hrow : ∀ r, ∃ c, f (r,c) ≠ 0
  · choose c hc using hrow
    have hh : Fintype.card R ≤ D.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_le_of_injective (f := fun r =>
        (⟨(r,c r), by simp [D,hc r]⟩ : D))
      intro r s h
      exact congrArg (fun p : D => p.val.1) h
    exact (Nat.min_le_left _ _).trans hh
  · push Not at hrow
    obtain ⟨r0,hr0⟩ := hrow
    obtain ⟨p,hp⟩ : ∃ p, f p ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    obtain ⟨a,b,hf⟩ := hf
    have hb (c : C) : b c = -a r0 := by
      have hh := hr0 c
      rw [hf] at hh
      exact eq_neg_of_add_eq_zero_right hh
    have hnonzero (c : C) : f (p.1,c) ≠ 0 := by
      have heq : f (p.1,c) = f p := by
        rcases p with ⟨r,s⟩
        rw [hf,hf,hb,hb]
      rwa [heq]
    have hh : Fintype.card C ≤ D.card := by
      rw [← Fintype.card_coe]
      apply Fintype.card_le_of_injective (f := fun c =>
        (⟨(p.1,c), by simp [D,hnonzero c]⟩ : D))
      intro r s h
      exact congrArg (fun p : D => p.val.2) h
    exact (Nat.min_le_right _ _).trans hh

/-- Distinct additive rectangular fields differ in at least the shorter side. -/
theorem hamming_lower {f g : R × C → A} (hf : IsAdditive f) (hg : IsAdditive g)
    (hne : f ≠ g) : min (Fintype.card R) (Fintype.card C) ≤ hammingDist f g := by
  have hh := support_lower (hf.sub hg) (by
    intro h
    apply hne
    funext p
    have hp := congrFun h p
    exact sub_eq_zero.mp hp)
  simpa only [sub_ne_zero, hammingDist] using hh

/-- The standard rectangle identity reconstructs one missing entry. -/
theorem rectangle_identity {f : R × C → A} (hf : IsAdditive f)
    (r r' : R) (c c' : C) :
    f (r,c) = f (r,c')+f (r',c)-f (r',c') := by
  obtain ⟨a,b,hf⟩ := hf
  simp only [hf]
  abel

/-- Every number of erasures below the shorter side can be repaired. -/
theorem tolerates_erasures (e : ℕ)
    (he : e < min (Fintype.card R) (Fintype.card C)) :
    ToleratesErasures (fun f : R × C → A => f) IsAdditive e := by
  rw [toleratesErasures_iff]
  intro f g hf hg hne
  exact he.trans_le (hamming_lower hf hg hne)

variable [Nonempty R] [Nonempty C] [Nontrivial A]

/-- A whole row or column is a sharp erasure obstruction. -/
theorem exists_minimum_distance :
    ∃ f g : R × C → A, IsAdditive f ∧ IsAdditive g ∧ f ≠ g ∧
      hammingDist f g = min (Fintype.card R) (Fintype.card C) := by
  classical
  obtain ⟨v,hv⟩ := exists_ne (0 : A)
  obtain ⟨r0⟩ := ‹Nonempty R›
  obtain ⟨c0⟩ := ‹Nonempty C›
  by_cases hsize : Fintype.card R ≤ Fintype.card C
  · let f : R × C → A := fun p => if p.2 = c0 then v else 0
    refine ⟨f,fun _ => 0,⟨fun _ => 0,fun c => if c=c0 then v else 0,by simp [f]⟩,
      zero_isAdditive,?_,?_⟩
    · intro h
      have hh := congrFun h (r0,c0)
      exact hv (by simpa [f] using hh)
    · rw [Nat.min_eq_left hsize]
      have hh : univ.filter (fun p => f p ≠ 0) =
          (univ : Finset R) ×ˢ {c0} := by
        ext p
        simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton]
        simp [f,hv]
      change (univ.filter (fun p => f p ≠ 0)).card = _
      rw [hh]
      simp
  · let f : R × C → A := fun p => if p.1 = r0 then v else 0
    refine ⟨f,fun _ => 0,⟨fun r => if r=r0 then v else 0,fun _ => 0,by simp [f]⟩,
      zero_isAdditive,?_,?_⟩
    · intro h
      have hh := congrFun h (r0,c0)
      exact hv (by simpa [f] using hh)
    · rw [Nat.min_eq_right (by omega)]
      have hh : univ.filter (fun p => f p ≠ 0) =
          {r0} ×ˢ (univ : Finset C) := by
        ext p
        simp only [mem_filter, mem_univ, true_and, mem_product, mem_singleton, and_true]
        simp [f,hv]
      change (univ.filter (fun p => f p ≠ 0)).card = _
      rw [hh]
      simp

/-- Exact erasure threshold for additive rectangular fields over any nontrivial
abelian group. It concerns recovery of the field, rather than of its potentials. -/
theorem tolerates_erasures_iff (e : ℕ) :
    ToleratesErasures (fun f : R × C → A => f) IsAdditive e ↔
      e < min (Fintype.card R) (Fintype.card C) := by
  constructor
  · intro he
    obtain ⟨f,g,hf,hg,hne,hd⟩ := exists_minimum_distance (R := R) (C := C) (A := A)
    have hh := (toleratesErasures_iff _ _ e).mp he f g hf hg hne
    rwa [hd] at hh
  · exact tolerates_erasures e

/-- The observed entries, viewed as edges between all row and column vertices.
Isolated coordinate vertices remain part of this graph. -/
def observationGraph (seen : Set (R × C)) : SimpleGraph (R ⊕ C) where
  Adj u v := match u,v with
    | Sum.inl r, Sum.inr c => (r,c) ∈ seen
    | Sum.inr c, Sum.inl r => (r,c) ∈ seen
    | _,_ => False
  symm := ⟨by intro u v h; cases u <;> cases v <;> exact h⟩
  loopless := ⟨by intro v; cases v <;> simp⟩

/-- Uniqueness of the entire field from the prescribed observations. -/
def Recovers (seen : Set (R × C)) : Prop :=
  ∀ f g : R × C → A, IsAdditive f → IsAdditive g →
    (∀ p ∈ seen, f p = g p) → f = g

private theorem edge_constant_walk {V : Type*} {G : SimpleGraph V}
    (p : V → A) (hp : ∀ u v, G.Adj u v → p u = p v)
    {u v : V} (w : G.Walk u v) : p u = p v := by
  induction w with
  | nil => rfl
  | @cons u v w huv tail ih => exact (hp u v huv).trans ih

private theorem connected_iff_cross (seen : Set (R × C)) :
    (observationGraph seen).Connected ↔
      ∀ r c, (observationGraph seen).Reachable (Sum.inl r) (Sum.inr c) := by
  constructor
  · exact fun h r c => h _ _
  · intro h
    obtain ⟨r0⟩ := ‹Nonempty R›
    obtain ⟨c0⟩ := ‹Nonempty C›
    refine ⟨?_⟩
    intro u v
    cases u with
    | inl r =>
      cases v with
      | inl s => exact (h r c0).trans (h s c0).symm
      | inr c => exact h r c
    | inr c =>
      cases v with
      | inl r => exact (h r c).symm
      | inr d => exact (h r0 c).symm.trans (h r0 d)

/-- Exact topological recovery criterion: observed scalar entries recover all
additive fields precisely when the bipartite observation graph is connected. -/
theorem recovers_iff_connected (seen : Set (R × C)) :
    Recovers (A := A) seen ↔ (observationGraph seen).Connected := by
  classical
  constructor
  · intro hrec
    rw [connected_iff_cross]
    intro r0 c0
    by_contra hnc
    obtain ⟨v,hv⟩ := exists_ne (0 : A)
    let p : R ⊕ C → A := fun u =>
      if (observationGraph seen).Reachable (Sum.inl r0) u then v else 0
    let f : R × C → A := fun z => p (Sum.inl z.1)-p (Sum.inr z.2)
    have hf : IsAdditive f :=
      ⟨fun r => p (Sum.inl r), fun c => -p (Sum.inr c), by intro r c; simp only [f,sub_eq_add_neg]⟩
    have hzero := hrec f (fun _ => 0) hf zero_isAdditive (by
      rintro ⟨r,c⟩ hseen
      have hadj : (observationGraph seen).Adj (Sum.inl r) (Sum.inr c) := hseen
      have hr : (observationGraph seen).Reachable (Sum.inl r0) (Sum.inl r) ↔
          (observationGraph seen).Reachable (Sum.inl r0) (Sum.inr c) :=
        ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.reachable.symm⟩
      simp only [f,p,hr,sub_self])
    have hh := congrFun hzero (r0,c0)
    exact hv (by simpa [f,p,hnc,SimpleGraph.Reachable.rfl] using hh)
  · intro hconn f g hf hg hagree
    obtain ⟨a,b,hd⟩ := hf.sub hg
    let p : R ⊕ C → A := Sum.elim a (fun c => -b c)
    have heq : ∀ u v, (observationGraph seen).Adj u v → p u = p v := by
      intro u v huv
      cases u with
      | inl r =>
        cases v with
        | inl s => exact False.elim huv
        | inr c =>
          have hh := hagree (r,c) huv
          have hz : a r+b c = 0 := by rw [← hd r c]; exact sub_eq_zero.mpr hh
          exact eq_neg_of_add_eq_zero_left hz
      | inr c =>
        cases v with
        | inl r =>
          have hh := hagree (r,c) huv
          have hz : a r+b c = 0 := by rw [← hd r c]; exact sub_eq_zero.mpr hh
          exact (eq_neg_of_add_eq_zero_left hz).symm
        | inr d => exact False.elim huv
    funext z
    have hp := (hconn (Sum.inl z.1) (Sum.inr z.2)).elim
      (fun w => edge_constant_walk p heq w)
    have hz : f z-g z = 0 := by
      calc
        f z-g z = a z.1+b z.2 := hd z.1 z.2
        _ = 0 := by
          change a z.1 = -b z.2 at hp
          rw [hp,neg_add_cancel]
    exact sub_eq_zero.mp hz

end ShellObservability.AdditiveFields

namespace ShellObservability.Rectangle
open ShellTomography Finset

/-- The total-distance field of a population, written as an integer-valued sum. -/
noncomputable def momentField (w h : ℕ) (x : Configuration (Grid w h))
    (s : Grid w h) : ℤ :=
  ∑ v, (x v : ℤ) * ((gridGraph w h).dist s v : ℤ)

/-- Actual rectangular graph-distance moments are additive coordinate fields. -/
theorem momentField_isAdditive (w h : ℕ) (x : Configuration (Grid w h)) :
    AdditiveFields.IsAdditive (momentField w h x) := by
  refine ⟨fun r => ∑ v, (x v : ℤ)*(natAbsDiff r.val v.1.val : ℤ),
    fun c => ∑ v, (x v : ℤ)*(natAbsDiff c.val v.2.val : ℤ),?_⟩
  intro r c
  simp only [momentField,grid_dist_eq_manhattan,manhattan,Nat.cast_add,
    mul_add,Finset.sum_add_distrib]

/-- The sum expression is exactly the first moment of the reported full bag. -/
theorem momentField_eq_bag_sum (w h : ℕ) (x : Configuration (Grid w h)) (s : Grid w h) :
    momentField w h x s = ((bag (fun s v => (gridGraph w h).dist s v) x s).sum : ℤ) := by
  classical
  have hsum : (bag (fun s v => (gridGraph w h).dist s v) x s).sum =
      ∑ v, x v * (gridGraph w h).dist s v := by
    unfold bag
    generalize (Finset.univ : Finset (Grid w h)) = t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert v t hv ih => simp [sum_insert hv,Multiset.sum_add,ih]
  rw [hsum]
  simp [momentField]

/-- Losing fewer than the shorter side many first moments cannot hide a
change in the full first-moment field, regardless of population mass. -/
theorem momentField_erasure_recovery (w h e : ℕ) (he : e < min w h)
    (erased : Finset (Grid w h)) (hecard : erased.card ≤ e)
    (x y : Configuration (Grid w h))
    (hagree : ∀ s, s ∉ erased → momentField w h x s = momentField w h y s) :
    momentField w h x = momentField w h y := by
  apply AdditiveFields.tolerates_erasures e (by simpa using he) erased hecard
    _ _ (momentField_isAdditive w h x) (momentField_isAdditive w h y) hagree

/-- Arbitrary erasure patterns are safe for first-moment reconstruction whenever
the surviving bipartite coordinate graph stays connected. -/
theorem momentField_connected_recovery (w h : ℕ) [NeZero w] [NeZero h]
    (seen : Set (Grid w h)) (hconn : (AdditiveFields.observationGraph seen).Connected)
    (x y : Configuration (Grid w h))
    (hagree : ∀ s ∈ seen, momentField w h x s = momentField w h y s) :
    momentField w h x = momentField w h y :=
  (AdditiveFields.recovers_iff_connected seen).mpr hconn _ _
    (momentField_isAdditive w h x) (momentField_isAdditive w h y) hagree

end ShellObservability.Rectangle
