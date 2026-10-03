module
public import Mathlib

/-!
# Geometric certificates: independent research statements

This Challenge selects fourteen endpoints in six related research groups:
fault-tolerant square grids, hypercube equalization, even bishop boards,
generalized Petersen counterexamples, a connected fractional-face
counterexample, and long rectangular grids. Definitions use concrete graph
distances and multiplicity-preserving population reports. No proof-library
module is imported. Deliberate theorem holes are the comparison obligations.

Auxiliary algebra, interpolation and prefix identities remain proved in the
library but are not separate submission claims. The single-moment capacity
and sharp moment-code-distance theorems, the unrestricted grid optimum and
exhaustive folded-cube lower bounds are not asserted by this Challenge.
The project README records source context, attribution and exact limitations.
-/
@[expose] public section

namespace ShellTomography
universe u v w
abbrev Configuration (V : Type u) := V → ℕ
variable {V : Type u} {S : Type v} {R : Type w}
variable [Fintype V] [DecidableEq R]
def mass (x : Configuration V) : ℕ := ∑ v, x v
def bag (δ : S → V → R) (x : Configuration V) (s : S) : Multiset R :=
  ∑ v, Multiset.replicate (x v) (δ s v)

abbrev Grid (n : ℕ) := Fin n × Fin n

def natAbsDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

def manhattan {n : ℕ} (x y : Grid n) : ℕ :=
  natAbsDiff x.1.val y.1.val + natAbsDiff x.2.val y.2.val

def gridGraph (n : ℕ) : SimpleGraph (Grid n) :=
  SimpleGraph.fromRel fun x y => manhattan x y = 1

end ShellTomography

namespace ShellObservability
open ShellTomography

def ToleratesErasures {X S A : Type*}
    (code : X → S → A) (admissible : X → Prop) (e : ℕ) : Prop :=
  ∀ erased : Finset S, erased.card ≤ e →
    ∀ x y, admissible x → admissible y →
      (∀ s, s ∉ erased → code x s = code y s) → x = y

def GridSensorBounds (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, p.1 < m+2 ∧ p.2 < m+2

def gridSensorVertex (m : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S)
    (s : S) : Grid (m+2) :=
  (⟨s.val.1,(hb s.val s.property).1⟩,⟨s.val.2,(hb s.val s.property).2⟩)

noncomputable def gridSensorDistance (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (s : S) (v : Grid (m+2)) : ℕ :=
  (gridGraph (m+2)).dist (gridSensorVertex m S hb s) v

def GridRobust (m : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S) : Prop :=
  ToleratesErasures (bag (gridSensorDistance m S hb)) (fun x => mass x ≤ 2) 1

def GridIntervalCuts (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b k : ℕ, 0 < k → a+k ≤ m → b+k ≤ m →
    2 ≤ (S.filter (fun p => ¬ ((a < p.1 ∧ p.1 ≤ a+k) ↔
      (b < p.2 ∧ p.2 ≤ b+k)))).card

def GridHasCorners (m : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ({(0,0),(0,m+1),(m+1,0),(m+1,m+1)} : Finset (ℕ × ℕ)) ⊆ S

noncomputable def mixedMomentReport {V S : Type*} [Fintype V]
    (δ : S → V → ℕ) (full : S → Prop) (x : Configuration V) (s : S) :
    Multiset ℕ × ℕ := by
  classical
  exact (if full s then bag δ x s else 0, (bag δ x s).sum)

def gridFullReport (m : ℕ) (p : ℕ × ℕ) : Prop :=
  p ∈ ({(0,0),(0,m+1),(m+1,0),(m+1,m+1)} : Finset (ℕ × ℕ))

noncomputable def gridMomentReport (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) : Configuration (Grid (m+2)) → S → Multiset ℕ × ℕ :=
  mixedMomentReport (gridSensorDistance m S hb) (fun s => gridFullReport m s.val)

def GridMomentRobust (m : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S) : Prop :=
  ToleratesErasures (gridMomentReport m S hb) (fun x => mass x ≤ 2) 1

end ShellObservability

namespace ShellObservability.Hypercube

abbrev Cube (n : ℕ) := Fin n → Bool

def weight {n : ℕ} (x : Cube n) : ℕ := ∑ i, if x i then 1 else 0

def evenPrefix (n j : ℕ) : Cube n := fun i => decide (i.val < 2 * j)

def cubeGraph (n : ℕ) : SimpleGraph (Cube n) :=
  SimpleGraph.fromRel (fun x y => hammingDist x y = 1)

def oddWords (n : ℕ) : Finset (Cube n) :=
  Finset.univ.filter (fun x => weight x % 2 = 1)

def prefixSet (q : ℕ) : Finset (Cube (4*q)) :=
  (Finset.range (2*q)).image (evenPrefix (4*q))

def IsDistanceEqualizer {n : ℕ} (S : Finset (Cube n)) : Prop :=
  ∀ x, x ∉ S → ∀ y, y ∉ S → x ≠ y →
    ∃ z ∈ S, (cubeGraph n).dist z x = (cubeGraph n).dist z y

def prefixEqualizer (q : ℕ) : Finset (Cube (4*q)) := oddWords (4*q) ∪ prefixSet q

def antipode {n : ℕ} (x : Cube n) : Cube n := fun i => !x i

end ShellObservability.Hypercube

namespace ShellObservability.BishopParity

abbrev Square (N : ℕ) := Fin (N+1) × Fin (N+1)

def plus {N : ℕ} (v : Square N) : ℕ := v.1.val + v.2.val

def minus {N : ℕ} (v : Square N) : ℕ := v.1.val + (N-v.2.val)

def Adj {N : ℕ} (u v : Square N) : Prop :=
  u ≠ v ∧ (plus u = plus v ∨ minus u = minus v)

instance {N : ℕ} : DecidableRel (@Adj N) := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

def graph (N : ℕ) : SimpleGraph (Square N) where
  Adj := Adj
  symm := ⟨by intro u v h; exact ⟨Ne.symm h.1, h.2.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

instance {N : ℕ} : DecidableRel (graph N).Adj :=
  inferInstanceAs (DecidableRel Adj)

def TwoDominates {N : ℕ} (S : Finset (Square N)) : Prop :=
  ∀ v, v ∉ S → 2 ≤ (S.filter (fun u => (graph N).Adj v u)).card

end ShellObservability.BishopParity

namespace ShellObservability.Petersen

abbrev V := Fin 22

def adjacent (a b : V) : Prop :=
  if a.val < 11 then
    if b.val < 11 then b.val = (a.val+1)%11 ∨ a.val = (b.val+1)%11
    else b.val = a.val+11
  else
    if b.val < 11 then a.val = b.val+11
    else b.val-11 = (a.val-11+4)%11 ∨ a.val-11 = (b.val-11+4)%11

instance (a b : V) : Decidable (adjacent a b) := by
  unfold adjacent
  infer_instance

def load (c : V → ℕ) (v : V) : ℕ := ∑ u, if adjacent v u then c u else 0

def indicator (S : Finset V) (v : V) : ℕ := if v ∈ S then 1 else 0

def DoubleTotalDominating (S : Finset V) : Prop :=
  ∀ v, 2 ≤ load (indicator S) v

end ShellObservability.Petersen

namespace ShellObservability.PetersenSecond

abbrev V := Fin 32

def adjacent (a b : V) : Prop :=
  if a.val < 16 then
    if b.val < 16 then b.val = (a.val + 1) % 16 ∨ a.val = (b.val + 1) % 16
    else b.val = a.val + 16
  else
    if b.val < 16 then a.val = b.val + 16
    else b.val - 16 = (a.val - 16 + 5) % 16 ∨
      a.val - 16 = (b.val - 16 + 5) % 16

instance (a b : V) : Decidable (adjacent a b) := by
  unfold adjacent
  infer_instance

def load (c : V → ℕ) (v : V) : ℕ := ∑ u, if adjacent v u then c u else 0

def indicator (S : Finset V) (v : V) : ℕ := if v ∈ S then 1 else 0

def DoubleTotalDominating (S : Finset V) : Prop :=
  ∀ v, 2 ≤ load (indicator S) v

end ShellObservability.PetersenSecond

namespace ShellObservability.FractionalCounterexample

abbrev V := Fin 6

def adjacent (a b : V) : Prop :=
  (a.val, b.val) ∈ ({(0,4),(4,0),(0,5),(5,0),(1,3),(3,1),(1,4),(4,1),
    (2,3),(3,2),(2,4),(4,2),(3,4),(4,3)} : Finset (ℕ × ℕ))

instance (a b : V) : Decidable (adjacent a b) := by
  unfold adjacent
  infer_instance

def graph : SimpleGraph V where
  Adj := adjacent
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun a b =>
  inferInstanceAs (Decidable (adjacent a b))

def load (f : V → ℝ) (v : V) : ℝ :=
  ∑ u, if u.val = v.val ∨ graph.Adj v u then f u else 0

def mass (f : V → ℝ) : ℝ := ∑ v, f v

def FractionalDominating (f : V → ℝ) : Prop :=
  (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ ∀ v, 1 ≤ load f v

def FractionalPacking (f : V → ℝ) : Prop :=
  (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ ∀ v, load f v ≤ 1

def minimumFace : Set (V → ℝ) := {f | FractionalDominating f ∧
  ∀ g, FractionalDominating g → mass f ≤ mass g}

def maximumFace : Set (V → ℝ) := {f | FractionalPacking f ∧
  ∀ g, FractionalPacking g → mass g ≤ mass f}

def ClassI : Prop := (minimumFace ∩ maximumFace).Nonempty ∧
  ¬ minimumFace ⊆ maximumFace ∧ ¬ maximumFace ⊆ minimumFace

def DominationNull (v : V) : Prop := ∀ f ∈ minimumFace, f v = 0

def PackingNull (v : V) : Prop := ∀ f ∈ maximumFace, f v = 0

end ShellObservability.FractionalCounterexample

namespace PalomarResults.Grid
open ShellObservability
open ShellTomography

/-- Exact single-erasure criterion for all populations of mass at most two. -/
theorem gridRobust_iff_intervalCuts (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridRobust m S hb ↔ GridIntervalCuts m S := by
  sorry

/-- Complete bags at corners and distance sums elsewhere retain exactly the same recovery power. -/
theorem gridMomentRobust_iff_gridRobust (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hcorners : GridHasCorners m S) :
    GridMomentRobust m S hb ↔ GridRobust m S hb := by
  sorry

/-- Every robust placement satisfies the strict three-halves lower bound. -/
theorem grid_robust_sensor_lower_bound (m : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds m S) (hm : 0 < m) (hr : GridRobust m S hb) :
    3*m < 2*S.card := by
  sorry

/-- On every (m+2) by (m+2) grid with m at least one, the exact optimum among placements containing the four corners is the ceiling of (3m+9)/2. -/
theorem exact_corner_grid_robust_minimum_all (m : ℕ) (hm : 0 < m) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      S.card = (3*m+10)/2 ∧ GridHasCorners m S ∧ GridRobust m S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds m S),
      GridHasCorners m S → GridRobust m S hb → (3*m+10)/2 ≤ S.card) := by
  sorry

end PalomarResults.Grid

namespace PalomarResults.Hypercube
open ShellObservability.Hypercube

/-- For every q at least three, the published exponential-extra conjecture is strictly exceeded in efficiency. -/
theorem infinite_counterexample_family (q : ℕ) (hq : 3 ≤ q) :
    ∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧
      S.card < 2^(4*q-1) + 2^((4*q)/2-2) := by
  sorry

/-- After selecting the odd words, only the explicit antipodal covering condition remains. -/
theorem odd_union_equalizer_iff_antipodal_cover (q : ℕ) (hq : 0 < q)
    (T : Finset (Cube (4*q))) :
    IsDistanceEqualizer (oddWords (4*q) ∪ T) ↔
      ∀ x, weight x % 2 = 0 →
        x ∈ T ∨ antipode x ∈ T ∨ ∃ z ∈ T, hammingDist z x = 2*q := by
  sorry

/-- The equidistant dimension of the 4q-cube is determined up to one: an equalizer of size 2^(4q-1)+2q exists, and none has fewer than 2^(4q-1)+2q-1 vertices. -/
theorem equidistant_dimension_within_one (q : ℕ) (hq : 0 < q) :
    (∃ S : Finset (Cube (4*q)), IsDistanceEqualizer S ∧ S.card = 2^(4*q-1) + 2*q) ∧
    (∀ S : Finset (Cube (4*q)), IsDistanceEqualizer S → 2^(4*q-1) + 2*q - 1 ≤ S.card) := by
  sorry

end PalomarResults.Hypercube

namespace PalomarResults.Bishop
open ShellObservability.BishopParity

/-- For every positive even board order N+1, ordinary bishop two-domination has exact value 2(N+1). -/
theorem exact_two_domination {N : ℕ} (hN : N % 2 = 1) :
    (∃ S : Finset (Square N), TwoDominates S ∧ S.card = 2*(N+1)) ∧
    (∀ S : Finset (Square N), TwoDominates S → 2*(N+1) ≤ S.card) := by
  sorry

end PalomarResults.Bishop

namespace PalomarResults.Petersen11
open ShellObservability.Petersen

/-- The double total domination number of P(11,4) is exactly sixteen, not the conjectured fifteen. -/
theorem exact_domination :
    (∃ S : Finset V, S.card = 16 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 16 ≤ S.card) := by
  sorry

end PalomarResults.Petersen11

namespace PalomarResults.Petersen16
open ShellObservability.PetersenSecond

/-- The double total domination number of P(16,5) is exactly twenty-four, not the conjectured twenty-two. -/
theorem exact_domination :
    (∃ S : Finset V, S.card = 24 ∧ DoubleTotalDominating S) ∧
    (∀ S : Finset V, DoubleTotalDominating S → 24 ≤ S.card) := by
  sorry

end PalomarResults.Petersen16

namespace PalomarResults.Fractional
open ShellObservability.FractionalCounterexample

/-- The six-vertex fractional counterexample graph is connected. -/
theorem graph_connected : graph.Connected := by
  sorry

/-- Its optimal real-valued domination and packing faces have Class I intersection but no vertex null on both. -/
theorem counterexample : ClassI ∧ ¬ ∃ v, DominationNull v ∧ PackingNull v := by
  sorry

end PalomarResults.Fractional

namespace ShellObservability.Rectangle
open ShellTomography
abbrev Grid (w h : ℕ) := Fin w × Fin h
def manhattan {w h : ℕ} (x y : Grid w h) : ℕ :=
  natAbsDiff x.1.val y.1.val + natAbsDiff x.2.val y.2.val
def gridGraph (w h : ℕ) : SimpleGraph (Grid w h) :=
  SimpleGraph.fromRel fun x y => manhattan x y = 1
def GridSensorBounds (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ S, p.1 < M+2 ∧ p.2 < N+2
def gridSensorVertex (M N : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S)
    (s : S) : Grid (M+2) (N+2) :=
  (⟨s.val.1,(hb s.val s.property).1⟩,⟨s.val.2,(hb s.val s.property).2⟩)
noncomputable def gridSensorDistance (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (s : S) (v : Grid (M+2) (N+2)) : ℕ :=
  (gridGraph (M+2) (N+2)).dist (gridSensorVertex M N S hb s) v
def GridRobust (M N : ℕ) (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S) : Prop :=
  ToleratesErasures (bag (gridSensorDistance M N S hb)) (fun x => mass x ≤ 2) 1
def GridIntervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ∀ a b k : ℕ, 0 < k → a+k ≤ M → b+k ≤ N →
    2 ≤ (S.filter (fun p => ¬ ((a < p.1 ∧ p.1 ≤ a+k) ↔
      (b < p.2 ∧ p.2 ≤ b+k)))).card
def GridHasCorners (M N : ℕ) (S : Finset (ℕ × ℕ)) : Prop :=
  ({(0,0),(0,N+1),(M+1,0),(M+1,N+1)} : Finset (ℕ × ℕ)) ⊆ S
end ShellObservability.Rectangle

namespace PalomarResults.Rectangle
open ShellObservability.Rectangle
theorem gridRobust_iff_intervalCuts (M N : ℕ) (S : Finset (ℕ × ℕ))
    (hb : GridSensorBounds M N S) (hcorners : GridHasCorners M N S) :
    GridRobust M N S hb ↔ GridIntervalCuts M N S := by sorry

theorem exact_long_rectangle_robust_minimum (M N : ℕ)
    (hsize : N ≤ M) (hratio : 5*N ≤ 3*M) :
    (∃ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      S.card = 2*N+4 ∧ GridHasCorners M N S ∧ GridRobust M N S hb) ∧
    (∀ (S : Finset (ℕ × ℕ)) (hb : GridSensorBounds M N S),
      GridHasCorners M N S → GridRobust M N S hb → 2*N+4 ≤ S.card) := by sorry
end PalomarResults.Rectangle

-- Append to the Mathlib-only Challenge, before the three wrappers below.
-- Exact explicit models; no moment-range or trade-volume bridge is assumed.
