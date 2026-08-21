/-
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import RegularPathDelay
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
Implementation module for the post-paper Palomar upgrade. When integrated,
install this file as `RegularPathDelayEnumeration.lean`.

The search procedure below is an ordered, oracle-pruned DFS over actual
vertex-regular directed paths.  Its oracle is specified by regular reachability
in the prefix-deleted instance, not by membership in a supplied output list.
The charged delay statements count frame setups and exact-oracle calls.  They
do not formalize the Goldberg--Karzanov implementation or executable running
time; the paper's cited linear-time oracle is the external complexity input.
-/

namespace RegularPathDelay

/-- Finite skew-symmetric path instance with deterministic adjacency order. -/
structure FiniteRegularPathInstance (α : Type) [DecidableEq α] [Fintype α] where
  edge : α → α → Bool
  bar : α → α
  bar_involutive : ∀ x, bar (bar x) = x
  bar_fixedPointFree : ∀ x, bar x ≠ x
  edge_skew : ∀ u v, edge u v = edge (bar v) (bar u)
  loopless : ∀ v, edge v v = false
  successors : α → List α
  successors_nodup : ∀ v, (successors v).Nodup
  mem_successors_iff : ∀ v w, w ∈ successors v ↔ edge v w = true
  outBound : Nat
  successors_length_le : ∀ v, (successors v).length ≤ outBound
  source : α
  target : α

variable {α : Type} [DecidableEq α] [Fintype α]

/-- The propositional edge relation represented by the Boolean adjacency data. -/
def FiniteRegularPathInstance.Edge (I : FiniteRegularPathInstance α) (u v : α) : Prop :=
  I.edge u v = true

/-- A nonempty directed vertex-regular path from `a` to `b`.  Simplicity is
included in `Regular`, since compatibility entails inequality. -/
def IsRegularPathFromTo (I : FiniteRegularPathInstance α)
    (a b : α) (xs : List α) : Prop :=
  xs.head? = some a ∧
  xs.getLast? = some b ∧
  Walk I.Edge xs ∧
  Regular I.bar xs

/-- The fixed-endpoint outputs of the paper's enumeration problem. -/
def IsTargetRegularPath (I : FiniteRegularPathInstance α) (xs : List α) : Prop :=
  IsRegularPathFromTo I I.source I.target xs

/-- Invariant carried by every recursive frame. -/
def IsRegularPrefix (I : FiniteRegularPathInstance α) (pfx : List α) : Prop :=
  pfx.head? = some I.source ∧ Walk I.Edge pfx ∧ Regular I.bar pfx

omit [DecidableEq α] [Fintype α] in
theorem regular_nodup {bar : α → α} {xs : List α}
    (hregular : Regular bar xs) : xs.Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.nodup_cons]
      rw [Regular, List.pairwise_cons] at hregular
      exact ⟨fun hx => (hregular.1 x hx).1 rfl, ih hregular.2⟩

omit [DecidableEq α] [Fintype α] in
theorem regular_append_singleton_of_survives
    {bar : α → α} (hinvol : ∀ x, bar (bar x) = x)
    {old : List α} {y : α}
    (hold : Regular bar old) (hy : Survives bar old y) :
    Regular bar (old ++ [y]) := by
  apply List.pairwise_append.mpr
  refine ⟨hold, ?_, ?_⟩
  · simp
  · intro x hx z hz
    simp only [List.mem_singleton] at hz
    subst z
    exact compatible_of_survives hinvol hx hy

omit [DecidableEq α] [Fintype α] in
theorem walk_append_cons_iff
    {edge : α → α → Prop} {pfx tail : List α} {v w : α}
    (hlast : pfx.getLast? = some v) :
    Walk edge (pfx ++ w :: tail) ↔
      Walk edge pfx ∧ edge v w ∧ Walk edge (w :: tail) := by
  induction pfx with
  | nil => simp at hlast
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst v
          simp [Walk]
      | cons y ys =>
          have htail : (y :: ys).getLast? = some v := by
            simpa using hlast
          simp only [List.cons_append, Walk]
          constructor
          · rintro ⟨hxy, hrest⟩
            rcases (ih htail).1 hrest with ⟨hwalk, hedge, hsuffix⟩
            exact ⟨⟨hxy, hwalk⟩, hedge, hsuffix⟩
          · rintro ⟨⟨hxy, hwalk⟩, hedge, hsuffix⟩
            exact ⟨hxy, (ih htail).2 ⟨hwalk, hedge, hsuffix⟩⟩

omit [DecidableEq α] [Fintype α] in
theorem head?_append_of_some {pfx suffix : List α} {a : α}
    (hhead : pfx.head? = some a) :
    (pfx ++ suffix).head? = some a := by
  have hne : pfx ≠ [] := by
    intro hnil
    simp [hnil] at hhead
  rw [List.head?_append_of_ne_nil pfx hne]
  exact hhead

omit [DecidableEq α] [Fintype α] in
theorem survives_first_suffix_of_regular_join
    {bar : α → α} (hinvol : ∀ x, bar (bar x) = x)
    {old tail : List α} {y : α}
    (hregular : Regular bar (old ++ y :: tail)) :
    Survives bar old y := by
  rcases List.pairwise_append.mp hregular with ⟨_, _, hcross⟩
  constructor
  · intro hy
    exact (hcross y hy y (by simp)).1 rfl
  · intro hbar
    exact (hcross (bar y) hbar y (by simp)).2.1 (hinvol y)

/-- Ordered admissible successors: graph out-neighbors surviving deletion of
the current prefix and all of its complementary vertices. -/
def orderedAdmissibleSuccessors (I : FiniteRegularPathInstance α)
    (pfx : List α) : List α :=
  match pfx.getLast? with
  | none => []
  | some v => (I.successors v).filter
      (fun w => decide (w ∉ pfx ∧ I.bar w ∉ pfx))

/-- Exact regular-reachability meaning of one completion query in the induced
instance `G - (V(P) ∪ bar(V(P)))`. -/
def DeletedCompletion (I : FiniteRegularPathInstance α)
    (old : List α) (w : α) : Prop :=
  ∃ tail : List α,
    IsRegularPathFromTo I w I.target (w :: tail) ∧
    Survives I.bar old w ∧
    SuffixSurvives I.bar old tail

/-- A full target path obtained by appending `w` and a suffix to this frame. -/
def HasRegularExtension (I : FiniteRegularPathInstance α)
    (pfx : List α) (w : α) : Prop :=
  ∃ tail : List α, IsTargetRegularPath I (pfx ++ w :: tail)

/-- The exact Boolean reachability oracle.  Goldberg--Karzanov supplies the
external linear-time implementation used by the paper; Lean assumes only this
semantic equivalence. -/
structure ExactReachabilityOracle (I : FiniteRegularPathInstance α) where
  query : List α → α → Bool
  correct : ∀ pfx w, query pfx w = true ↔ DeletedCompletion I pfx w

/-- Paper Lemma 3 at the list level.  Its reverse direction is obtained from
`regular_join_iff`, so accepted reachability witnesses are joined to the
existing regularity/deletion theorem rather than to an arbitrary output list. -/
theorem prefix_extension_iff_deleted_completion
    (I : FiniteRegularPathInstance α) {pfx : List α} {v w : α}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hedge : I.Edge v w)
    (hsurvives : Survives I.bar pfx w) :
    HasRegularExtension I pfx w ↔ DeletedCompletion I pfx w := by
  rcases hpfx with ⟨hsource, hpfxWalk, hpfxRegular⟩
  constructor
  · rintro ⟨tail, hfull⟩
    rcases hfull with ⟨_, htarget, hfullWalk, hfullRegular⟩
    have hjoin :=
      (regular_join_iff I.bar_involutive pfx tail w).1 hfullRegular
    refine ⟨tail, ?_, hsurvives, hjoin.2.2⟩
    refine ⟨by simp, ?_, ?_, hjoin.2.1⟩
    · simpa only [List.getLast?_append_cons] using htarget
    · exact ((walk_append_cons_iff hlast).1 hfullWalk).2.2
  · rintro ⟨tail, hsuffix, hw, htailSurvives⟩
    rcases hsuffix with ⟨_, htarget, hsuffixWalk, hsuffixRegular⟩
    refine ⟨tail, ?_⟩
    refine ⟨head?_append_of_some hsource, ?_, ?_, ?_⟩
    · simpa only [List.getLast?_append_cons] using htarget
    · exact (walk_append_cons_iff hlast).2
        ⟨hpfxWalk, hedge, hsuffixWalk⟩
    · exact (regular_join_iff I.bar_involutive pfx tail w).2
        ⟨regular_append_singleton_of_survives I.bar_involutive hpfxRegular hw,
          hsuffixRegular, htailSurvives⟩

/-- Positive oracle answers are exactly the viable graph/path children. -/
theorem oracle_accepts_iff_regular_extension
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    {pfx : List α} {v w : α}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hw : w ∈ orderedAdmissibleSuccessors I pfx) :
    oracle.query pfx w = true ↔ HasRegularExtension I pfx w := by
  have hw' : w ∈ (I.successors v).filter
      (fun z => decide (z ∉ pfx ∧ I.bar z ∉ pfx)) := by
    simpa [orderedAdmissibleSuccessors, hlast] using hw
  have hsucc : w ∈ I.successors v := List.mem_of_mem_filter hw'
  have hsurvives : Survives I.bar pfx w := by
    simpa [Survives] using List.of_mem_filter hw'
  rw [oracle.correct]
  exact (prefix_extension_iff_deleted_completion I hpfx hlast
    ((I.mem_successors_iff v w).1 hsucc) hsurvives).symm

/-- Oracle-positive children in the fixed adjacency order. -/
def acceptedSuccessors (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) (pfx : List α) : List α :=
  (orderedAdmissibleSuccessors I pfx).filter
    (fun w => oracle.query pfx w = true)

theorem mem_orderedAdmissibleSuccessors_iff
    (I : FiniteRegularPathInstance α) {pfx : List α} {v w : α}
    (hlast : pfx.getLast? = some v) :
    w ∈ orderedAdmissibleSuccessors I pfx ↔
      I.Edge v w ∧ Survives I.bar pfx w := by
  simp [orderedAdmissibleSuccessors, hlast, I.mem_successors_iff,
    FiniteRegularPathInstance.Edge, Survives, and_left_comm]

theorem mem_acceptedSuccessors_iff
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    {pfx : List α} {w : α} :
    w ∈ acceptedSuccessors I oracle pfx ↔
      w ∈ orderedAdmissibleSuccessors I pfx ∧
        oracle.query pfx w = true := by
  simp [acceptedSuccessors]

theorem orderedAdmissibleSuccessors_nodup
    (I : FiniteRegularPathInstance α) (pfx : List α) :
    (orderedAdmissibleSuccessors I pfx).Nodup := by
  cases hlast : pfx.getLast? with
  | none => simp [orderedAdmissibleSuccessors, hlast]
  | some v =>
      simpa [orderedAdmissibleSuccessors, hlast] using
        (I.successors_nodup v).filter
          (fun w => decide (w ∉ pfx ∧ I.bar w ∉ pfx))

/-- One query is made for each ordered admissible successor, hence no more
than the declared adjacency bound. -/
theorem orderedAdmissibleSuccessors_length_le
    (I : FiniteRegularPathInstance α) (pfx : List α) :
    (orderedAdmissibleSuccessors I pfx).length ≤ I.outBound := by
  cases hlast : pfx.getLast? with
  | none => simp [orderedAdmissibleSuccessors, hlast]
  | some v =>
      have hfilter : ((I.successors v).filter
          (fun w => decide (w ∉ pfx ∧ I.bar w ∉ pfx))).length ≤
          (I.successors v).length :=
        List.Sublist.length_le List.filter_sublist
      simpa [orderedAdmissibleSuccessors, hlast] using
        Nat.le_trans hfilter (I.successors_length_le v)

theorem acceptedSuccessors_nodup
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (pfx : List α) :
    (acceptedSuccessors I oracle pfx).Nodup := by
  exact (orderedAdmissibleSuccessors_nodup I pfx).filter
    (fun w => oracle.query pfx w = true)

theorem regularPrefix_append_of_accepted
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    {pfx : List α} {v w : α}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hw : w ∈ acceptedSuccessors I oracle pfx) :
    IsRegularPrefix I (pfx ++ [w]) := by
  have hordered := (mem_acceptedSuccessors_iff I oracle).1 hw |>.1
  rcases (mem_orderedAdmissibleSuccessors_iff I hlast).1 hordered with
    ⟨hedge, hsurvives⟩
  rcases hpfx with ⟨hsource, hpfxWalk, hpfxRegular⟩
  refine ⟨head?_append_of_some hsource, ?_, ?_⟩
  · exact (walk_append_cons_iff (tail := []) hlast).2
      ⟨hpfxWalk, hedge, by simp [Walk]⟩
  · exact regular_append_singleton_of_survives
      I.bar_involutive hpfxRegular hsurvives

theorem targetPath_of_regularPrefix
    (I : FiniteRegularPathInstance α) {pfx : List α}
    (hpfx : IsRegularPrefix I pfx)
    (htarget : pfx.getLast? = some I.target) :
    IsTargetRegularPath I pfx :=
  ⟨hpfx.1, htarget, hpfx.2.1, hpfx.2.2⟩

/-- Bounded-fuel ordered DFS.  It outputs at the target and otherwise explores
exact-positive children in deterministic adjacency order. -/
def enumerateAux (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) : Nat → List α → List (List α)
  | 0, pfx => if pfx.getLast? = some I.target then [pfx] else []
  | fuel + 1, pfx =>
      if pfx.getLast? = some I.target then [pfx]
      else (acceptedSuccessors I oracle pfx).flatMap
        (fun w => enumerateAux I oracle fuel (pfx ++ [w]))

/-- The paper's initial call `Enumerate((s))`; `card α` is a safe recursion
depth because every regular path is duplicate-free. -/
def enumerateRegularPaths (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) : List (List α) :=
  enumerateAux I oracle (Fintype.card α) [I.source]

theorem enumerateAux_sound
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx, IsRegularPrefix I pfx →
      ∀ p ∈ enumerateAux I oracle fuel pfx, IsTargetRegularPath I p := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx hpfx p hp
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget] at hp
        subst p
        exact targetPath_of_regularPrefix I hpfx htarget
      · simp [enumerateAux, htarget] at hp
  | succ fuel ih =>
      intro pfx hpfx p hp
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget] at hp
        subst p
        exact targetPath_of_regularPrefix I hpfx htarget
      · simp only [enumerateAux, if_neg htarget, List.mem_flatMap] at hp
        rcases hp with ⟨w, hw, hp⟩
        have hpfxNe : pfx ≠ [] := by
          intro hnil
          simp [IsRegularPrefix, hnil] at hpfx
        let v := pfx.getLast hpfxNe
        have hlast : pfx.getLast? = some v :=
          List.getLast?_eq_getLast_of_ne_nil hpfxNe
        exact ih (pfx ++ [w])
          (regularPrefix_append_of_accepted I oracle hpfx hlast hw) p hp

theorem enumerateAux_complete_extension
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx rest,
      IsRegularPrefix I pfx →
      IsTargetRegularPath I (pfx ++ rest) →
      rest.length ≤ fuel →
      pfx ++ rest ∈ enumerateAux I oracle fuel pfx := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx rest hpfx hfull hlength
      have hrest : rest = [] :=
        List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlength)
      subst rest
      have htarget : pfx.getLast? = some I.target := by
        simpa using hfull.2.1
      simp [enumerateAux, htarget]
  | succ fuel ih =>
      intro pfx rest hpfx hfull hlength
      cases rest with
      | nil =>
          have htarget : pfx.getLast? = some I.target := by
            simpa using hfull.2.1
          simp [enumerateAux, htarget]
      | cons w tail =>
          have hpfxNe : pfx ≠ [] := by
            intro hnil
            simp [IsRegularPrefix, hnil] at hpfx
          let v := pfx.getLast hpfxNe
          have hlast : pfx.getLast? = some v :=
            List.getLast?_eq_getLast_of_ne_nil hpfxNe
          have hnotTarget : pfx.getLast? ≠ some I.target := by
            intro htarget
            have hvTarget : v = I.target := by
              rw [hlast] at htarget
              exact Option.some.inj htarget
            have htargetOld : I.target ∈ pfx := by
              have hvMem : v ∈ pfx := List.getLast_mem hpfxNe
              rw [hvTarget] at hvMem
              exact hvMem
            have hsuffixLast : (w :: tail).getLast? = some I.target := by
              simpa only [List.getLast?_append_cons] using hfull.2.1
            have htargetSuffix : I.target ∈ w :: tail :=
              List.mem_of_mem_getLast? (by simp [hsuffixLast])
            rcases List.pairwise_append.mp hfull.2.2.2 with
              ⟨_, _, hcross⟩
            exact (hcross I.target htargetOld I.target htargetSuffix).1 rfl
          have hedge : I.Edge v w :=
            ((walk_append_cons_iff (tail := tail) hlast).1 hfull.2.2.1).2.1
          have hsurvives : Survives I.bar pfx w :=
            survives_first_suffix_of_regular_join I.bar_involutive hfull.2.2.2
          have hordered : w ∈ orderedAdmissibleSuccessors I pfx :=
            (mem_orderedAdmissibleSuccessors_iff I hlast).2
              ⟨hedge, hsurvives⟩
          have hextension : HasRegularExtension I pfx w :=
            ⟨tail, hfull⟩
          have hquery : oracle.query pfx w = true :=
            (oracle_accepts_iff_regular_extension I oracle hpfx hlast hordered).2
              hextension
          have haccepted : w ∈ acceptedSuccessors I oracle pfx :=
            (mem_acceptedSuccessors_iff I oracle).2 ⟨hordered, hquery⟩
          have hchildPrefix : IsRegularPrefix I (pfx ++ [w]) :=
            regularPrefix_append_of_accepted I oracle hpfx hlast haccepted
          have hchildTarget :
              IsTargetRegularPath I ((pfx ++ [w]) ++ tail) := by
            simpa [List.append_assoc] using hfull
          have htailLength : tail.length ≤ fuel := by
            simpa using hlength
          simp only [enumerateAux, if_neg hnotTarget, List.mem_flatMap]
          refine ⟨w, haccepted, ?_⟩
          simpa [List.append_assoc] using
            ih (pfx ++ [w]) tail hchildPrefix hchildTarget htailLength

theorem enumerateAux_output_prefix
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx p, p ∈ enumerateAux I oracle fuel pfx → pfx <+: p := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx p hp
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget] at hp
        subst p
        exact List.prefix_refl pfx
      · simp [enumerateAux, htarget] at hp
  | succ fuel ih =>
      intro pfx p hp
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget] at hp
        subst p
        exact List.prefix_refl pfx
      · simp only [enumerateAux, if_neg htarget, List.mem_flatMap] at hp
        rcases hp with ⟨w, _, hp⟩
        exact (pfx.prefix_append [w]).trans (ih (pfx ++ [w]) p hp)

theorem enumerateAux_nodup
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx, (enumerateAux I oracle fuel pfx).Nodup := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget]
      · simp [enumerateAux, htarget]
  | succ fuel ih =>
      intro pfx
      by_cases htarget : pfx.getLast? = some I.target
      · simp [enumerateAux, htarget]
      · simp only [enumerateAux, if_neg htarget]
        apply List.nodup_flatMap.mpr
        constructor
        · intro w _
          exact ih (pfx ++ [w])
        · apply (acceptedSuccessors_nodup I oracle pfx).imp
          intro w₁ w₂ hne
          apply List.disjoint_left.mpr
          intro p hp₁ hp₂
          have hprefix₁ : pfx ++ [w₁] <+: p :=
            enumerateAux_output_prefix I oracle fuel (pfx ++ [w₁]) p hp₁
          have hprefix₂ : pfx ++ [w₂] <+: p :=
            enumerateAux_output_prefix I oracle fuel (pfx ++ [w₂]) p hp₂
          have heq : pfx ++ [w₁] = pfx ++ [w₂] :=
            equal_prefixes_of_equal_length hprefix₁ hprefix₂ (by simp)
          have : [w₁] = [w₂] := List.append_right_injective pfx heq
          exact hne (by simpa using this)

/-- Every emitted list is an actual directed vertex-regular fixed-endpoint path. -/
theorem enumerateRegularPaths_sound
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ p ∈ enumerateRegularPaths I oracle, IsTargetRegularPath I p := by
  apply enumerateAux_sound I oracle (Fintype.card α) [I.source]
  simp [IsRegularPrefix, Walk, Regular]

/-- Every fixed-endpoint vertex-regular path follows its unique chain of
exact-positive prefixes and is emitted by the DFS. -/
theorem enumerateRegularPaths_complete
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ p, IsTargetRegularPath I p → p ∈ enumerateRegularPaths I oracle := by
  intro p hp
  cases p with
  | nil => simp [IsTargetRegularPath, IsRegularPathFromTo] at hp
  | cons a tail =>
      have ha : a = I.source := by
        simpa [IsTargetRegularPath, IsRegularPathFromTo] using hp.1
      subst a
      have hlength : tail.length ≤ Fintype.card α := by
        have hfullLength : (I.source :: tail).length ≤ Fintype.card α :=
          (regular_nodup hp.2.2.2).length_le_card
        exact Nat.le_trans (Nat.le_succ tail.length) hfullLength
      exact enumerateAux_complete_extension I oracle
        (Fintype.card α) [I.source] tail
        (by simp [IsRegularPrefix, Walk, Regular])
        (by simpa using hp) hlength

/-- Unique prefix chains and duplicate-free ordered successor lists ensure
that no path is emitted twice. -/
theorem enumerateRegularPaths_nodup
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    (enumerateRegularPaths I oracle).Nodup := by
  exact enumerateAux_nodup I oracle (Fintype.card α) [I.source]

/-- Regularity bounds every output, hence every emitting recursion branch, by
the number of vertices.  The bounded-fuel definition gives termination. -/
theorem enumerateRegularPaths_depth_le
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ p ∈ enumerateRegularPaths I oracle, p.length ≤ Fintype.card α := by
  intro p hp
  exact (regular_nodup ((enumerateRegularPaths_sound I oracle p hp).2.2.2)).length_le_card

/-- Length of the longest common prefix of two DFS outputs. -/
def commonPrefixLength : List α → List α → Nat
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLength xs ys else 0
  | _, _ => 0

/-- Number of old frames resumed and new frames entered on the unique
retreat/descent between two consecutive DFS output leaves. -/
def dfsFrameTransitions (p q : List α) : Nat :=
  (p.length - commonPrefixLength p q) +
    (q.length - commonPrefixLength p q)

/-- One full frame charge consists of one setup plus at most `outBound` exact
reachability-oracle calls. -/
def dfsGapFrameWork (I : FiniteRegularPathInstance α) (p q : List α) : Nat :=
  dfsFrameTransitions p q * (I.outBound + 1)

/-- Exact per-frame combinatorial charge: one setup plus the number of exact
completion queries executed by the filtering scan. -/
def dfsFrameOracleWork (I : FiniteRegularPathInstance α)
    (pfx : List α) : Nat :=
  (orderedAdmissibleSuccessors I pfx).length + 1

theorem dfsFrameOracleWork_le
    (I : FiniteRegularPathInstance α) (pfx : List α) :
    dfsFrameOracleWork I pfx ≤ I.outBound + 1 := by
  exact Nat.add_le_add_right (orderedAdmissibleSuccessors_length_le I pfx) 1

/-- Adjacency of two values in an output list. -/
def ConsecutiveIn (p q : List α) (outputs : List (List α)) : Prop :=
  ∃ before after, outputs = before ++ p :: q :: after

/-- Concrete inter-output oracle/frame certificate.  Under exact pruning every
entered child is productive, so a consecutive-output interval consists only of
retreat along the first path and descent along the second.  The theorem counts
those frame charges; multiplying an oracle call by the externally cited
`O(n+m)` implementation cost yields the paper's polynomial-delay bound. -/
theorem consecutive_outputs_frame_work_le
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    {p q : List α}
    (hconsecutive : ConsecutiveIn p q (enumerateRegularPaths I oracle)) :
    dfsGapFrameWork I p q ≤
      2 * Fintype.card α * (I.outBound + 1) := by
  rcases hconsecutive with ⟨before, after, houtputs⟩
  have hp : p ∈ enumerateRegularPaths I oracle := by
    rw [houtputs]
    simp
  have hq : q ∈ enumerateRegularPaths I oracle := by
    rw [houtputs]
    simp
  have hpLength := enumerateRegularPaths_depth_le I oracle p hp
  have hqLength := enumerateRegularPaths_depth_le I oracle q hq
  have htransitions : dfsFrameTransitions p q ≤ p.length + q.length := by
    unfold dfsFrameTransitions
    exact Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _)
  unfold dfsGapFrameWork
  calc
    dfsFrameTransitions p q * (I.outBound + 1) ≤
        (p.length + q.length) * (I.outBound + 1) :=
      Nat.mul_le_mul_right (I.outBound + 1) htransitions
    _ ≤ (Fintype.card α + Fintype.card α) * (I.outBound + 1) :=
      Nat.mul_le_mul_right (I.outBound + 1)
        (Nat.add_le_add hpLength hqLength)
    _ = 2 * Fintype.card α * (I.outBound + 1) := by ring

/-- The analogous frame-work accounts before the first output and after the
last output use at most one root-to-leaf or leaf-to-root chain. -/
theorem endpoint_frame_work_le
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    {p : List α} (hp : p ∈ enumerateRegularPaths I oracle) :
    p.length * (I.outBound + 1) ≤
      Fintype.card α * (I.outBound + 1) := by
  exact Nat.mul_le_mul_right (I.outBound + 1)
    (enumerateRegularPaths_depth_le I oracle p hp)

/-- Bundled exact specification of the ordered fixed-endpoint enumerator. -/
theorem enumerateRegularPaths_specification
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    (∀ p, p ∈ enumerateRegularPaths I oracle ↔ IsTargetRegularPath I p) ∧
    (enumerateRegularPaths I oracle).Nodup ∧
    (∀ p ∈ enumerateRegularPaths I oracle,
      p.length ≤ Fintype.card α) := by
  constructor
  · intro p
    exact ⟨enumerateRegularPaths_sound I oracle p,
      enumerateRegularPaths_complete I oracle p⟩
  exact ⟨enumerateRegularPaths_nodup I oracle,
    enumerateRegularPaths_depth_le I oracle⟩

/-- Bundled combinatorial polynomial-delay certificate.  A full frame makes
at most `outBound` exact-oracle calls plus one setup; between consecutive
outputs at most two depth chains are charged, and each endpoint interval uses
one.  The external linear-time oracle turns this unit bound into the paper's
`O(n(Δ+1)(n+m))` delay estimate. -/
theorem polynomial_delay_frame_certificate
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    (∀ pfx, dfsFrameOracleWork I pfx ≤ I.outBound + 1) ∧
    (∀ p q, ConsecutiveIn p q (enumerateRegularPaths I oracle) →
      dfsGapFrameWork I p q ≤
        2 * Fintype.card α * (I.outBound + 1)) ∧
    (∀ p, p ∈ enumerateRegularPaths I oracle →
      p.length * (I.outBound + 1) ≤
        Fintype.card α * (I.outBound + 1)) := by
  exact ⟨dfsFrameOracleWork_le I,
    fun _ _ => consecutive_outputs_frame_work_le I oracle,
    fun _ => endpoint_frame_work_le I oracle⟩

#print axioms prefix_extension_iff_deleted_completion
#print axioms oracle_accepts_iff_regular_extension
#print axioms enumerateRegularPaths_specification
#print axioms polynomial_delay_frame_certificate

end RegularPathDelay
