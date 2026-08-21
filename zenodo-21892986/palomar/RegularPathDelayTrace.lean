/-
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
-/

import RegularPathDelayEnumeration
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
An explicit event trace for the ordered, exact-oracle-pruned DFS.

Unlike `acceptedSuccessors`, which is extensionally convenient because it
filters the complete successor list before `flatMap`, `dfsTrace` records the
paper's streaming execution order: query one admissible successor, recurse
immediately after a positive answer, resume the saved frame, and continue its
scan.  `outputsOfTrace_dfsTrace` proves that this operational presentation has
exactly the same output list as `enumerateAux`.
-/

namespace RegularPathDelay

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Observable events of the depth-first evaluator. -/
inductive DfsEvent (α : Type) where
  /-- A recursive frame is entered and its induced-instance setup begins. -/
  | enter (pfx : List α)
  /-- One admissible successor is submitted to the exact completion oracle. -/
  | query (pfx : List α) (w : α) (answer : Bool)
  /-- A completed child returns control to its saved parent scan. -/
  | resume (pfx : List α)
  /-- A target path is emitted. -/
  | output (path : List α)
  /-- The frame has terminated and returns to its caller (or halts at root). -/
  | exit (pfx : List α)
deriving DecidableEq

/-- The output projection of an event stream. -/
def outputsOfTrace : List (DfsEvent α) → List (List α) :=
  List.filterMap fun
    | .output p => some p
    | _ => none

/-- Query-or-frame work events.  Output and exit markers delimit intervals but
carry no unit of the paper's charged successor-scan work. -/
def DfsEvent.isWork : DfsEvent α → Bool
  | .enter _ | .query _ _ _ | .resume _ => true
  | .output _ | .exit _ => false

/-- Number of query/frame work events in a concrete trace segment. -/
def traceWork (events : List (DfsEvent α)) : Nat :=
  (events.filter DfsEvent.isWork).length

/-- Events produced while scanning the remaining ordered admissible successors
of one already-entered frame. -/
def scanTrace (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) (fuel : Nat) (pfx : List α)
    (childTrace : α → List (DfsEvent α)) : List α → List (DfsEvent α)
  | [] => []
  | w :: ws =>
      let answer := oracle.query pfx w
      .query pfx w answer ::
        if answer then
          childTrace w ++ .resume pfx :: scanTrace I oracle fuel pfx childTrace ws
        else
          scanTrace I oracle fuel pfx childTrace ws

/-- Explicit streaming DFS trace.  Fuel zero still recognizes a target frame,
matching `enumerateAux`; a nontarget fuel-zero frame terminates without a scan. -/
def dfsTrace (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) : Nat → List α → List (DfsEvent α) :=
  Nat.rec
    (fun pfx => .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx] else []) ++ [.exit pfx])
    (fun fuel child pfx => .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx]
       else scanTrace I oracle fuel pfx (fun w => child (pfx ++ [w]))
         (orderedAdmissibleSuccessors I pfx)) ++ [.exit pfx])

@[simp] theorem dfsTrace_zero
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (pfx : List α) :
    dfsTrace I oracle 0 pfx = .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx] else []) ++ [.exit pfx] := rfl

@[simp] theorem dfsTrace_succ
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) :
    dfsTrace I oracle (fuel + 1) pfx = .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx]
       else scanTrace I oracle fuel pfx
         (fun w => dfsTrace I oracle fuel (pfx ++ [w]))
         (orderedAdmissibleSuccessors I pfx)) ++ [.exit pfx] := rfl

/-- Full event trace of the paper's initial call. -/
def enumerateRegularPathsTrace (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) : List (DfsEvent α) :=
  dfsTrace I oracle (Fintype.card α) [I.source]

@[simp] theorem outputsOfTrace_nil :
    outputsOfTrace ([] : List (DfsEvent α)) = [] := rfl

@[simp] theorem outputsOfTrace_cons_enter (pfx : List α) (events : List (DfsEvent α)) :
    outputsOfTrace (.enter pfx :: events) = outputsOfTrace events := rfl

@[simp] theorem outputsOfTrace_cons_query
    (pfx : List α) (w : α) (answer : Bool) (events : List (DfsEvent α)) :
    outputsOfTrace (.query pfx w answer :: events) = outputsOfTrace events := rfl

@[simp] theorem outputsOfTrace_cons_resume (pfx : List α) (events : List (DfsEvent α)) :
    outputsOfTrace (.resume pfx :: events) = outputsOfTrace events := rfl

@[simp] theorem outputsOfTrace_cons_output (p : List α) (events : List (DfsEvent α)) :
    outputsOfTrace (.output p :: events) = p :: outputsOfTrace events := rfl

@[simp] theorem outputsOfTrace_cons_exit (pfx : List α) (events : List (DfsEvent α)) :
    outputsOfTrace (.exit pfx :: events) = outputsOfTrace events := rfl

@[simp] theorem outputsOfTrace_append (xs ys : List (DfsEvent α)) :
    outputsOfTrace (xs ++ ys) = outputsOfTrace xs ++ outputsOfTrace ys := by
  induction xs with
  | nil => rfl
  | cons e xs ih =>
      cases e <;> simp [outputsOfTrace]

/-- Output projection of a streaming scan: false queries contribute no output,
and a true query contributes precisely the child's output projection. -/
theorem outputsOfTrace_scanTrace
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) (childTrace : α → List (DfsEvent α))
    (ws : List α) :
    outputsOfTrace (scanTrace I oracle fuel pfx childTrace ws) =
      ws.flatMap (fun w =>
        if oracle.query pfx w then outputsOfTrace (childTrace w) else []) := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [scanTrace, List.flatMap_cons]
      by_cases hq : oracle.query pfx w = true
      · simp [hq, ih]
      · have hfalse : oracle.query pfx w = false := Bool.eq_false_of_not_eq_true hq
        simp [hfalse, ih]

theorem ordered_true_flatMap_eq_accepted
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (pfx : List α) (f : α → List (List α)) :
    (orderedAdmissibleSuccessors I pfx).flatMap
        (fun w => if oracle.query pfx w then f w else []) =
      (acceptedSuccessors I oracle pfx).flatMap f := by
  unfold acceptedSuccessors
  induction orderedAdmissibleSuccessors I pfx with
  | nil => rfl
  | cons w ws ih =>
      by_cases hq : oracle.query pfx w = true
      · simp [hq, ih]
      · have hfalse : oracle.query pfx w = false := Bool.eq_false_of_not_eq_true hq
        simp [hfalse, ih]

/-- The executable event trace has exactly the extensional output list of the
original bounded DFS. -/
theorem outputsOfTrace_dfsTrace
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx,
      outputsOfTrace (dfsTrace I oracle fuel pfx) =
        enumerateAux I oracle fuel pfx := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx
      by_cases htarget : pfx.getLast? = some I.target
      · simp [dfsTrace, enumerateAux, htarget]
      · simp [dfsTrace, enumerateAux, htarget]
  | succ fuel ih =>
      intro pfx
      by_cases htarget : pfx.getLast? = some I.target
      · simp [dfsTrace, enumerateAux, htarget]
      · simp only [dfsTrace_succ, enumerateAux, if_neg htarget,
          outputsOfTrace_cons_enter, outputsOfTrace_append,
          outputsOfTrace_cons_exit, outputsOfTrace_nil, List.append_nil]
        rw [outputsOfTrace_scanTrace]
        simp_rw [ih]
        exact ordered_true_flatMap_eq_accepted I oracle pfx
          (fun w => enumerateAux I oracle fuel (pfx ++ [w]))

theorem outputsOfTrace_enumerateRegularPathsTrace
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    outputsOfTrace (enumerateRegularPathsTrace I oracle) =
      enumerateRegularPaths I oracle := by
  exact outputsOfTrace_dfsTrace I oracle (Fintype.card α) [I.source]

/-! ## Exact interval predicates over the event stream -/

/-- A trace prefix ending immediately before its first output event. -/
def FirstOutputInterval (p : List α) (events initial : List (DfsEvent α)) : Prop :=
  ∃ suffix, events = initial ++ .output p :: suffix ∧ outputsOfTrace initial = []

/-- The exact event segment strictly between two consecutive output events. -/
def ConsecutiveOutputInterval
    (p q : List α) (events gap : List (DfsEvent α)) : Prop :=
  ∃ before after,
    events = before ++ .output p :: gap ++ .output q :: after ∧
    outputsOfTrace gap = []

/-- A trace suffix beginning immediately after its last output event. -/
def LastOutputInterval (p : List α) (events suffix : List (DfsEvent α)) : Prop :=
  ∃ before, events = before ++ .output p :: suffix ∧ outputsOfTrace suffix = []

/-- The complete terminating run has no output event. -/
def NoOutputRun (events : List (DfsEvent α)) : Prop :=
  outputsOfTrace events = []

/-! ## An exact work profile extracted from the event stream

`WorkProfile.emitting before first rest after` records `before` work events
before the first output, then each `(gap,q)` in `rest` records the work strictly
between the preceding output and `q`, and finally `after` records the work after
the last output.  Thus the profile exposes the actual event counts that the
delay theorem bounds; none of these counts is supplied as a hypothesis.
-/

inductive WorkProfile (α : Type) where
  | silent (work : Nat)
  | emitting
      (before : Nat)
      (first : List α)
      (rest : List (Nat × List α))
      (after : Nat)
deriving DecidableEq

/-- Output projection of a work profile. -/
def WorkProfile.outputs : WorkProfile α → List (List α)
  | .silent _ => []
  | .emitting _ first rest _ => first :: rest.map Prod.snd

/-- Add work to the beginning of a profile. -/
def WorkProfile.addBefore (k : Nat) : WorkProfile α → WorkProfile α
  | .silent work => .silent (k + work)
  | .emitting before first rest after =>
      .emitting (k + before) first rest after

/-- Concatenation of exact interval profiles. -/
def WorkProfile.append : WorkProfile α → WorkProfile α → WorkProfile α
  | .silent a, .silent b => .silent (a + b)
  | .silent a, .emitting before first rest after =>
      .emitting (a + before) first rest after
  | .emitting before first rest after, .silent b =>
      .emitting before first rest (after + b)
  | .emitting before₁ first₁ rest₁ after₁,
      .emitting before₂ first₂ rest₂ after₂ =>
      .emitting before₁ first₁
        (rest₁ ++ (after₁ + before₂, first₂) :: rest₂) after₂

/-- Exact profile of a concrete event list. -/
def workProfile : List (DfsEvent α) → WorkProfile α
  | [] => .silent 0
  | e :: events =>
      match e with
      | .output p =>
          (WorkProfile.emitting 0 p [] 0).append (workProfile events)
      | .enter _ | .query _ _ _ | .resume _ =>
          (workProfile events).addBefore 1
      | .exit _ => workProfile events

@[simp] theorem WorkProfile.outputs_silent (work : Nat) :
    (WorkProfile.silent work : WorkProfile α).outputs = [] := rfl

@[simp] theorem WorkProfile.outputs_emitting
    (before : Nat) (first : List α) (rest : List (Nat × List α)) (after : Nat) :
    (WorkProfile.emitting before first rest after).outputs =
      first :: rest.map Prod.snd := rfl

@[simp] theorem WorkProfile.outputs_addBefore
    (k : Nat) (profile : WorkProfile α) :
    (profile.addBefore k).outputs = profile.outputs := by
  cases profile <;> rfl

@[simp] theorem WorkProfile.outputs_append
    (left right : WorkProfile α) :
    (left.append right).outputs = left.outputs ++ right.outputs := by
  cases left <;> cases right <;> simp [WorkProfile.append, WorkProfile.outputs]

@[simp] theorem workProfile_outputs (events : List (DfsEvent α)) :
    (workProfile events).outputs = outputsOfTrace events := by
  induction events with
  | nil => rfl
  | cons e events ih =>
      cases e <;> simp [workProfile, outputsOfTrace, ih]

theorem WorkProfile.append_assoc
    (a b c : WorkProfile α) :
    (a.append b).append c = a.append (b.append c) := by
  cases a <;> cases b <;> cases c <;>
    simp [WorkProfile.append, Nat.add_assoc, List.append_assoc]

@[simp] theorem WorkProfile.append_silent_zero_right (p : WorkProfile α) :
    p.append (.silent 0) = p := by
  cases p <;> simp [WorkProfile.append]

@[simp] theorem WorkProfile.silent_zero_append (p : WorkProfile α) :
    (WorkProfile.silent 0).append p = p := by
  cases p <;> simp [WorkProfile.append]

theorem WorkProfile.addBefore_append
    (k : Nat) (a b : WorkProfile α) :
    (a.append b).addBefore k = (a.addBefore k).append b := by
  cases a <;> cases b <;>
    simp [WorkProfile.addBefore, WorkProfile.append, Nat.add_assoc]

@[simp] theorem workProfile_append
    (xs ys : List (DfsEvent α)) :
    workProfile (xs ++ ys) = (workProfile xs).append (workProfile ys) := by
  induction xs with
  | nil => simp [workProfile]
  | cons e xs ih =>
      cases e with
      | enter pfx =>
          simp only [List.cons_append, workProfile]
          rw [ih, WorkProfile.addBefore_append]
      | query pfx w answer =>
          simp only [List.cons_append, workProfile]
          rw [ih, WorkProfile.addBefore_append]
      | resume pfx =>
          simp only [List.cons_append, workProfile]
          rw [ih, WorkProfile.addBefore_append]
      | output p =>
          simp only [List.cons_append, workProfile]
          rw [ih, WorkProfile.append_assoc]
      | exit pfx => simpa [workProfile] using ih

/-- Sum the exact work counts stored between consecutive outputs. -/
def WorkProfile.gapWork : List (Nat × List α) → Nat
  | [] => 0
  | (gap, _) :: rest => gap + gapWork rest

@[simp] theorem WorkProfile.gapWork_append
    (xs ys : List (Nat × List α)) :
    gapWork (xs ++ ys) = gapWork xs + gapWork ys := by
  induction xs with
  | nil => simp [gapWork]
  | cons x xs ih =>
      rcases x with ⟨gap, path⟩
      simp [gapWork, ih, Nat.add_assoc]

/-- The profile's interval numbers sum to the exact number of work events. -/
def WorkProfile.totalWork : WorkProfile α → Nat
  | .silent work => work
  | .emitting before _ rest after =>
      before + gapWork rest + after

@[simp] theorem WorkProfile.totalWork_addBefore
    (k : Nat) (profile : WorkProfile α) :
    (profile.addBefore k).totalWork = k + profile.totalWork := by
  cases profile <;>
    simp [WorkProfile.addBefore, WorkProfile.totalWork, Nat.add_assoc]

@[simp] theorem WorkProfile.totalWork_append
    (left right : WorkProfile α) :
    (left.append right).totalWork = left.totalWork + right.totalWork := by
  cases left <;> cases right <;>
    simp [WorkProfile.append, WorkProfile.totalWork, WorkProfile.gapWork,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[simp] theorem workProfile_totalWork (events : List (DfsEvent α)) :
    (workProfile events).totalWork = traceWork events := by
  induction events with
  | nil => rfl
  | cons e events ih =>
      cases e with
      | enter pfx =>
          simpa [workProfile, traceWork, DfsEvent.isWork, Nat.add_comm] using ih
      | query pfx w answer =>
          simpa [workProfile, traceWork, DfsEvent.isWork, Nat.add_comm] using ih
      | resume pfx =>
          simpa [workProfile, traceWork, DfsEvent.isWork, Nat.add_comm] using ih
      | output path =>
          calc
            ((WorkProfile.emitting 0 path [] 0).append
                (workProfile events)).totalWork =
                (WorkProfile.emitting 0 path [] 0).totalWork +
                  (workProfile events).totalWork :=
              WorkProfile.totalWork_append _ _
            _ = (workProfile events).totalWork := by
              simp [WorkProfile.totalWork, WorkProfile.gapWork]
            _ = traceWork events := ih
            _ = traceWork (.output path :: events) := by
              rfl
      | exit pfx =>
          simpa [workProfile, traceWork, DfsEvent.isWork] using ih

/-! ## Semantic bounds on exact profiles -/

/-- The final output stored by a nonempty profile. -/
def lastProfileOutput (first : List α) : List (Nat × List α) → List α
  | [] => first
  | (_, q) :: rest => lastProfileOutput q rest

/-- Every concrete inter-output interval stored in a profile obeys the sharp
longest-common-prefix frame bound. -/
def ProfileGapsBound (I : FiniteRegularPathInstance α) :
    List α → List (Nat × List α) → Prop
  | _, [] => True
  | p, (gap, q) :: rest =>
      gap ≤ dfsGapFrameWork I p q ∧ ProfileGapsBound I q rest

/-- Every output of a profile extends the root prefix of its recursive call. -/
def ProfileExtends (root : List α) : WorkProfile α → Prop
  | .silent _ => True
  | .emitting _ first rest _ =>
      root <+: first ∧ ∀ item ∈ rest, root <+: item.2

/-- Every scan output records the successor branch from which it came. -/
def ProfileOrigins (root : List α) (ws : List α) (profile : WorkProfile α) : Prop :=
  ∀ p ∈ profile.outputs, ∃ w ∈ ws, root ++ [w] <+: p

/-- Exact first/inter-output/last bounds for a productive recursive call, and
the one-frame bound for a call producing no output. -/
def ProfileBound (I : FiniteRegularPathInstance α) (root : List α) :
    WorkProfile α → Prop
  | .silent work => work ≤ I.outBound + 1
  | .emitting before first rest after =>
      before ≤ (first.length - root.length + 1) * (I.outBound + 1) ∧
      ProfileGapsBound I first rest ∧
      after ≤ ((lastProfileOutput first rest).length - root.length) *
        (I.outBound + 1)

theorem lastProfileOutput_mem
    (first : List α) (rest : List (Nat × List α)) :
    lastProfileOutput first rest ∈ first :: rest.map Prod.snd := by
  induction rest generalizing first with
  | nil => simp [lastProfileOutput]
  | cons item rest ih =>
      rcases item with ⟨gap, q⟩
      simp only [lastProfileOutput, List.map_cons, List.mem_cons]
      exact Or.inr (by simpa using ih q)

theorem ProfileExtends_first
    {root : List α} {before after : Nat} {first : List α}
    {rest : List (Nat × List α)}
    (h : ProfileExtends root (.emitting before first rest after)) :
    root <+: first := h.1

theorem ProfileExtends_last
    {root : List α} {before after : Nat} {first : List α}
    {rest : List (Nat × List α)}
    (h : ProfileExtends root (.emitting before first rest after)) :
    root <+: lastProfileOutput first rest := by
  rcases h with ⟨hfirst, hrest⟩
  have hmem := lastProfileOutput_mem first rest
  simp only [List.mem_cons, List.mem_map] at hmem
  rcases hmem with hlast | hlast
  · simpa [hlast] using hfirst
  · rcases hlast with ⟨item, hitem, heq⟩
    simpa [← heq] using hrest item hitem

@[simp] theorem lastProfileOutput_append_bridge
    (first next : List α) (left right : List (Nat × List α)) (gap : Nat) :
    lastProfileOutput first (left ++ (gap, next) :: right) =
      lastProfileOutput next right := by
  induction left generalizing first with
  | nil => rfl
  | cons item left ih =>
      rcases item with ⟨itemGap, itemPath⟩
      exact ih itemPath

theorem ProfileGapsBound_append_bridge
    (I : FiniteRegularPathInstance α)
    {first : List α} {rest₁ : List (Nat × List α)}
    {gap : Nat} {next : List α} {rest₂ : List (Nat × List α)}
    (hleft : ProfileGapsBound I first rest₁)
    (hbridge : gap ≤ dfsGapFrameWork I (lastProfileOutput first rest₁) next)
    (hright : ProfileGapsBound I next rest₂) :
    ProfileGapsBound I first (rest₁ ++ (gap, next) :: rest₂) := by
  induction rest₁ generalizing first with
  | nil => exact ⟨hbridge, hright⟩
  | cons item rest ih =>
      rcases item with ⟨firstGap, q⟩
      rcases hleft with ⟨hfirst, htail⟩
      exact ⟨hfirst, ih htail hbridge⟩

@[simp] theorem ProfileExtends_silent (root : List α) (work : Nat) :
    ProfileExtends root (.silent work : WorkProfile α) := trivial

theorem profileExtends_iff
    (root : List α) (profile : WorkProfile α) :
    ProfileExtends root profile ↔
      ∀ p ∈ profile.outputs, root <+: p := by
  cases profile with
  | silent work => simp [ProfileExtends, WorkProfile.outputs]
  | emitting before first rest after =>
      simp only [ProfileExtends, WorkProfile.outputs, List.mem_cons,
        List.mem_map]
      constructor
      · rintro ⟨hfirst, hrest⟩ p (rfl | hp)
        · exact hfirst
        · rcases hp with ⟨item, hitem, rfl⟩
          exact hrest item hitem
      · intro hall
        constructor
        · exact hall first (by simp)
        · intro item hitem
          exact hall item.2 (by
            exact Or.inr ⟨item, hitem, rfl⟩)

theorem commonPrefixLength_eq_length_of_append_distinct
    (pfx left right : List α) (w₁ w₂ : α) (hne : w₁ ≠ w₂) :
    commonPrefixLength (pfx ++ w₁ :: left) (pfx ++ w₂ :: right) = pfx.length := by
  induction pfx with
  | nil => simp [commonPrefixLength, hne]
  | cons x xs ih => simp [commonPrefixLength, ih, Nat.add_comm]

theorem dfsFrameTransitions_eq_of_sibling_extensions
    (pfx left right : List α) (w₁ w₂ : α) (hne : w₁ ≠ w₂) :
    dfsFrameTransitions (pfx ++ w₁ :: left) (pfx ++ w₂ :: right) =
      ((pfx ++ w₁ :: left).length - pfx.length) +
      ((pfx ++ w₂ :: right).length - pfx.length) := by
  simp [dfsFrameTransitions,
    commonPrefixLength_eq_length_of_append_distinct pfx left right w₁ w₂ hne]

theorem commonPrefixLength_eq_of_sibling_prefixes
    {pfx p q : List α} {w₁ w₂ : α} (hne : w₁ ≠ w₂)
    (hp : pfx ++ [w₁] <+: p) (hq : pfx ++ [w₂] <+: q) :
    commonPrefixLength p q = pfx.length := by
  rcases hp with ⟨left, rfl⟩
  rcases hq with ⟨right, rfl⟩
  simpa [List.append_assoc] using
    commonPrefixLength_eq_length_of_append_distinct pfx left right w₁ w₂ hne

theorem dfsFrameTransitions_eq_of_sibling_prefixes
    {pfx p q : List α} {w₁ w₂ : α} (hne : w₁ ≠ w₂)
    (hp : pfx ++ [w₁] <+: p) (hq : pfx ++ [w₂] <+: q) :
    dfsFrameTransitions p q =
      (p.length - pfx.length) + (q.length - pfx.length) := by
  simp [dfsFrameTransitions,
    commonPrefixLength_eq_of_sibling_prefixes hne hp hq]

/-- Profile-level streaming scan, definitionally parallel to `scanTrace`. -/
def scanProfile (I : FiniteRegularPathInstance α)
    (oracle : ExactReachabilityOracle I) (pfx : List α)
    (childProfile : α → WorkProfile α) : List α → WorkProfile α
  | [] => .silent 0
  | w :: ws =>
      if oracle.query pfx w then
        (childProfile w).append ((scanProfile I oracle pfx childProfile ws).addBefore 1)
          |>.addBefore 1
      else
        (scanProfile I oracle pfx childProfile ws).addBefore 1

/-- Strengthened bound used while a frame is partway through its successor
scan.  The explicit `ws.length + 1` term is the exact remaining-frame budget;
the outer `enter` event later converts it to the uniform `outBound + 1` charge. -/
def ScanProfileBound (I : FiniteRegularPathInstance α)
    (root : List α) (ws : List α) : WorkProfile α → Prop
  | .silent work => work = ws.length
  | .emitting before first rest after =>
      before + 1 ≤
          (first.length - root.length) * (I.outBound + 1) + (ws.length + 1) ∧
      ProfileGapsBound I first rest ∧
      after ≤
        ((lastProfileOutput first rest).length - root.length - 1) *
            (I.outBound + 1) +
          (ws.length + 1)

@[simp] theorem workProfile_scanTrace
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) (childTrace : α → List (DfsEvent α))
    (ws : List α) :
    workProfile (scanTrace I oracle fuel pfx childTrace ws) =
      scanProfile I oracle pfx (fun w => workProfile (childTrace w)) ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      simp only [scanTrace, scanProfile]
      by_cases hq : oracle.query pfx w = true
      · simp [hq, ih, workProfile, workProfile_append]
      · have hfalse : oracle.query pfx w = false := Bool.eq_false_of_not_eq_true hq
        simp [hfalse, ih, workProfile]

@[simp] theorem workProfile_dfsTrace_zero
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (pfx : List α) :
    workProfile (dfsTrace I oracle 0 pfx) =
      if pfx.getLast? = some I.target then .emitting 1 pfx [] 0
      else .silent 1 := by
  by_cases htarget : pfx.getLast? = some I.target <;>
    simp [dfsTrace, htarget, workProfile, WorkProfile.append,
      WorkProfile.addBefore]

theorem workProfile_dfsTrace_succ
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) :
    workProfile (dfsTrace I oracle (fuel + 1) pfx) =
      if pfx.getLast? = some I.target then .emitting 1 pfx [] 0
      else
        (scanProfile I oracle pfx
          (fun w => workProfile (dfsTrace I oracle fuel (pfx ++ [w])))
          (orderedAdmissibleSuccessors I pfx)).addBefore 1 := by
  by_cases htarget : pfx.getLast? = some I.target
  · simp [dfsTrace, htarget, workProfile, WorkProfile.append,
      WorkProfile.addBefore]
  · simp only [dfsTrace, htarget, if_false, workProfile,
      workProfile_append, WorkProfile.append_silent_zero_right,
      workProfile_scanTrace]

theorem dfsTrace_profile_extends
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) :
    ProfileExtends pfx (workProfile (dfsTrace I oracle fuel pfx)) := by
  rw [profileExtends_iff]
  intro p hp
  rw [workProfile_outputs, outputsOfTrace_dfsTrace] at hp
  exact enumerateAux_output_prefix I oracle fuel pfx p hp

/-- A successor scan has an exact profile bound provided every positive child
is productive and already satisfies the recursive profile invariant. -/
theorem scanProfile_certificate
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (pfx : List α) (childProfile : α → WorkProfile α) (ws : List α)
    (hnodup : ws.Nodup)
    (hlen : ws.length ≤ I.outBound)
    (hchild : ∀ w ∈ ws, oracle.query pfx w = true →
      ProfileBound I (pfx ++ [w]) (childProfile w) ∧
      ProfileExtends (pfx ++ [w]) (childProfile w) ∧
      (childProfile w).outputs ≠ []) :
    ScanProfileBound I pfx ws (scanProfile I oracle pfx childProfile ws) ∧
      ProfileOrigins pfx ws (scanProfile I oracle pfx childProfile ws) := by
  induction ws with
  | nil =>
      simp [scanProfile, ScanProfileBound, ProfileOrigins,
        WorkProfile.outputs]
  | cons w ws ih =>
      have hnodup' := List.nodup_cons.mp hnodup
      have hlen' : ws.length ≤ I.outBound := by
        have hs : ws.length + 1 ≤ I.outBound := by simpa using hlen
        omega
      have hchild' : ∀ z ∈ ws, oracle.query pfx z = true →
          ProfileBound I (pfx ++ [z]) (childProfile z) ∧
          ProfileExtends (pfx ++ [z]) (childProfile z) ∧
          (childProfile z).outputs ≠ [] := by
        intro z hz
        exact hchild z (by simp [hz])
      rcases ih hnodup'.2 hlen' hchild' with ⟨hrestBound, hrestOrigins⟩
      by_cases hq : oracle.query pfx w = true
      · rcases hchild w (by simp) hq with ⟨hcbound, hcextends, hcne⟩
        have hcevery : ∀ p ∈ (childProfile w).outputs, pfx ++ [w] <+: p :=
          (profileExtends_iff (pfx ++ [w]) (childProfile w)).1 hcextends
        have horiginsCombined :
            ProfileOrigins pfx (w :: ws)
              (scanProfile I oracle pfx childProfile (w :: ws)) := by
          intro p hp
          have hp' : p ∈ (childProfile w).outputs ++
              (scanProfile I oracle pfx childProfile ws).outputs := by
            simpa only [scanProfile, hq, if_true,
              WorkProfile.outputs_addBefore, WorkProfile.outputs_append] using hp
          rcases List.mem_append.mp hp' with hpChild | hpRest
          · exact ⟨w, List.mem_cons_self, hcevery p hpChild⟩
          · rcases hrestOrigins p hpRest with ⟨z, hz, hzprefix⟩
            exact ⟨z, List.mem_cons_of_mem w hz, hzprefix⟩
        cases hcp : childProfile w with
        | silent childWork =>
            exfalso
            apply hcne
            simp [hcp, WorkProfile.outputs]
        | emitting cbefore cfirst crest cafter =>
            cases hrp : scanProfile I oracle pfx childProfile ws with
            | silent restWork =>
                have hrsilent : restWork = ws.length := by
                  simpa [hrp, ScanProfileBound] using hrestBound
                have hcbound' := hcbound
                have hcextends' := hcextends
                simp only [hcp, ProfileBound, ProfileExtends,
                  List.length_append, List.length_singleton] at hcbound' hcextends'
                have hfirstLen := hcextends'.1.length_le
                simp only [List.length_append, List.length_singleton] at hfirstLen
                have hfirstDepth :
                    cfirst.length - (pfx.length + 1) + 1 =
                      cfirst.length - pfx.length := by
                  omega
                have hlastPrefix := ProfileExtends_last
                  (before := cbefore) (after := cafter) hcextends'
                have hlastLen := hlastPrefix.length_le
                simp only [List.length_append, List.length_singleton] at hlastLen
                have hlastDepth :
                    (lastProfileOutput cfirst crest).length - (pfx.length + 1) =
                      (lastProfileOutput cfirst crest).length - pfx.length - 1 := by
                  omega
                rw [hfirstDepth] at hcbound'
                rw [hlastDepth] at hcbound'
                constructor
                · simp only [scanProfile, hq, if_true, hcp, hrp,
                    WorkProfile.addBefore, WorkProfile.append,
                    ScanProfileBound, List.length_cons]
                  refine ⟨?_, hcbound'.2.1, ?_⟩
                  · omega
                  · omega
                · exact horiginsCombined
            | emitting rbefore rfirst rrest rafter =>
                have hrbound' := hrestBound
                simp only [hrp, ScanProfileBound] at hrbound'
                have hroriginFirst := hrestOrigins rfirst (by
                  simp [hrp, WorkProfile.outputs])
                rcases hroriginFirst with ⟨z, hzws, hzprefix⟩
                have hwne : w ≠ z := by
                  intro hwz
                  subst z
                  exact hnodup'.1 hzws
                have hcbound' := hcbound
                have hcextends' := hcextends
                simp only [hcp, ProfileBound, ProfileExtends,
                  List.length_append, List.length_singleton] at hcbound' hcextends'
                have hlastPrefix : pfx ++ [w] <+:
                    lastProfileOutput cfirst crest :=
                  ProfileExtends_last
                    (before := cbefore) (after := cafter) hcextends'
                have htransition :
                    dfsFrameTransitions (lastProfileOutput cfirst crest) rfirst =
                      ((lastProfileOutput cfirst crest).length - pfx.length) +
                        (rfirst.length - pfx.length) :=
                  dfsFrameTransitions_eq_of_sibling_prefixes hwne
                    hlastPrefix hzprefix
                have hcross : cafter + (1 + rbefore) ≤
                    dfsGapFrameWork I (lastProfileOutput cfirst crest) rfirst := by
                  unfold dfsGapFrameWork
                  rw [htransition]
                  have hlastLen := hlastPrefix.length_le
                  simp only [List.length_append, List.length_singleton] at hlastLen
                  have hleftSplit :
                      (lastProfileOutput cfirst crest).length - pfx.length =
                        ((lastProfileOutput cfirst crest).length -
                          (pfx.length + 1)) + 1 := by
                    omega
                  have hremaining : ws.length + 1 ≤ I.outBound + 1 := by
                    omega
                  calc
                    cafter + (1 + rbefore) = cafter + (rbefore + 1) := by omega
                    _ ≤ ((lastProfileOutput cfirst crest).length -
                          (pfx.length + 1)) * (I.outBound + 1) +
                        ((rfirst.length - pfx.length) * (I.outBound + 1) +
                          (ws.length + 1)) :=
                      Nat.add_le_add hcbound'.2.2 hrbound'.1
                    _ ≤ ((lastProfileOutput cfirst crest).length -
                          (pfx.length + 1)) * (I.outBound + 1) +
                        ((rfirst.length - pfx.length) * (I.outBound + 1) +
                          (I.outBound + 1)) := by
                      exact Nat.add_le_add_left
                        (Nat.add_le_add_left hremaining _) _
                    _ = (((lastProfileOutput cfirst crest).length -
                          (pfx.length + 1)) + 1 +
                        (rfirst.length - pfx.length)) * (I.outBound + 1) := by
                      ring
                    _ = (((lastProfileOutput cfirst crest).length - pfx.length) +
                        (rfirst.length - pfx.length)) * (I.outBound + 1) := by
                      rw [hleftSplit]
                constructor
                · simp only [scanProfile, hq, if_true, hcp, hrp,
                    WorkProfile.addBefore, WorkProfile.append,
                    ScanProfileBound, List.length_cons]
                  refine ⟨?_, ?_, ?_⟩
                  · have hfirstLen := hcextends'.1.length_le
                    simp only [List.length_append, List.length_singleton] at hfirstLen
                    have hfirstDepth :
                        cfirst.length - (pfx.length + 1) + 1 =
                          cfirst.length - pfx.length := by
                      omega
                    rw [hfirstDepth] at hcbound'
                    omega
                  · exact ProfileGapsBound_append_bridge I
                      hcbound'.2.1 hcross hrbound'.2.1
                  · rw [lastProfileOutput_append_bridge]
                    omega
                · exact horiginsCombined
      · have hfalse : oracle.query pfx w = false :=
          Bool.eq_false_of_not_eq_true hq
        cases hrp : scanProfile I oracle pfx childProfile ws with
        | silent restWork =>
            have hrsilent : restWork = ws.length := by
              simpa [hrp, ScanProfileBound] using hrestBound
            constructor
            · simp [scanProfile, hfalse, hrp, WorkProfile.addBefore,
                ScanProfileBound, hrsilent, Nat.add_comm]
            · simp [scanProfile, hfalse, hrp, WorkProfile.addBefore,
                ProfileOrigins, WorkProfile.outputs]
        | emitting rbefore rfirst rrest rafter =>
            have hrbound' := hrestBound
            simp only [hrp, ScanProfileBound] at hrbound'
            constructor
            · simp only [scanProfile, hfalse, hrp,
                WorkProfile.addBefore, ScanProfileBound, List.length_cons]
              constructor
              · omega
              constructor
              · exact hrbound'.2.1
              · omega
            · intro p hp
              have hpRest : p ∈
                  (scanProfile I oracle pfx childProfile ws).outputs := by
                simpa [scanProfile, hfalse, hrp, WorkProfile.addBefore,
                  WorkProfile.outputs] using hp
              rcases hrestOrigins p hpRest with ⟨z, hz, hprefix⟩
              exact ⟨z, by simp [hz], hprefix⟩

theorem profileBound_of_scan
    (I : FiniteRegularPathInstance α) (root ws : List α)
    (profile : WorkProfile α)
    (hlen : ws.length ≤ I.outBound)
    (hscan : ScanProfileBound I root ws profile)
    (horigins : ProfileOrigins root ws profile) :
    ProfileBound I root (profile.addBefore 1) := by
  cases profile with
  | silent work =>
      simp only [WorkProfile.addBefore, ProfileBound]
      simp only [ScanProfileBound] at hscan
      omega
  | emitting before first rest after =>
      simp only [WorkProfile.addBefore, ProfileBound]
      simp only [ScanProfileBound] at hscan
      have hfirstOrigin := horigins first (by
        simp [WorkProfile.outputs])
      rcases hfirstOrigin with ⟨wfirst, _, hfirstPrefix⟩
      have hlastOrigin := horigins (lastProfileOutput first rest)
        (lastProfileOutput_mem first rest)
      rcases hlastOrigin with ⟨wlast, _, hlastPrefix⟩
      have hfirstLen := hfirstPrefix.length_le
      have hlastLen := hlastPrefix.length_le
      simp only [List.length_append, List.length_singleton] at hfirstLen hlastLen
      have hafterDepth :
          (lastProfileOutput first rest).length - root.length =
            ((lastProfileOutput first rest).length - root.length - 1) + 1 := by
        omega
      refine ⟨?_, hscan.2.1, ?_⟩
      · rw [Nat.add_mul]
        simp only [one_mul]
        rw [Nat.add_comm 1 before]
        exact Nat.le_trans hscan.1
          (Nat.add_le_add_left
            (by omega : ws.length + 1 ≤ I.outBound + 1) _)
      · rw [hafterDepth, Nat.add_mul]
        simp only [one_mul]
        exact Nat.le_trans hscan.2.2
          (Nat.add_le_add_left
            (by omega : ws.length + 1 ≤ I.outBound + 1) _)

/-- The exact event profile of every semantically valid recursive call obeys
the one-frame, sharp inter-output, and endpoint bounds whenever its remaining
fuel can accommodate every regular completion. -/
theorem dfsTrace_profile_bound
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    ∀ fuel pfx,
      IsRegularPrefix I pfx →
      Fintype.card α ≤ pfx.length + fuel →
      ProfileBound I pfx (workProfile (dfsTrace I oracle fuel pfx)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro pfx hpfx hbudget
      by_cases htarget : pfx.getLast? = some I.target
      · rw [workProfile_dfsTrace_zero, if_pos htarget]
        simp [ProfileBound, ProfileGapsBound, lastProfileOutput]
      · rw [workProfile_dfsTrace_zero, if_neg htarget]
        simp [ProfileBound]
  | succ fuel ih =>
      intro pfx hpfx hbudget
      by_cases htarget : pfx.getLast? = some I.target
      · rw [workProfile_dfsTrace_succ, if_pos htarget]
        simp [ProfileBound, ProfileGapsBound, lastProfileOutput]
      · rw [workProfile_dfsTrace_succ, if_neg htarget]
        let ws := orderedAdmissibleSuccessors I pfx
        have hwsNodup : ws.Nodup := orderedAdmissibleSuccessors_nodup I pfx
        have hwsLength : ws.length ≤ I.outBound :=
          orderedAdmissibleSuccessors_length_le I pfx
        have hpfxNe : pfx ≠ [] := by
          intro hnil
          simp [IsRegularPrefix, hnil] at hpfx
        let v := pfx.getLast hpfxNe
        have hlast : pfx.getLast? = some v :=
          List.getLast?_eq_getLast_of_ne_nil hpfxNe
        have hchildren : ∀ w ∈ ws, oracle.query pfx w = true →
            ProfileBound I (pfx ++ [w])
                (workProfile (dfsTrace I oracle fuel (pfx ++ [w]))) ∧
            ProfileExtends (pfx ++ [w])
                (workProfile (dfsTrace I oracle fuel (pfx ++ [w]))) ∧
            (workProfile (dfsTrace I oracle fuel (pfx ++ [w]))).outputs ≠ [] := by
          intro w hw hquery
          have haccepted : w ∈ acceptedSuccessors I oracle pfx :=
            (mem_acceptedSuccessors_iff I oracle).2 ⟨hw, hquery⟩
          have hchildPrefix : IsRegularPrefix I (pfx ++ [w]) :=
            regularPrefix_append_of_accepted I oracle hpfx hlast haccepted
          have hchildBudget :
              Fintype.card α ≤ (pfx ++ [w]).length + fuel := by
            simpa [List.length_append, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using hbudget
          have hbound := ih (pfx ++ [w]) hchildPrefix hchildBudget
          have hextension : HasRegularExtension I pfx w :=
            (oracle_accepts_iff_regular_extension I oracle hpfx hlast hw).1 hquery
          rcases hextension with ⟨tail, hfull⟩
          have hfullLength : (pfx ++ w :: tail).length ≤ Fintype.card α :=
            (regular_nodup hfull.2.2.2).length_le_card
          have htailLength : tail.length ≤ fuel := by
            simp only [List.length_append, List.length_cons] at hfullLength
            omega
          have hchildTarget :
              IsTargetRegularPath I ((pfx ++ [w]) ++ tail) := by
            simpa [List.append_assoc] using hfull
          have hmember : (pfx ++ [w]) ++ tail ∈
              enumerateAux I oracle fuel (pfx ++ [w]) :=
            enumerateAux_complete_extension I oracle fuel (pfx ++ [w]) tail
              hchildPrefix hchildTarget htailLength
          refine ⟨hbound, dfsTrace_profile_extends I oracle fuel (pfx ++ [w]), ?_⟩
          intro hempty
          have houtputsEmpty :
              outputsOfTrace (dfsTrace I oracle fuel (pfx ++ [w])) = [] := by
            simpa [workProfile_outputs] using hempty
          rw [outputsOfTrace_dfsTrace] at houtputsEmpty
          rw [houtputsEmpty] at hmember
          simp at hmember
        have hscan := scanProfile_certificate I oracle pfx
          (fun w => workProfile (dfsTrace I oracle fuel (pfx ++ [w]))) ws
          hwsNodup hwsLength hchildren
        exact profileBound_of_scan I pfx ws _ hwsLength hscan.1 hscan.2

theorem dfsTrace_ends_with_exit
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I)
    (fuel : Nat) (pfx : List α) :
    (dfsTrace I oracle fuel pfx).getLast? = some (.exit pfx) := by
  cases fuel <;> by_cases htarget : pfx.getLast? = some I.target <;>
    simp only [dfsTrace_zero, dfsTrace_succ, htarget, if_true, if_false]
  all_goals
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    rfl

/-- End-to-end combinatorial delay certificate for the explicit event
evaluator.  The profile is extracted from the events, its output projection is
the existing exact enumerator, and its four cases are bounded as follows:

* `silent work`: the complete no-output run uses at most one root frame charge;
* `emitting before ...`: `before` counts preprocessing/setup and work through
  the first output;
* every stored `(gap,q)` is the actual work between adjacent output events and
  is bounded sharply by retreat/descent through their longest common prefix;
* `after` counts the actual work after the final output through root exit.

`exit [I.source]` is an explicit termination event.  Replacing one exact query
unit by Goldberg--Karzanov's cited `O(|V|+|E|)` implementation cost remains the
only external asymptotic step. -/
theorem explicit_dfs_event_trace_certificate
    (I : FiniteRegularPathInstance α) (oracle : ExactReachabilityOracle I) :
    let events := enumerateRegularPathsTrace I oracle
    let profile := workProfile events
    profile.totalWork = traceWork events ∧
      profile.outputs = enumerateRegularPaths I oracle ∧
      ProfileBound I [I.source] profile ∧
      events.getLast? = some (.exit [I.source]) := by
  dsimp only [enumerateRegularPathsTrace]
  constructor
  · exact workProfile_totalWork _
  constructor
  · rw [workProfile_outputs]
    exact outputsOfTrace_dfsTrace I oracle (Fintype.card α) [I.source]
  constructor
  · apply dfsTrace_profile_bound I oracle
    · simp [IsRegularPrefix, Walk, Regular]
    · simp
  · exact dfsTrace_ends_with_exit I oracle (Fintype.card α) [I.source]

end RegularPathDelay
