/-
Paper: Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892986
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup

/-!
# Exact fixed-endpoint regular-path enumeration

The completion oracle is exact regular reachability after deleting a prefix
and all complementary vertices.  The explicit trace below executes the
ordered DFS one successor query at a time and records frame entry, query,
resume, output, and exit events.  Its work profile is extracted from those
events; interval counts are not theorem hypotheses.

Goldberg--Karzanov's linear-time regular-reachability implementation remains
an external complexity input.  Lean proves the combinatorial event-count
certificate, not that implementation's executable running time.
-/

namespace RegularPathDelay

variable {alpha : Type}

def Walk (edge : alpha → alpha → Prop) : List alpha → Prop
  | [] => True
  | [_] => True
  | u :: v :: tail => edge u v ∧ Walk edge (v :: tail)

def Compatible (bar : alpha → alpha) (x y : alpha) : Prop :=
  x ≠ y ∧ bar x ≠ y ∧ x ≠ bar y

def Regular (bar : alpha → alpha) (xs : List alpha) : Prop :=
  xs.Pairwise (Compatible bar)

def Survives (bar : alpha → alpha) (old : List alpha) (y : alpha) : Prop :=
  y ∉ old ∧ bar y ∉ old

def SuffixSurvives (bar : alpha → alpha) (old tail : List alpha) : Prop :=
  ∀ y ∈ tail, Survives bar old y

structure FiniteRegularPathInstance (alpha : Type) [DecidableEq alpha]
    [Fintype alpha] where
  edge : alpha → alpha → Bool
  bar : alpha → alpha
  bar_involutive : ∀ x, bar (bar x) = x
  bar_fixedPointFree : ∀ x, bar x ≠ x
  edge_skew : ∀ u v, edge u v = edge (bar v) (bar u)
  loopless : ∀ v, edge v v = false
  successors : alpha → List alpha
  successors_nodup : ∀ v, (successors v).Nodup
  mem_successors_iff : ∀ v w, w ∈ successors v ↔ edge v w = true
  outBound : Nat
  successors_length_le : ∀ v, (successors v).length ≤ outBound
  source : alpha
  target : alpha

variable {alpha : Type} [DecidableEq alpha] [Fintype alpha]

def FiniteRegularPathInstance.Edge (I : FiniteRegularPathInstance alpha)
    (u v : alpha) : Prop :=
  I.edge u v = true

def IsRegularPathFromTo (I : FiniteRegularPathInstance alpha)
    (a b : alpha) (xs : List alpha) : Prop :=
  xs.head? = some a ∧ xs.getLast? = some b ∧ Walk I.Edge xs ∧ Regular I.bar xs

def IsTargetRegularPath (I : FiniteRegularPathInstance alpha)
    (xs : List alpha) : Prop :=
  IsRegularPathFromTo I I.source I.target xs

def IsRegularPrefix (I : FiniteRegularPathInstance alpha)
    (pfx : List alpha) : Prop :=
  pfx.head? = some I.source ∧ Walk I.Edge pfx ∧ Regular I.bar pfx

def orderedAdmissibleSuccessors (I : FiniteRegularPathInstance alpha)
    (pfx : List alpha) : List alpha :=
  match pfx.getLast? with
  | none => []
  | some v => (I.successors v).filter
      (fun w => decide (w ∉ pfx ∧ I.bar w ∉ pfx))

def DeletedCompletion (I : FiniteRegularPathInstance alpha)
    (old : List alpha) (w : alpha) : Prop :=
  ∃ tail : List alpha,
    IsRegularPathFromTo I w I.target (w :: tail) ∧
    Survives I.bar old w ∧ SuffixSurvives I.bar old tail

def HasRegularExtension (I : FiniteRegularPathInstance alpha)
    (pfx : List alpha) (w : alpha) : Prop :=
  ∃ tail : List alpha, IsTargetRegularPath I (pfx ++ w :: tail)

structure ExactReachabilityOracle (I : FiniteRegularPathInstance alpha) where
  query : List alpha → alpha → Bool
  correct : ∀ pfx w, query pfx w = true ↔ DeletedCompletion I pfx w

def acceptedSuccessors (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) (pfx : List alpha) : List alpha :=
  (orderedAdmissibleSuccessors I pfx).filter
    (fun w => oracle.query pfx w = true)

def enumerateAux (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) : Nat → List alpha → List (List alpha)
  | 0, pfx => if pfx.getLast? = some I.target then [pfx] else []
  | fuel + 1, pfx =>
      if pfx.getLast? = some I.target then [pfx]
      else (acceptedSuccessors I oracle pfx).flatMap
        (fun w => enumerateAux I oracle fuel (pfx ++ [w]))

def enumerateRegularPaths (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) : List (List alpha) :=
  enumerateAux I oracle (Fintype.card alpha) [I.source]

def commonPrefixLength : List alpha → List alpha → Nat
  | x :: xs, y :: ys => if x = y then 1 + commonPrefixLength xs ys else 0
  | _, _ => 0

def dfsFrameTransitions (p q : List alpha) : Nat :=
  (p.length - commonPrefixLength p q) +
    (q.length - commonPrefixLength p q)

def dfsGapFrameWork (I : FiniteRegularPathInstance alpha)
    (p q : List alpha) : Nat :=
  dfsFrameTransitions p q * (I.outBound + 1)

inductive DfsEvent (alpha : Type) where
  | enter (pfx : List alpha)
  | query (pfx : List alpha) (w : alpha) (answer : Bool)
  | resume (pfx : List alpha)
  | output (path : List alpha)
  | exit (pfx : List alpha)
deriving DecidableEq

def outputsOfTrace : List (DfsEvent alpha) → List (List alpha) :=
  List.filterMap fun
    | .output p => some p
    | _ => none

def DfsEvent.isWork : DfsEvent alpha → Bool
  | .enter _ | .query _ _ _ | .resume _ => true
  | .output _ | .exit _ => false

def traceWork (events : List (DfsEvent alpha)) : Nat :=
  (events.filter DfsEvent.isWork).length

def scanTrace (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) (fuel : Nat) (pfx : List alpha)
    (childTrace : alpha → List (DfsEvent alpha)) :
    List alpha → List (DfsEvent alpha)
  | [] => []
  | w :: ws =>
      let answer := oracle.query pfx w
      .query pfx w answer ::
        if answer then
          childTrace w ++ .resume pfx ::
            scanTrace I oracle fuel pfx childTrace ws
        else
          scanTrace I oracle fuel pfx childTrace ws

def dfsTrace (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) :
    Nat → List alpha → List (DfsEvent alpha) :=
  Nat.rec
    (fun pfx => .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx] else []) ++ [.exit pfx])
    (fun fuel child pfx => .enter pfx ::
      (if pfx.getLast? = some I.target then [.output pfx]
       else scanTrace I oracle fuel pfx (fun w => child (pfx ++ [w]))
         (orderedAdmissibleSuccessors I pfx)) ++ [.exit pfx])

def enumerateRegularPathsTrace (I : FiniteRegularPathInstance alpha)
    (oracle : ExactReachabilityOracle I) : List (DfsEvent alpha) :=
  dfsTrace I oracle (Fintype.card alpha) [I.source]

inductive WorkProfile (alpha : Type) where
  | silent (work : Nat)
  | emitting
      (before : Nat)
      (first : List alpha)
      (rest : List (Nat × List alpha))
      (after : Nat)
deriving DecidableEq

def WorkProfile.outputs : WorkProfile alpha → List (List alpha)
  | .silent _ => []
  | .emitting _ first rest _ => first :: rest.map Prod.snd

def WorkProfile.addBefore (k : Nat) : WorkProfile alpha → WorkProfile alpha
  | .silent work => .silent (k + work)
  | .emitting before first rest after =>
      .emitting (k + before) first rest after

def WorkProfile.append : WorkProfile alpha → WorkProfile alpha → WorkProfile alpha
  | .silent a, .silent b => .silent (a + b)
  | .silent a, .emitting before first rest after =>
      .emitting (a + before) first rest after
  | .emitting before first rest after, .silent b =>
      .emitting before first rest (after + b)
  | .emitting before1 first1 rest1 after1,
      .emitting before2 first2 rest2 after2 =>
      .emitting before1 first1
        (rest1 ++ (after1 + before2, first2) :: rest2) after2

def workProfile : List (DfsEvent alpha) → WorkProfile alpha
  | [] => .silent 0
  | e :: events =>
      match e with
      | .output p =>
          (WorkProfile.emitting 0 p [] 0).append (workProfile events)
      | .enter _ | .query _ _ _ | .resume _ =>
          (workProfile events).addBefore 1
      | .exit _ => workProfile events

def WorkProfile.gapWork : List (Nat × List alpha) → Nat
  | [] => 0 | (gap, _) :: rest => gap + gapWork rest
def WorkProfile.totalWork : WorkProfile alpha → Nat
  | .silent work => work
  | .emitting before _ rest after =>
      before + gapWork rest + after

def lastProfileOutput (first : List alpha) : List (Nat × List alpha) → List alpha
  | [] => first
  | (_, q) :: rest => lastProfileOutput q rest

def ProfileGapsBound (I : FiniteRegularPathInstance alpha) :
    List alpha → List (Nat × List alpha) → Prop
  | _, [] => True
  | p, (gap, q) :: rest =>
      gap ≤ dfsGapFrameWork I p q ∧ ProfileGapsBound I q rest

def ProfileBound (I : FiniteRegularPathInstance alpha) (root : List alpha) :
    WorkProfile alpha → Prop
  | .silent work => work ≤ I.outBound + 1
  | .emitting before first rest after =>
      before ≤ (first.length - root.length + 1) * (I.outBound + 1) ∧
      ProfileGapsBound I first rest ∧
      after ≤ ((lastProfileOutput first rest).length - root.length) *
        (I.outBound + 1)

end RegularPathDelay

namespace PalomarRegularPathDelay

open RegularPathDelay

theorem exact_prefix_deletion_extension
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) {pfx : List alpha} {v w : alpha}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hedge : I.Edge v w)
    (hsurvives : Survives I.bar pfx w) :
    HasRegularExtension I pfx w ↔ DeletedCompletion I pfx w := by
  sorry

theorem exact_oracle_regular_extension
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I)
    {pfx : List alpha} {v w : alpha}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hw : w ∈ orderedAdmissibleSuccessors I pfx) :
    oracle.query pfx w = true ↔ HasRegularExtension I pfx w := by
  sorry

theorem ordered_fixed_endpoint_enumerator
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I) :
    (∀ p, p ∈ enumerateRegularPaths I oracle ↔ IsTargetRegularPath I p) ∧
    (enumerateRegularPaths I oracle).Nodup ∧
    (∀ p ∈ enumerateRegularPaths I oracle,
      p.length ≤ Fintype.card alpha) := by
  sorry

/-- Exact operational delay certificate.  `workProfile` extracts the actual
work counts before the first output, between every consecutive output pair,
after the final output, or for the complete no-output run. -/
theorem explicit_dfs_event_trace_certificate
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I) :
    let events := enumerateRegularPathsTrace I oracle
    let profile := workProfile events
    profile.totalWork = traceWork events ∧
      profile.outputs = enumerateRegularPaths I oracle ∧
      ProfileBound I [I.source] profile ∧
      events.getLast? = some (.exit [I.source]) := by
  sorry

end PalomarRegularPathDelay
