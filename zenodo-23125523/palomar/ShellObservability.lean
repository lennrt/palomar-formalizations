module

public import ShellObservability.HypercubeReduction
public import ShellObservability.BishopUpper
public import ShellObservability.DefectSyndrome
public import ShellTomography.Foundations
public import ShellObservability.CycleShell
public import ShellObservability.Robust
public import ShellObservability.LowerBound
public import ShellObservability.GridRecovery
public import ShellObservability.GridTrades
public import ShellObservability.GridTheorems
public import ShellObservability.GridMomentRecovery
public import ShellObservability.PetersenCounterexample
public import ShellObservability.PetersenSecond
public import ShellObservability.FractionalCounterexample
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Tactic

@[expose] public section

/-!
Entry point for the shell-observability formalization.
The imported foundations come from the distance-shell
 tomography companion artifact (DOI 10.5281/zenodo.22404456).
Their module interfaces are ported to the pinned Lean version; mathematical
definitions and proofs are retained. See formalization.yaml for source attribution.
-/
