/-
Paper: Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric Digraphs
Authors: Lennart Rudolph, Sol, Fable
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21892986
Preprint published: 2026-08-11. Palomar formalization upgraded: 2026-08-20.
-/

import RegularPathDelayTrace

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
  exact RegularPathDelay.prefix_extension_iff_deleted_completion
    I hpfx hlast hedge hsurvives

theorem exact_oracle_regular_extension
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I)
    {pfx : List alpha} {v w : alpha}
    (hpfx : IsRegularPrefix I pfx)
    (hlast : pfx.getLast? = some v)
    (hw : w ∈ orderedAdmissibleSuccessors I pfx) :
    oracle.query pfx w = true ↔ HasRegularExtension I pfx w := by
  exact RegularPathDelay.oracle_accepts_iff_regular_extension
    I oracle hpfx hlast hw

theorem ordered_fixed_endpoint_enumerator
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I) :
    (∀ p, p ∈ enumerateRegularPaths I oracle ↔ IsTargetRegularPath I p) ∧
    (enumerateRegularPaths I oracle).Nodup ∧
    (∀ p ∈ enumerateRegularPaths I oracle,
      p.length ≤ Fintype.card alpha) := by
  exact RegularPathDelay.enumerateRegularPaths_specification I oracle

theorem explicit_dfs_event_trace_certificate
    {alpha : Type} [DecidableEq alpha] [Fintype alpha]
    (I : FiniteRegularPathInstance alpha) (oracle : ExactReachabilityOracle I) :
    let events := enumerateRegularPathsTrace I oracle
    let profile := workProfile events
    profile.totalWork = traceWork events ∧
      profile.outputs = enumerateRegularPaths I oracle ∧
      ProfileBound I [I.source] profile ∧
      events.getLast? = some (.exit [I.source]) := by
  exact RegularPathDelay.explicit_dfs_event_trace_certificate I oracle

end PalomarRegularPathDelay
