# Polynomial-Delay Enumeration of Fixed-Endpoint Vertex-Regular Paths

DOI: [10.5281/zenodo.21892986](https://doi.org/10.5281/zenodo.21892986)

Author: Lennart Rudolph ([ORCID 0009-0009-0198-085X](https://orcid.org/0009-0009-0198-085X))

Authors: Lennart Rudolph, Sol, Fable

- `palomar/` is the independent Lean project prepared for Palomar submission.

The Palomar entry formalizes exact prefix-deletion completion semantics and a
sound, complete, duplicate-free ordered oracle-pruned enumerator. Its upgraded
delay result is based on an executable streaming DFS event list—not a bound on
an abstract pair of paths. Frame entry, each successor query, parent resume,
output, and frame exit are explicit. The output projection is proved equal to
the enumerator, and the work profile extracted from the trace supplies the
actual no-output, first-output, consecutive-output, and post-last-output
interval counts. Consecutive-output work is bounded through the paths' longest
common prefix.

One exact reachability query is still a charged unit. The
Goldberg--Karzanov `O(|V|+|E|)` implementation and its runtime proof, the
derived executable wall-clock delay theorem, and the paper's space bound are
external and are not formalized or claimed.
