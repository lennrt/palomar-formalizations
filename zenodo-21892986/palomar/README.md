# Exact regular-path enumeration — Palomar project

Authors: Lennart Rudolph, Sol, Fable

This Lean project formalizes the recursive core of *Polynomial-Delay
Enumeration of Fixed-Endpoint Vertex-Regular Paths in Skew-Symmetric
Digraphs* ([DOI 10.5281/zenodo.21892986](https://doi.org/10.5281/zenodo.21892986)).

The first three compared results prove the prefix-deletion completion
equivalence, correctness of the exact Boolean completion oracle on ordered
admissible successors, and sound/complete/duplicate-free bounded-depth
enumeration of all fixed-endpoint vertex-regular paths.

The upgraded fourth result is operational. It defines a streaming DFS trace
with explicit frame-enter, individual successor-query, frame-resume, output,
and frame-exit events. Lean proves that:

- projecting output events gives exactly `enumerateRegularPaths`;
- the profile extracted from the event list has total work equal to the
  number of enter/query/resume events;
- a complete no-output run uses at most `outBound + 1` work events;
- work through the first output and after the last output obeys the relevant
  descent/retreat-depth bounds;
- every actual interval between consecutive output events is bounded by the
  retreat/descent distance through their longest common prefix, multiplied by
  `outBound + 1`; and
- the event list terminates with the root frame's exit event.

These are combinatorial event counts, not machine-step bounds. One exact
oracle query remains a unit-cost event in Lean. Goldberg--Karzanov's cited
`O(|V|+|E|)` regular-reachability implementation, the derived wall-clock
polynomial-delay theorem, and the paper's space analysis remain external and
are not claimed.

The four compared declarations are listed in `comparator.json`. Their checked
axiom surface is limited to `propext`, `Quot.sound`, and (for the bundled
enumeration/trace results) `Classical.choice`; there are no proof holes.
