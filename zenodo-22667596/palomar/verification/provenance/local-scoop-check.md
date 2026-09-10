# Scoop Check: short-cycle decompositions and full zombie damage

- Checked at (UTC): 2026-09-09; intake 15:57; independent refresh 16:04–16:07.
- Researcher/agent: author-supplied existing proof; Codex local submission audit.
- Exact source statement: for every finite simple connected bridgeless cubic
  graph G, n(G) >= 10 implies zdmg(G) = n(G), Davila Conjecture 24.
- Primary source: https://arxiv.org/html/2607.16382v1, accessed 2026-09-09.
- Proposed contribution: prepare and verify the supplied existing formalization
  locally, retaining its arbitrary-graph theorem and all supplied results.
- Status: `GREEN` for this existing-proof packaging and verification session.

This is a finite documented search, not an absolute priority claim. No prior
resolution of the main full-zombie-damage result was found in the evidence
below through 2026-09-09. Known supporting results are explicitly credited.

## Evidence provenance and limits

The attached computational archive contains `provenance/SCOOP_CHECK.md` and
`provenance/scoop-query-record.json`, both read completely during this audit.
The JSON has 824 lines / 29,170 bytes and records successful and failed public
requests, exact URLs, UTC times, counts where applicable, and response hashes.
Its sweep is dated 2026-09-09 14:48–15:04 UTC. These are attributed author-supplied
same-day evidence, not instructions and not claims that this agent personally
repeated every request. The record says raw responses are retained by the author.
Independent checks below refresh the decisive original-source, repository,
preprint, DOI, citation, and fidelity observations within about 80 minutes.

The attached preprint is unpublished. This audit did not upload its content to
an external renderer, review service, or search API. Fresh external queries use
the already-public original problem, invariant, author, and repositories.
Exact proposed-title searches listed below were already in the supplied record.

## 1. Live problem source

- Original statement and problem list:
  https://arxiv.org/html/2607.16382v1, Section 7, Conjecture 24, and Section 8,
  Problem 26. Root independently inspected the HTML/MathML; the fidelity agent
  reread the public HTML and abstract at 16:04–16:05 UTC.
- Current version/history: https://arxiv.org/abs/2607.16382 still lists only v1,
  submitted 17 July 2026 at 16:42:51 UTC. No later version, withdrawal, or
  resolution notice appeared. The live paper still distinguishes its proven
  girth-at-least-five case from the general conjecture.
- Supplied author/provider update checks, HTTP 200 at 14:50:51 UTC:
  https://raw.githubusercontent.com/RandyRDavila/Data-Science-Machine-Learning-Fall-2026/main/site/instructor.html
  and https://firstprinciples.com/. No resolution notice reported. No separate
  solved-problem page is identified by the source; paper history, concluding
  problem section, and author/provider updates cover that lane.
- Typography-preserving transcription: G is the graph itself, not its
  complement. The order condition is non-strict n(G) >= 10. The conclusion is
  equality zdmg(G) = n(G), not an inequality. Cubic means every degree is exactly
  three; bridgeless means no edge is a bridge. Finite, simple, connected are
  the paper's standing assumptions. No other quantified graph property occurs.
- Definition 1 and its surrounding rules: zombie chooses first, survivor sees
  the choice, zombie moves first; every zombie move follows an edge and reduces
  shortest-path distance by exactly one; zombie ties are adversarial; survivor
  may move along an edge or pass; damage counts distinct departure sources after
  a survived zombie turn, not arrival vertices.
- Result: current original source and exact mathematical reading confirmed.

## 2. Current upstream repository

- Author repository inventory in supplied record:
  https://api.github.com/users/RandyRDavila/repos?per_page=100&sort=updated
  returned 35 public repositories at 14:50:50 UTC. The relevant upstream is
  https://github.com/RandyRDavila/TxGraffiti2.
- Default head independently confirmed at 16:04 UTC using
  https://api.github.com/repos/RandyRDavila/TxGraffiti2/commits/main:
  `e37126da53b84150d142a5d61202b61f78521fcc`, commit date 2026-01-07,
  message “bumped version to v0.4.1”. Same head as supplied sweep.
- Supplied complete tree, branch list and recent 100 commits:
  https://api.github.com/repos/RandyRDavila/TxGraffiti2/git/trees/main?recursive=1,
  https://api.github.com/repos/RandyRDavila/TxGraffiti2/branches?per_page=100,
  https://api.github.com/repos/RandyRDavila/TxGraffiti2/commits?per_page=100.
  Tree/branch/commit inspection found no resolution; 30 branch names were
  returned, including the existing Lean-export/development branches.
- Supplied all-state search queries: `user:RandyRDavila zombie is:pr`,
  `user:RandyRDavila zombie is:issue`, and the analogous `zdmg` queries, at
  https://api.github.com/search/issues. No equivalent proof reported.
- Independent 16:04–16:05 refresh searched `zombie` and `zdmg` in title/body,
  scoped to `user:RandyRDavila` plus the two formalization repositories below,
  with `is:pr` and `is:issue` separately and no state restriction: all four
  searches returned total_count 0. A query initially lacking the now-required
  type qualifier returned HTTP 422; the corrected searches succeeded.
- Independent https://api.github.com/search/code query
  `zombie user:RandyRDavila` found only `site/instructor.html`, the publication
  listing, at `c5000e713939eeaf6267d61fca631019d7dae111`. No proof code found.
- Independent https://api.github.com/search/commits query `zombie`, scoped to
  these same owner/repositories, returned total_count 0. Supplied commit searches
  additionally used `zdmg` and `2607.16382`.
- Result: no upstream code resolution found; live upstream head checked.

## 3. General web exact searches

- Supplied same-day sweep: exact original title “The Zombie Damage Number of
  a Graph”; exact supplied preprint title; “Conjecture 24”, Randy Davila,
  “zombie damage”, “bridgeless cubic”, `zdmg`, and `2n(n+1)`. Negative for a
  substantially equivalent resolution. URLs and related-source leads are in
  the attached query record; the narrative attributes the search outcome.
- Independent public web queries at 16:04 UTC:
  `"zombie damage" "Conjecture 24"`,
  `"zombie damage" bridgeless cubic proof`,
  `"Davila" "zombie damage" solved`, and `"zdmg" "2n(n+1)"`.
  Results included the original arXiv preprint and its author-uploaded
  ResearchGate copy; other results were unrelated video-game/DNS uses.
  No independent resolution was returned.
- Root separately searched the public Conjecture-24/zombie/cubic/Davila
  resolution terms during intake; likewise no new resolution found.
- Result: no competing public theorem located in these finite searches.

## 4. Preprint servers

- Supplied fresh arXiv API searches used
  https://export.arxiv.org/api/query with `sortBy=submittedDate`,
  `sortOrder=descending`, `max_results=100`, and queries
  `all:"zombie" AND all:"damage"`, `au:"Davila_Randy"`,
  `ti:"Short-Cycle Decompositions"`, and `ti:"damage number"`.
  Newest-results review included the August Gledel paper, not just July work.
- Independent request at 16:05:37 UTC with the first query, newest first,
  max_results 10, returned totalResults 2: Davila 2607.16382v1 and unrelated
  DNS-security paper 2605.06880v1. Thus the full matching result set was read;
  there was no newer matching mathematical preprint.
- HAL supplied and independently refreshed query:
  https://api.archives-ouvertes.fr/search/?q=%22zombie%20damage%22&wt=json&rows=100
  returned numFound 0 at 16:06 UTC.
- Gledel et al. https://arxiv.org/html/2608.15226v1 and
  https://arxiv.org/abs/2608.15226 were checked by root and in the supplied
  primary-source review: ordinary one-cop damage with unrestricted cop moves,
  not the geodesic-zombie theorem. Stojaković–Wulf
  https://arxiv.org/html/2209.10965v4 is ordinary multi-robber damage, revised
  22 June 2026, not the present objective/strategy class.
- Result: no matching preprint resolution found; recent neighboring literature
  was evaluated for the actual rules, not dismissed by title alone.

## 5. DOI and research repositories

- Supplied Crossref requests succeeded at 14:50:50–52 UTC:
  https://api.crossref.org/works?query.title=The+Zombie+Damage+Number+of+a+Graph&rows=20,
  https://api.crossref.org/works?query.bibliographic=%22zombie+damage%22&rows=50,
  and the exact supplied preprint title with query.title and rows=25.
  Fuzzy metadata hits did not disclose an equivalent result. One separate
  generic query returned HTTP 429; the successful title/bibliographic requests
  cover the query lane, and the failed request is retained in the supplied log.
- DataCite direct invariant request independently refreshed at 16:06 UTC:
  https://api.datacite.org/dois?query=%22zombie%20damage%22&page%5Bsize%5D=100
  returned total 1, the original `10.48550/arxiv.2607.16382`, and no other record.
- Supplied DataCite exact supplied-title search returned 0. Query
  `"subcubic" AND ("triangles" OR "quadrilaterals")` returned 11 records;
  the listed titles concern algorithmic subcubic running times, triangle
  detection, orientation Ramsey thresholds, or restricted 2-matchings,
  not the full-damage theorem. Exact records are retained in the supplied JSON.
- Supplied direct Zenodo API queries at 14:50:50–52 UTC:
  https://zenodo.org/api/records?q=%22zombie+damage%22&size=25,
  https://zenodo.org/api/records?q=%22The+Zombie+Damage+Number+of+a+Graph%22&size=25,
  and exact supplied-title/short-title queries all succeeded and returned 0.
  DataCite queries constrained to `client-id=cern.zenodo` for the invariant,
  original title, and supplied title also returned 0; an unrelated control DOI
  returned records, confirming that the endpoint was functioning.
- Result: both metadata and exact-title searches are covered. No equivalent DOI
  or deposit found. Zero results do not imply a reserved DOI is public, nor
  exclude unpublished or indexing-delayed work.

## 6. Scholarly literature and citations

- OpenAlex original-source forward citations:
  https://api.openalex.org/works?filter=cites%3AW7169878461&per-page=100.
  Supplied sweep and independent 16:06 UTC request returned count 0.
- Supplied OpenAlex invariant search:
  https://api.openalex.org/works?search=%22zombie+damage%22&per-page=100.
  Supplied Cushing forward-citation request
  https://api.openalex.org/works?filter=cites%3AW2772063712&per-page=100
  found nine curvature-related citations, no full-damage theorem.
- Closest structural source: Cushing et al.,
  https://arxiv.org/abs/1712.03033 and
  https://doi.org/10.1080/10586458.2019.1660740. Lemma 5.1 and Corollary 5.4
  of arXiv v2 supply the known closed cubic classification. Root checked this
  source; it is credited, not treated as a new result of the supplied paper.
- Known ring sensor bound: Sardar et al.,
  https://doi.org/10.61091/jcmcc119-17, Theorem 2, and publisher page
  https://combinatorialpress.com/jcmcc-articles/volume-119/computing-metric-dimension-of-two-types-of-claw-free-cubic-graphs-with-applications/.
  Supplied OpenAlex and Semantic Scholar metadata/citation checks succeeded;
  this bound is credited supporting material.
- Primary-source comparisons in supplied same-day full-text review:
  Cox–Sanaei https://ajc.maths.uq.edu.au/pdf/75/ajc_v75_p001.pdf;
  Liu–Miller https://doi.org/10.4230/LIPIcs.FUN.2026.30 and its publisher HTML;
  Gledel and Stojaković–Wulf as in lane 4;
  Huggan–Messinger–Porter https://ajc.maths.uq.edu.au/pdf/88/ajc_v88_p362.pdf
  together with https://ajc.maths.uq.edu.au/pdf/91/ajc_v91_p217.pdf.
  Ordinary damage permits unrestricted cop movement; zombie capture/throttling
  has a different objective. None is a theorem about this full-zombie-damage
  characterization under the same hypotheses.
- Semantic Scholar original-paper request returned HTTP 429; successful
  OpenAlex citation access supplies the citation lane. A ResearchGate lead to
  “From Counterexamples to Theorems: The Theo-Conjecture Loop in Scientific
  Discovery” describes methodology and quantum-information/brane-tiling cases;
  supplied full-text attempt returned HTTP 403. No full-text review or absence
  claim about that inaccessible text is made; its available description
  advertises no competing cubic-game result.
- Result: no substantially equivalent theorem located in the citation or
  neighboring-literature trail. Known overlapping supporting results retained
  with attribution rather than promoted as new.

## 7. Formalization repositories

- Current repositories: https://github.com/google-deepmind/formal-conjectures
  and https://github.com/leanprover-community/mathlib4.
- Supplied successful 14:50 UTC requests covered recursive default-branch
  trees, branch-name lists and recent 100 commits through the corresponding
  `/git/trees/main?recursive=1` (formal-conjectures),
  `/git/trees/master?recursive=1` (Mathlib), `/branches?per_page=100`, and
  `/commits?per_page=100` GitHub API endpoints. Mathlib tree SHA was
  `a4c8ef0a69f52ec80525d5086bb3542f4660faaf`. These are live requests, not
  frozen benchmark snapshots. Branch inspection is a finite branch-name
  search, not a claim that every branch's full contents were downloaded.
- All-state supplied PR/issue searches used `zombie`, with repository scope;
  only unrelated older Mathlib PRs 19343 and 2838 were noted. The independent
  16:04–16:05 typed searches for both `zombie` and `zdmg`, scoped to these
  repositories plus the author, returned 0 current search hits. No state
  restriction excluded merged or closed work. Commit search returned 0.
- Independent GitHub code searches at 16:05 UTC:
  `zombie repo:google-deepmind/formal-conjectures` returned 0;
  `zombie repo:leanprover-community/mathlib4` returned one unrelated
  `scripts/verify_version_tags.py` use at
  `42a3845c6d7ec6866eefa4cc327a306a0c4a7d3c`.
  An initial combined code query failed parsing; these separate corrected
  queries succeeded. Neither hit is an equivalent formal statement or proof.
- Result: no equivalent public formalization located in these current
  repository, statement-file, PR, issue, commit, and branch searches.

## 8. Local duplication sweep

- Root's 2026-09-09 intake searched `RESEARCH_LEDGER.md`, `scoop_checks/`,
  `palomar-repository/` Markdown, and repository filenames for `zombie`,
  `short-cycle`, `Davila`, and `Conjecture 24`. No prior separate local target
  or closed lane was found in this checkout; the current INTAKE is this work.
- Supplied wider author-side duplication inventory: 370,713 files and 171 ZIPs;
  589 matching text paths and 462 matching archive members all belonged to this
  work, its inputs, or its preparation. This is attributed supplied evidence,
  not a claim of another scan over the user's entire disk by this agent.
- All attached ZIPs were checked for CRC, traversal, symlinks and conflicting
  duplicate paths before extraction: 413 members across three archives.
- Source version: supplied v1.0.0, DOI 10.5281/zenodo.22667596, 9 September 2026.
- Lean ZIP SHA256:
  `cfaf883855f94ae2a5c666eba5e3a8966ce6b1c76c769dffb566719a3c3627ba`.
- Result: no independent local duplicate or forbidden reopened lane found.

## Equivalence and source-to-Lean audit

Read the attached mathematical body and source, and visually inspected complete
PDF pages 1–17 including all main statements, the composition/initialization
proofs, game conventions, formalization scope, and DOI. No formula clipping or
typographical ambiguity affected the reading. The main predicate was compared
term by term before changing the submission interface:

| Preserved source term | Actual Lean representation and audit result |
|---|---|
| finite simple graph | `V`, `[Fintype V]`, `G : SimpleGraph V`; literal adjacency in `gameGraph` |
| connected | `G.Connected`, including nonempty graph |
| cubic | `∀ v, G.degree v = 3`; equality, not maximum-degree bound |
| bridgeless | `∀ u v, G.Adj u v → ¬ G.IsBridge s(u,v)` |
| n >= 10 | `10 ≤ Fintype.card V` in both conjecture corollaries |
| zdmg(G) = n | literal numerical equality in `davila_conjecture_24_damage_number`; proved bridge to `FullDamage` |
| zombie starts first and moves first | `∀ z, ∃ v, z ≠ v ∧ ForcesWithin ... .zombie (initial z v)` |
| every geodesic reply | minimum `Walk` length definition, universal reply continuation, nonempty reply set |
| survivor pass and source damage | `LegalSurvivor`; `State.survivorTo` adds the departure source to a set |
| four exceptions | exact finite graph definitions and graph isomorphisms for K4, K3,3, triangular prism, cube |
| explicit bound | `2 * Fintype.card V * (Fintype.card V + 1)`, counting survivor moves |
| infinite recurrent coverage | one fixed controller, all legal replies safe, every vertex is a departure beyond every finite time |

The classification uses actual Mathlib short cycles, all-order attachment
induction, and bijective adjacency-reflecting catalogue embeddings. Its
one-port alternative is explicit and is then ruled out from bridgelessness.
Actual component models, identified external stubs, local strategies, quotient
paths, the twice-order service bound, and original-start initialization are
constructed by the proof chain. No classification, routing, initialization,
or full-damage premise is hidden in the main theorem's hypotheses.

Omitting moves onto the occupied zombie vertex has a proved exact equivalence
for damaged-set objectives. The finite numerical value/threshold/eventual
interfaces are also proved. These are disclosed representation choices, not
assumptions of the intended conclusion. A simple quotient is formed only after
deleting the original entering edge; parallel original witnesses and loop ports
remain correctly handled by ambient routing.

The paper's entirely general degree-independent interface theorem and the
ring's structural connection to recurrent coverage remain written results;
Lean proves the complete cubic-game application directly and separately proves
the ring sensor obstruction. Historical Davila regressions and census counts
are tests, not formal theorem claims. These scope boundaries are explicit.

The found prior results do not imply the full theorem: Davila's girth theorem
excludes short cycles; known closed cubic classification gives no game strategy;
ordinary-cop damage and capture-only zombie results change the strategy class
or payoff. Known closed classification and sensor bounds are not novelty claims.

Research interest is supported by the actual arbitrary-graph characterization,
explicit all-order move bound, recurrent coverage, and universal short-cycle
structure, with structural-graph and pursuit-game expert audiences. This is
an assessment of the supplied mathematics, not a promised Palomar decision.

## Decision

- Final status: `GREEN` for local packaging and verification of this existing
  proof. Every required lane has current documented evidence; the decisive
  source, version, statement, repository, preprint, DOI and citation checks
  were independently refreshed, and source fidelity was directly audited.
- No prior resolution of the main theorem was found in this documented finite
  sweep through 2026-09-09. This sentence does not claim exhaustive priority.
- Residual uncertainty: unpublished/indexing-delayed work, finite repository
  search coverage, Semantic Scholar rate limiting covered by OpenAlex, and
  the inaccessible methodology-overview full text. No positive indication of
  an equivalent result arose from those residual limits.
- Palomar acceptance is separate: the supplied Challenge imports local proof
  modules and must be reconstructed with permitted imports; the subsequent
  mechanical, rendering, and editorial checks still have to be completed.
- Required recheck: repeat the full gate immediately before any new abstract
  drafting and before public submission, and on a changed source, scope,
  delayed submission, or new competing evidence. No submission occurs here.
- Exclusion ledger: no new exclusion; known supporting results are credited.

## Session outcome (2026-09-09, local preparation)

The package is prepared at
`palomar-formalizations/zenodo-22667596/palomar`. All 135 supplied library
sources remain unchanged. The replacement Challenge independently states all
42 results using only permitted imports. Thirteen transparent interfaces
(direct applications of the original results) avoid Palomar's documented
renderer alias bug #134; no mathematical result or hypothesis was removed.
All 42 comparisons, the additional 24-game comparison, 276 transitive axiom
checks, the official core-notation audit, Verso and sanitizer pass locally.
The exact logs, pins, source hashes, coverage limits and no-submission caveat
are in `verification/local-2026-09-09/` and `VERIFICATION.md` in that project.
No new abstract or mathematics was invented; the metadata accurately describes
the supplied existing proof and its two written-only boundaries. No commit,
push, hosted review, registration or unpublished-content upload occurred.
