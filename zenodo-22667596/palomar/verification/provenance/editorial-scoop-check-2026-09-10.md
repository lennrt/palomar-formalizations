# Scoop Check: full zombie damage — editorial-scope repair

- Checked at (UTC): 2026-09-10, 01:10–01:15.
- Researcher/agent: Codex, current public-source refresh for the author's existing proof.
- Exact source statement: every finite connected simple bridgeless cubic graph
  G of order n(G) >= 10 satisfies zdmg(G) = n(G), Davila Conjecture 24.
- Primary source URL: https://arxiv.org/html/2607.16382v1; accessed 2026-09-10.
- Proposed contribution: repair the selected-result scope and its description
  for the existing formalization, without developing a new theorem or making
  a fresh mathematical priority claim.
- Status: `GREEN` for this existing-proof editorial-repair session.

No competing prior resolution of the main theorem was found in the documented
finite sweep through 2026-09-10 01:15 UTC. This is not an absolute priority claim.
The author's now-public proof is the work being repaired, not a competing result.
The root agent recorded this session's INTAKE in `RESEARCH_LEDGER.md` before
substantive changes. The previous full record and `TEMPLATE.md` were read in full.

## 1. Live problem source

- Current statement, surrounding hypotheses, game definitions and concluding
  problem section: https://arxiv.org/html/2607.16382v1. HTTP 200 at
  01:12:21 UTC; HTML SHA256
  `3e76417defbf41fb1e8289a903100b414d9fb2043a122401d508cd15d291e18e`.
- Typography-preserving verification used the actual HTML source's MathML and
  TeX annotations, not plain-text extraction alone. `Thmtheorem24.p1.m2` has
  `n(G)\\geq 10` and MathML `≥`; `S7.Ex36.m1` has
  `\\operatorname{zdmg}(G)=n(G).` and MathML equality. There is no complement,
  overline, superscript, hidden negation, or strict inequality in this statement.
- Section 2 supplies finite, simple and connected as standing assumptions.
  Cubic is exact degree three; bridgeless excludes every bridge. Quantification
  is over every such graph, not a finite census. The zombie acts first, cannot
  pass and takes an adjacent distance-decreasing step; all ties remain its
  choice. Survivor passes are permitted, and damage counts distinct departure
  sources after surviving the preceding zombie turn.
- Live history: https://arxiv.org/abs/2607.16382 lists only v1, submitted
  2026-07-17 16:42:51 UTC. No revised version or withdrawal was shown. Section 7
  still separates the proven girth-at-least-five case from the short-cycle case;
  Section 8 repeats the general characterization question. No separate solved
  page is linked, so current history, concluding section and author updates
  were checked, rather than treating an old open marker as decisive evidence.
- Author update page, HTTP 200 at 01:12:21:
  https://raw.githubusercontent.com/RandyRDavila/Data-Science-Machine-Learning-Fall-2026/main/site/instructor.html
  still lists the original zombie-damage paper as submitted in 2026. Also
  lists *Cops and Zombies in Claw-Free Graphs* with Henning, a different capture
  objective. No resolution notice found. Provider https://firstprinciples.com/
  returned HTTP 200; no zombie/zdmg/solved/resolved match in the returned page.
- Result: source and exact mathematical reading confirmed; no new source
  ambiguity. The formal hypotheses were reread term by term below.

## 2. Current upstream repository

- Repository: https://github.com/RandyRDavila/TxGraffiti2.
- Default head at 01:12:21 UTC:
  `e37126da53b84150d142a5d61202b61f78521fcc`, dated 2026-01-07,
  “bumped version to v0.4.1”. Same head as the previous session.
- Successful live endpoints under `https://api.github.com/repos/RandyRDavila/TxGraffiti2`:
  `/commits/main`, `/git/trees/main?recursive=1`, `/branches?per_page=100`,
  `/commits?per_page=100`. The complete tree returned 590 paths, not truncated;
  30 branches were returned, including `rrd-lean4-export-module` and
  `rrd-lean4-upgrade-v1`; newest 100 commits were searched. No zombie/zdmg/
  Conjecture-24/formula branch or path indicated a proof. Davila-named paths
  are the package's pre-existing heuristic and processing code.
- Current GitHub code search (connected read-only search) queried `zombie`
  and `zdmg` in `repo:RandyRDavila/TxGraffiti2`: both zero. Broader owner-scoped
  queries used `"Conjecture 24"`, `"The Zombie Damage Number"`, and
  `"2n(n+1)"`. Exact-title search found only the instructor publication list;
  formula search returned zero. Number search found unrelated generated
  independence/chromatic/zero-forcing conjectures in `Conjecturing.jl/README.md`
  and `TxGraffiti/graph_conjectures.ipynb`, not the target invariant.
- All-state owner-scoped PR searches used `zombie`, `zdmg`, the title fragment,
  number and formula. Only the number search returned hits: GraphCalc PR 24
  adds burning/clique-cover numbers and TxGraffiti2 PR 24 is the JOSS paper.
  All-state issues similarly found only GraphProperties.jl issue 24 (docstrings).
  These literal-number collisions are not equivalent statements.
- Independently scoped REST searches at 01:14:08–09 UTC, via
  `https://api.github.com/search/issues?q=TERM+repo:RandyRDavila/TxGraffiti2+is:TYPE&per_page=100`,
  with TERM `zombie`/`zdmg` and TYPE `pr`/`issue`, returned zero in all four cases.
  No state filter excluded merged, closed or open work.
- Commit searches at `https://api.github.com/search/commits`, each with
  `q=TERM repo:RandyRDavila/TxGraffiti2&per_page=100`, for `zombie`, `zdmg`,
  `2607.16382`, all returned zero. Owner-wide `zombie` commit search also zero.
- Result: no upstream resolution found in this live, finite search. Branch
  coverage is branch-name inventory plus current-head contents, not a claim
  that every historical branch's entire contents were downloaded.

## 3. General web exact searches

All queries below were run on the public web on 2026-09-10, 01:11–01:14 UTC:

- `"Short-Cycle Decompositions and Full Zombie Damage in Cubic Graphs"`:
  a separate exact query returned no results.
- `"The Zombie Damage Number of a Graph" "Conjecture 24"` and
  `"zombie damage" "Conjecture 24" solution`: original paper and its
  author-uploaded ResearchGate copy; no competing resolution.
- `"Davila" "zombie damage" solved`: original/neighboring work plus unrelated
  names and zombie terminology; no competing theorem.
- `"zdmg" "2n(n+1)"`: no relevant mathematical result; unrelated token matches.
- `"zombie damage" "bridgeless cubic"`: original conjecture material.
- `"Short-Cycle Decompositions" "Rudolph"`: no competing result.
- `"full zombie damage" cubic proof`: no competing mathematical theorem;
  primarily unrelated video-game results.
- Result: no substantially equivalent independent theorem located. Search
  indexing may lag the author's newly pushed public formalization.

## 4. Preprint servers

- Current arXiv API endpoint https://export.arxiv.org/api/query, with
  `sortBy=submittedDate&sortOrder=descending&max_results=100`, accessed
  successfully at 01:12:22–23 UTC. Query and complete matching set counts:
  - `all:"zombie" AND all:"damage"`: 2, original 2607.16382v1 and unrelated
    DNS-security 2605.06880v1; no later mathematical result.
  - `au:"Davila_Randy"`: 36, newest 2608.05972v1 (decoherence kernels), then
    2608.04040v2 (common-divisor graph residues), then original zombie paper.
    All returned titles and dates inspected; no later resolution found.
  - `ti:"Short-Cycle Decompositions"`: 1, 1805.12051v1, graph sparsification/
    spectral sketches/resistance computation; not a pursuit-game theorem.
  - `ti:"damage number"`: 5; newest 2608.15226v1 (15 August 2026), then original
    zombie paper, 2308.09645v2, 2209.10965v4, 2205.06956v1.
- HAL: https://api.archives-ouvertes.fr/search/?q=%22zombie+damage%22&wt=json&rows=100
  returned HTTP 200 and numFound 0 at 01:12:23 UTC.
- Current primary-source abstracts/history for
  https://arxiv.org/abs/2608.15226 and https://arxiv.org/abs/2209.10965 were
  inspected again. Gledel et al. study ordinary-cop damage, not geodesic-zombie
  moves; Stojaković–Wulf study multi-robber ordinary damage, latest v4 June 2026.
  Their payoffs/strategy classes do not assert the target theorem.
- Result: newest matching preprint sets and a relevant other server covered;
  no independent matching resolution located.

## 5. DOI and research repositories

- Crossref, all HTTP 200 at 01:12:23–24 UTC:
  https://api.crossref.org/works with `query.title` equal to the complete
  original title and the complete Rudolph title, `rows=20`; additionally
  `query.bibliographic="zombie damage"&rows=30`. All returned titles inspected.
  Fuzzy totals are not exact-match counts. Original-title search returned
  capture-only zombie-number literature, multi-robber damage and unrelated
  records; proposed-title search returned cycle-cover/decomposition papers,
  not a full-damage strategy. Metadata query was mostly unrelated zombie uses.
- DataCite: https://api.datacite.org/dois with `page[size]=100`; query
  `"The Zombie Damage Number of a Graph"` returned one record,
  `10.48550/arxiv.2607.16382`; `"zombie damage"` returned the same one;
  the complete quoted Rudolph title returned zero. HTTP 200 at 01:12:23–24.
- Direct Zenodo endpoint https://zenodo.org/api/records was queried for all
  three quoted strings above with size=25: HTTP 504 for all three. Retried
  with size=1 at 01:14:07: all three read timeouts. Public search UI
  https://zenodo.org/search?q=%22zombie%20damage%22 likewise failed to load.
  These failures are access failures, NOT negative search results.
- Current successful Zenodo alternatives:
  https://api.datacite.org/dois with `client-id=cern.zenodo&page[size]=100`
  and each of the three quoted queries above returned HTTP 200 and zero
  registered records at 01:14:07–08. These are live searches of Zenodo's DOI
  metadata index, not an assertion of live access to the Zenodo API.
- Independently searched the web index with `site:zenodo.org` plus each
  quoted full title and `"zombie damage"`. Both exact full-title queries
  returned no results in a separate query. The invariant query found unrelated
  senescence, fiction and computer-security deposits, no mathematical theorem.
- Result: required repository lane covered by current Zenodo-index metadata
  and exact-title/site-index searches despite the direct outage. Residual
  uncertainty includes indexing delays and not-yet-registered deposits. The
  author's DOI 10.5281/zenodo.22667596 is not treated as published by zero hits.

## 6. Scholarly literature and citations

- OpenAlex https://api.openalex.org/works with `filter=cites:W7169878461&per-page=100`
  returned zero at 01:12:24 UTC. The duplicate original-paper record
  `W7170112857` was also checked, same filter at 01:14:12, zero.
- `search="zombie damage"&per-page=100` returned four records: two versions
  of the original paper and unrelated enterprise/DNS papers; no independent
  full-damage theorem.
- `filter=cites:W2772063712&per-page=100` returned nine Cushing-source
  forward citations at 01:12:25, all curvature/Ricci/rigidity related. No
  zombie-damage theorem appears among them. Titles, DOIs and dates inspected.
- Closest structural primary source refreshed:
  https://arxiv.org/abs/1712.03033, latest v2 still 2017-12-22, related DOI
  https://doi.org/10.1080/10586458.2019.1660740. Cushing et al. classify cubic
  nonnegative-curvature graphs. Its known closed classification remains
  credited supporting material, not claimed new here.
- Known sensor source refreshed at the publisher, HTTP 200 at 01:14:12:
  https://combinatorialpress.com/jcmcc-articles/volume-119/computing-metric-dimension-of-two-types-of-claw-free-cubic-graphs-with-applications/.
  Sardar and coauthors study resolving sets on strings/rings of diamonds.
  Direct DOI browser opening returned an internal error, but publisher content
  was available. The ring sensor bound is known supporting material and is
  precisely part of the separately selected sensing group to be deselected.
- Current neighboring damage results are evaluated under lane 4 and against
  the original source's references/rules under lane 1. Neither unrestricted
  cop damage nor zombie capture numbers establish this geodesic-damage result.
- Result: primary bibliography and current forward-citation trails covered;
  no substantially equivalent independent main theorem found.

## 7. Formalization repositories

- Live default-head/tree/branch/recent-commit API endpoints were called for
  https://github.com/leanprover-community/mathlib4 and
  https://github.com/google-deepmind/formal-conjectures at 01:12:21–22 UTC,
  using the same endpoint suffixes as lane 2 (master for Mathlib, main for
  formal-conjectures).
- Mathlib head `01c8d16a8c31eed40a54a38a8c8006c4ee001152`, 2026-09-09
  22:48:08 UTC. Tree 10,604 paths, not truncated; first 100 branch names and
  newest 100 commits searched. No relevant path/commit/branch-name hit.
- Formal-conjectures head `b82b08faa9006484021c12005ab41287fb2ffb69`,
  2026-09-09 16:54:25 UTC. Tree 1,728 paths, not truncated; 30 branches and
  newest 100 commits searched. No target path/commit/branch-name hit.
- Current code searches: `zombie repo:leanprover-community/mathlib4` found
  only unrelated subprocess cleanup in `scripts/verify_version_tags.py`;
  `zdmg` there returned zero; `zombie` in formal-conjectures returned zero.
- Individually scoped all-state REST PR/issue searches for `zombie` and `zdmg`
  at 01:14:09–11 returned zero except two old unrelated Mathlib PRs:
  https://github.com/leanprover-community/mathlib4/pull/19343 (Coxeter weights)
  and https://github.com/leanprover-community/mathlib4/pull/2838 (cache handling).
  All states were included, covering open, merged and recently closed work.
- Formal-conjectures' two REST issue searches hit HTTP 403 rate limits;
  repeated both via connected read-only GitHub issue search, each successful
  with zero results at 01:14–01:15. Individually scoped commit searches for
  `zombie`, `zdmg`, `2607.16382` returned zero for both repositories.
- Initial combined GitHub issue queries used ambiguous parentheses and
  are not relied upon. Initial commit-response summarization misclassified
  the JSON response; corrected individual queries supplied the counts above.
- Own public repository https://github.com/lennrt/palomar-formalizations,
  local current commit `c52864a39eb96a92ff9393e3b8bc62f98b196553`, contains
  this author's existing proof. It is the same work being revised, not a scoop.
- Result: current statement/code, PR/issue, commits and finite branch-name
  searches reveal no equivalent independent formalization.

## 8. Local duplication sweep

- Before searches, read `AGENTS.md`, the full prior dated record and template;
  searched `RESEARCH_LEDGER.md` using zombie, short-cycle, Davila, Conjecture24,
  22667596 and the distinctive bound. Existing entry is ACTIVE—GREEN for this
  same supplied proof; no closed lane is being reopened by the editorial edit.
- Current `rg` content sweep covered `.md`, `.lean`, `.tex`, `.json` throughout
  this checkout, excluding `.lake` and `.git`, with those same terms and the
  formal cardinality expression. Found 170 matching files inside this paper's
  existing project and only the root README, ledger and prior scoop record
  outside it. No separate local proof attempt or competing deliverable found.
- Local source remains supplied v1.0.0, 2026-09-09, DOI 10.5281/zenodo.22667596;
  original Lean ZIP SHA256
  `cfaf883855f94ae2a5c666eba5e3a8966ce6b1c76c769dffb566719a3c3627ba`.
- Result: continuation of the same work. Distinct distance-shell paper and
  known sensing material are not misrepresented as new Conjecture-24 content.

## Equivalence and term-by-term audit

Reread current `PalomarWrappers.lean`, `ZombieMain/NumericalConjecture.lean`
and the corresponding Challenge declarations before scope editing. `V` with
`Fintype`, `SimpleGraph V`, `G.Connected`, exact degree-three equality,
`∀ u v, G.Adj u v → ¬G.IsBridge s(u,v)` and `10 ≤ Fintype.card V` respectively
match finiteness, simplicity, connectivity, cubicity, bridgelessness and the
source order cutoff. The conclusion literally compares `zombieDamageNumber`
with the vertex count. `PalomarVerified.degree` is a transparent spelling of
Mathlib degree; the conjecture wrappers apply existing original theorems.
The stronger survivor-move bound is exactly `2*n*(n+1)`. No computation,
proof search or new mathematical construction was initiated by this refresh.

The main conjecture and four-exception characterization are not supplied by
the located girth-only theorem, closed cubic classification, known sensor bound,
ordinary-cop damage results or zombie capture results. Those respectively
restrict the graph class, omit pursuit strategies, or change objective/rules.
The editorial repair will remove the three unrelated sensing endpoints from
the selected result set while preserving their library proofs. It does not
make their elementary content paper-worthy merely by rewording its description.
No new result is proposed and the full main theorem is not weakened.

## Decision

- Final status: `GREEN` for revising the existing proof's selected scope and
  honest description in this session. All eight lanes have current evidence;
  Zenodo outage and GitHub rate limit have documented current alternatives.
- No competing prior resolution of the main theorem was found in this finite
  sweep through 2026-09-10 01:15 UTC. This does not assert exhaustive priority.
- Residual uncertainty: finite search/branch scope, unpublished work,
  delayed web/DOI indexing, direct Zenodo outage. No concrete competing result
  or unresolved mathematical source ambiguity was identified.
- Required recheck: repeat the gate if scope/source changes, new competing
  evidence appears, or before a delayed submission. A public submission is
  still a separate user action; acceptance is not certified by this scoop gate.
- Exclusion ledger: no new exclusion. Known Cushing/Sardar supporting results
  remain credited; the unrelated sensing group is not used to claim research
  interest for the revised selected theorem group.
