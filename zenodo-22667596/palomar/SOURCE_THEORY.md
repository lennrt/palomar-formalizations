# Source theory and formalization attribution

**Original source theory: Randy Davila.** The zombie damage number and the
one-zombie damage game are from Definition 1 of
[*The Zombie Damage Number of a Graph*](https://arxiv.org/abs/2607.16382v1),
arXiv:2607.16382v1, 17 July 2026. Davila also posed Conjecture 24. The ordinary
damage game was introduced by Cox and Sanaei in
[*The damage number of a graph*](https://ajc.maths.uq.edu.au/pdf/75/ajc_v75_p001.pdf),
*Australasian Journal of Combinatorics* 75(1), 1–16 (2019). This project does
not claim to introduce either game or parameter.

**Proof and formalization: Lennart Rudolph.** The implementation, complete
Conjecture 24 proof, numerical interface and associated manuscript were
developed with the OpenAI ChatGPT, OpenAI Codex (Astra), and Anthropic Fable 5.1
adversarial-review assistance disclosed in [README.md](README.md). Randy Davila
is credited as the mathematical source, without implying coauthorship or
endorsement of this implementation.

| Formal material | Mathematical attribution |
|---|---|
| Geodesic replies, start/turn order, survivor moves, capture and damage | Davila Definition 1, formalized using actual shortest walks |
| Numerical zombie damage number and score thresholds | Davila’s parameter, formalized as the largest guaranteed damage score; the interface equivalences are proved here |
| Pass/zero-damage conventions and universal-vertex obstruction | Davila’s rules and the relevant direction of Proposition 3 |
| `CycleGame.full_damage` for cycles of length at least five | Davila Theorem 6 |
| `ForcedTrace` and subsequent routing | Development of the source’s nonbacktracking method, with source Lemma 12 identified in that module |
| Conjecture 24 | Posed by Davila; its complete proof and numerical conclusion are formalized here |
| Four-exception characterization, explicit move bound and clean-edge recurrence | Results of the associated paper and formalization |
| Closed cubic short-cycle classification | Earlier work by Cushing, Kangaslampi, Lipiäinen, Liu and Stagg |
| Ring-of-diamonds metric dimension and resulting sensor lower bound | Earlier work by Sardar, Xu, Cancan, Farahani, Alaeiyan and Patil; supplementary library material, not selected |
| Labelled multiplicity-preserving distance-shell observations | The observation model in Rudolph’s tomography preprint; supplementary library material separate from the selected pursuit theorem |

Cushing et al., [*The Graph Curvature Calculator and the curvatures of cubic
graphs*](https://doi.org/10.1080/10586458.2019.1660740), *Experimental Mathematics*
31(2), 583–595 (2022; online 2019), already give the closed classification.
The specific locators are Lemma 5.1 and Corollary 5.4 of
[arXiv:1712.03033v2](https://arxiv.org/abs/1712.03033v2).

Sardar et al., [*Computing Metric Dimension of Two Types of Claw-free Cubic
Graphs with Applications*](https://doi.org/10.61091/jcmcc119-17), *Journal of
Combinatorial Mathematics and Combinatorial Computing* 119, 163–174 (2024),
Theorem 2, already prove the metric-dimension bound for rings of diamonds.
The sensor results in this project are supporting formalizations of known
mathematics, without a new priority claim. The involution obstruction,
central-pair sensor lemma and ring sensor-cardinality bound are preserved in
the Lean library but excluded from the 39-result pursuit Comparator selection
and its Challenge. They support the separate discussion around paper Remark 19,
not the proof of Conjecture 24.

The observation model is documented in [*Distance-Shell Tomography on Graphs:
Integer Trades and Optimal Grid Sensing*](https://doi.org/10.5281/zenodo.22404456).
It is used only for those unselected accompanying observation results.

## Related pursuit and damage literature

Liu and Miller, [*Replacing Cops with Zombies*](https://doi.org/10.4230/LIPIcs.FUN.2026.30),
FUN 2026, LIPIcs 366, 30:1–30:12, study geodesic pursuit with a capture objective,
including capture throttling on grids. Their full publisher text does not
introduce a damaged-vertex objective.

Gledel, Kinnersley, Patkós and Stojaković,
[*On the damage number of graphs*](https://arxiv.org/abs/2608.15226v1),
arXiv:2608.15226v1 (15 August 2026), study ordinary one-cop damage, with
graph-family and complexity results. The cop may choose any neighboring vertex
or pass. This is a different strategy class from Davila's geodesic zombie.

The ordinary-damage lineage also includes Stojaković and Wulf,
[*On the multi-robber damage number*](https://arxiv.org/abs/2209.10965v4)
(2022; v4 revised 22 June 2026), and Huggan, Messinger and Porter,
[*The damage number of the Cartesian product of graphs*](https://ajc.maths.uq.edu.au/pdf/88/ajc_v88_p362.pdf),
AJC 88(3), 362–384 (2024), with their
[*Corrigendum*](https://ajc.maths.uq.edu.au/pdf/91/ajc_v91_p217.pdf),
AJC 91(1), 217–218 (2025). The correction concerns domination definitions and
affected ordinary-damage statements. These works provide background; their
theorems are not imported as unproved premises of the formalization.

The [game map](GAME.md), [selected declaration map](DECLARATIONS.md), and
[structured metadata](formalization.yaml) provide the source-to-formalization
correspondence. This project includes the entire formal game and the selected
results; numerical regression comparisons do not constitute formal proofs of
all results in the original paper. No external endorsement is claimed.
