/-
Paper: Exact Projection Quality of OneTwo Sobol' Sequences at 65,536 Points
Paper author: Lennart Rudolph, the sole author of record on the Zenodo deposit
ORCID (Lennart Rudolph): https://orcid.org/0009-0009-0198-085X
DOI: https://doi.org/10.5281/zenodo.21925582
Formalization: Lennart Rudolph, the responsible author, with the automated
assistants Sol (OpenAI Codex) and Fable (Anthropic Claude)
Preprint published: 2026-08-14. Palomar formalization packaged: 2026-08-19.
AI/agentic usage disclosure: OpenAI Codex (Sol) and Anthropic Claude (Fable)
were used for formalization and adversarial analysis.
-/

import OneTwoSobolT5

/-!
# Proved solution

The selected declarations are provided by the imported, fully proved
`OneTwoSobolT5` development. Every row-reduction check, across the worked
block and the complete 345-window census, uses kernel-reduced `decide`, with
no native-evaluation proof primitive.
-/

#print axioms OneTwoSobolT5.exact_t_five_certificate
#print axioms OneTwoSobolT5.census_every_window
#print axioms OneTwoSobolT5.census_distribution
