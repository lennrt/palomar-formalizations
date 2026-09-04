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

import OneTwoSobolT5.Core
import OneTwoSobolT5.Census

#print axioms OneTwoSobolT5.source_directions_to_rows
#print axioms OneTwoSobolT5.compositions_11_count
#print axioms OneTwoSobolT5.compositions_11_nodup
#print axioms OneTwoSobolT5.compositions_11_totals
#print axioms OneTwoSobolT5.compositions_12_count
#print axioms OneTwoSobolT5.compositions_12_nodup
#print axioms OneTwoSobolT5.compositions_12_totals
#print axioms OneTwoSobolT5.compositions_13_to_16_totals
#print axioms OneTwoSobolT5.selected_stack_lengths
#print axioms OneTwoSobolT5.all_total_11_independent
#print axioms OneTwoSobolT5.t_le_five_certificate
#print axioms OneTwoSobolT5.witness_row_count
#print axioms OneTwoSobolT5.witness_rows_exact
#print axioms OneTwoSobolT5.witness_dependency
#print axioms OneTwoSobolT5.some_total_12_dependent
#print axioms OneTwoSobolT5.some_total_13_dependent
#print axioms OneTwoSobolT5.some_total_14_dependent
#print axioms OneTwoSobolT5.some_total_15_dependent
#print axioms OneTwoSobolT5.some_total_16_dependent
#print axioms OneTwoSobolT5.not_t_le_four_certificate
#print axioms OneTwoSobolT5.not_t_le_three_certificate
#print axioms OneTwoSobolT5.not_t_le_two_certificate
#print axioms OneTwoSobolT5.not_t_le_one_certificate
#print axioms OneTwoSobolT5.not_t_le_zero_certificate
#print axioms OneTwoSobolT5.exact_t_five_certificate
#print axioms OneTwoSobolT5.explicit_eight_row_xor
#print axioms OneTwoSobolT5.Census.buildWindows_eq_wlist
#print axioms OneTwoSobolT5.Census.wlist_all
#print axioms OneTwoSobolT5.Census.census_all
#print axioms OneTwoSobolT5.census_every_window
#print axioms OneTwoSobolT5.census_distribution
