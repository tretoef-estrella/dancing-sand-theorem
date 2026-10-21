# Version 11 → version 12 of «The Dancing Sand Theorem» (Grepy el Zahorí, 21 October 2026)

Rafa's order of 21 October 2026: put in the paper (and the repository) the table of `Syl_2 K(Q_n)` for `n ≤ 16`, which a reader of version 11 suggested by email on 20 October 2026 (a table that recovers Bai's and goes beyond it), and which the author sent him that day with the promise to add it to the next version. Version 12 is built from version 11 by `v12_edits/text_edits.py`: anchored replacements, each asserted unique; the table is generated from `logs/paper_rule_abs_2_16.log`, no row typed by hand. Diff `v12_edits/DIFF_v11_to_v12.txt`. **No statement, proof or number of the mathematics changes.**

| # | Place | Change |
|---|---|---|
| T1 | header | `14 October 2026 · version 11` → `21 October 2026 · version 12` |
| T2 | new §1.9 «The groups for `n ≤ 16`» | the table of `Syl_2 K(Q_n)`, `n = 2, …, 16`, with how each row was checked, and one paragraph |
| T3 | §1.0, record of the readings | one sentence: the table of §1.9 changes no statement, proof or number and was not read cold |
| T4 | §13 | one sentence: the table of §1.9 adds no statement and was not read cold |
| T5 | Appendix A, later versions | one sentence: the table was added after a reader of version 11 suggested it; its rows were checked as §1.9 says; not read cold |

**How the rows were checked (double check, 21 October 2026).**
- Rule log `logs/paper_rule_abs_2_16.log` (the paper's `gate/rule_abs.py`).
- Second program: the cold reader's own rule engine (`~/Desktop/LECTORES_EN_FRIO/CUBO_DANCING_SAND_1/engines/myrule.py`, written without our code), forms B and X: 30/30 rows equal; control «no pooling» differs in 4 rows. `release/TABLA_N16_2026-10-21/segunda_ruta.py`, log `segunda_ruta.log` (VIGIA-FIN-OK). A first version of the comparison forgot to remove the summand `ℤ_2` of the reader's output and reported 30 false differences; kept as `segunda_ruta_v1_comparacion_mal_escrita.log`.
- Rows 2–11 against Bai's printed table: `logs/gh_bai_table_gate_v2.log` (10/10, control 0). Rows 2–13 against the direct Smith form: `logs/gh_audit_vuelo1.log` (PASS) and §12.1, §12.2.
- Rows 14–16, numbers of factors of order 2, 4, ≥ 8: `logs/gh_audit_vuelo1.log` («PASS layers»); the engine `engines/aire_*` (linear algebra over 𝔽_2, without the rule) gives `r_{≥3} + 1` (the `+1` is the summand `ℤ_2`) in every row `n = 3..11, 14, 15, 16`, the same offset where Bai's table is the ground truth.
- Every row: `2^{n−1} − 1` factors and `2^{n−2} − 2^{⌊(n−2)/2⌋}` factors `ℤ/2` (asserted in `text_edits.py`).

**Pdf.** `build_v12.sh` = `build_v11.sh` with the name changed. 54 pages (v11: 53). Word diff of the pdf texts (v11 → v12): only T1–T5 and page numbers. Pages 1, 11 and 12 looked at (`checks_v12/`).
