# Corrections from version 6 to version 7 of «The Dancing Sand Theorem»

Grepy Muchas Pilas, chief auditor, 6 October 2026.

## Files
- `THE_DANCING_SAND_THEOREM_v7.md`: md5 `e950ed939cd2bb9180af8533e7eaa918`.
- `THE_DANCING_SAND_THEOREM_v7.pdf`: md5 `feb4ab4c81e479d4f0ebcdf5825421e8`, 52 pages, build 1 (`logs/v7_build_1.log`).
- `THE_DANCING_SAND_THEOREM_v7.html`: md5 `70ac84dca8b5c6894d1aac20d60886a7`.
- Builder: `build_v7.sh`, `md2html_v7.py`, `phtml.py`. These are the builder of version 6 with the names changed and no rule changed.
- Edits: `v7_edits/text_edits.py`; every replacement is asserted to be unique. The diff of the md is `v7_edits/DIFF_v6_to_v7.txt`.
- Source: cold reading 8, `reports/LECTOR_FRIO_8/delivered/REPORT_COLD_8.md` (md5 `e64caf53a14ff90786f5e27c5e14cce6`), graded in `reports/LECTOR_FRIO_8/CALIFICACION_LECTOR_FRIO_8_v1.md`.

**No mathematical statement changed, and no number.** The changes are sentences of the record, one row of §12.2, one sentence of §1.7, one sentence of a proof, and one reference.

## The changes
- **E1, §13:** the sentence on what changed in versions 2 to 7 now names every statement that changed (Theorem 7.8 and Lemma 7.2(b) in version 2; Lemmas 7.9, 10.6(a) and 10.10 in version 3), and only then says «no other numbered statement».
- **E2, Acknowledgements:** «The work took five days, from 2 to 6 October 2026».
- **E3, §12.2, reader 3 on the lattices `T(λ)`:** the row now prints both runs, and the counts taken from cold reader 3's two logs (`reports/LECTOR_FRIO_3/delivered_2026-10-05/logs/family_lattice_31_10.log`, `family_lattice_63_8.log`):
  - the ranges: `λ ≤ 31, i ≤ 10` and `λ ≤ 63, i ≤ 8`;
  - cells compared: 639 and 762;
  - cells skipped, whose predicted exponent is at least 60: 43 and 372;
  - cells where pooling acts: 102 and 172.
- **D1, §1.7:** «each move gives every new floor a payment equal to minus half the product of the payments of two adjacent old floors».
- **From the reader's taste list, because each makes a sentence more exact:**
  - §1.0 now reads «(§7.1, §7.4, §7.5, §9.2)»;
  - Proposition 9.6 (H) now reads «if `Z_1` is positive there»;
  - [LZ22] now reads «with an appendix by S. Casalaina-Martin»;
  - the ranges of houses in §12 and Appendix A now say whether `k = 0` is included: «`k ≤ 7` (`k = 0` included)» for 43 690; «`1 ≤ k ≤ 7`» for 65 532; «`1 ≤ k ≤ 6`» for 16 380.
- **The record:**
  - header «version 7»;
  - §1.0, §13 and Appendix A record reading 8, which read the changes of version 6 and its whole pdf;
  - version 7 is «made by the auditor, not yet read cold».

## The pdf
- Pages 1, 2, 3, 9, 30, 44 and 46–52 differ from version 6, found by comparing the rendered pages. Each was looked at at 85 dpi; nothing is broken. The other 39 pages are unchanged.
- **The acceptance list, repaired (`checks_v7/acceptance.py`; logs `logs/v7_accept_2.log`, `v7_accept_control_2.log`, `v7_accept_on_v6_2.log`, `v7_accept_on_v5_2.log`, all `VIGIA-FIN-OK`):**
  - version 7 passes 9 of 9;
  - control mode fires 9 of 9;
  - version 6 passes 9 of 9;
  - version 5 fails checks 1, 4, 6 and 8. Check 6 flags the row of its §1.7 table, which is not a text line.
  - Check 9 is now judged, with cold reader 8's cross-reference check and number check: 32 keys cited; every numbered reference resolves except five external items; 108 + 7 + 16 numbers of §12, §1.0–§1.4, §13 and Appendix A agree in order.
  - A bug of check 6 was found by its new control: the match needed a leading space, so a line at 10 pt or more was never seen. It is fixed.

## Errors of the scribe in this turn
- My first edit of Appendix A gave cold reader 4 the range «`α = 1, 2`». Its report says `α ≤ 3` and 65 532 houses. I caught it before the build, and it is corrected.
- `echo` with a word starting with `=` in zsh, once more (harmless).

## Erratum (added on 6 October 2026 by Grepy Escribano, after cold reading 9; the lines above are left as they were written)
- l. 13, «No mathematical statement changed, and no number»: «and no number» is false. The dates of the work in the Acknowledgements and one row of §12.2 changed (`reports/LECTOR_FRIO_9/delivered/REPORT_COLD_9.md` §0).
- l. 35, «The other 39 pages are unchanged»: they are 38 (52 pages − 14 changed).
