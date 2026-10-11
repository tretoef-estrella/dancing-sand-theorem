# Version 9 → version 10 of «The Dancing Sand Theorem» (Grepy Escribano, 11 October 2026)

Rafa's order of 11 October 2026: version 2 of the Lean certificate, with piece C53 (the small cases), and every place that must mention it. Version 10 is built from version 9 by `v10_edits/text_edits.py`: anchored replacements, each asserted unique. The diff is `v10_edits/DIFF_v9_to_v10.txt`, five hunks. **No statement and no number of the mathematics changes.** The counts of the Lean project are read from `lean/CERTIFICADO/data/totals_v2.txt`, and the DOI of version 2 of the certificate from `lean/CERTIFICADO/data/lc_v2_doi.txt`.

| # | Place | Change |
|---|---|---|
| F1 | header | `version 9` → `version 10` |
| F2 | §12.3, What Lean proves | Theorem DW's equivalent form is `SmallCases.DW'_all`, for every `n ≥ 1`; for `n ≥ 2` it is `FoldLaw.DW'` |
| F3 | §12.3, Corollary 1.4 | the `2`-part is `SmallCases.DW'_all` read together with the Main Theorem |
| F4 | §12.3, Corollary 1.6 | Gao et al.'s Theorem 4.1 for every `n ≥ 2` is `SmallCases.G1_all` (was: for `n ≥ 3`) |
| F5 | §12.3, How | a 69th piece added the cases that the first 68 left out; the four modules of the 69th piece were compiled from their sources, with the other 416 unchanged; the counts are now 420 files (419 in 69 folders), 61 285 lines, 3 470 declarations |
| F6 | §12.3, Read cold | one sentence on the cold reading of the changes of version 2 of the certificate |
| F7 | §12.3, What Lean does not state | the bullet on the small cases removed: they are now stated |
| F8 | §12.3, Where | 68 → 69 pieces |
| F9 | Appendix A, Formal verification | the 69th piece (11 October 2026) and the cold reading of the changes of version 2 of the certificate |
| F10 | [LC26] | version 2 of the certificate, DOI 10.5281/zenodo.23298436; all versions, concept DOI 10.5281/zenodo.23296707 |

**Builder.** `build_v10.sh`, the builder of version 9 unchanged.

**Acceptance** (`checks_v10/acceptance.py`): the twelve checks of version 9, with two changes. Check 11 reads `logs/CertCubo2.log`, the version-2 log that declares the `SmallCases` names. Check 12 looks for the DOI of version 2 of the certificate. Result: 12/12 PASS; control: 12/12 FAIL.

**Pdf.** 52 pages. Pages 2–47 are identical to version 9 pixel by pixel at 40 dpi. Pages 1 and 48–52 were looked at.

## After cold reading 13 («Grepy Remate», 11 October 2026)

The reading read three things: the changes of version 10, the changes of version 2 of the certificate, and the Lean of piece C53. Its report is `reports/LECTOR_FRIO_13/delivered_2026-10-11/REPORT_COLD_13.md`, graded HIGHEST in `CALIFICACION_LECTOR_FRIO_13_v1.md`. In the paper it found two sentences that overstated the scope of that reading, and one name defined nowhere. They were replaced word for word in `text_edits.py`:

- **P-1**, §12.3 How: «Theorem DW′» → «the equivalent form of Theorem DW».
- **P-2**, §12.3 Read cold: «Version 2 of the certificate … was read cold in its turn» → «The changes of version 2 of the certificate … were read cold in their turn before release, with the Lean of that piece».
- **P-3**, Appendix A: «and so was its version 2» → «and so were the changes of its version 2».

The result is byte-identical to the reader's own `scratch/applied_THE_DANCING_SAND_THEOREM_v10.md`.

- **Acceptance:** 12/12 PASS, controls 12/12 FAIL (`logs/acc_v10_remate.log`, `logs/acc_v10_remate_control.log`).
- **Pdf:** pages 1–47 are identical to the pdf before these replacements, and pages 48–52 were looked at.
- **No further reading:** every change of text is the reader's own (termination rule).

**Files of version 10:** md `d059cc86a8b23a190799b6ce35c5e767`, pdf `1924465ba23ca58584e6348229e10d51` (52 pages). Published on Zenodo as version 10, DOI 10.5281/zenodo.23298437.
