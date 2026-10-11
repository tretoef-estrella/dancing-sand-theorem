# Version 8 → version 9 of «The Dancing Sand Theorem» (Grepy Escribano, 11 October 2026)

Plan A–D of Rafa, 11 October 2026, step B1: the paper with the Lean certificate. Built from version 8 by `v9_edits/text_edits.py` (anchored replacements, each asserted unique). Diff: `v9_edits/DIFF_v8_to_v9.txt`, 9 hunks (14 is the number of edits of `text_edits.py`; corrected 11 Oct 2026 after cold reading 11). **No statement and no number of the mathematics changes.**

| # | Place | Change | Source |
|---|---|---|---|
| E1 | header | `6 October 2026 · version 8` → `11 October 2026 · version 9` | — |
| E2 | Abstract | one bold sentence: the whole proof checked in Lean 4 with Mathlib, nothing cited | plan B1 |
| E3 | §1.0 table | **not changed.** A «Lean» column was built first; it made the table wider than the page, and Chrome scaled every page (right edge 542 → 537 pt; check 3 failed). Withdrawn; the Lean names are in §12.3 | acceptance check 3 |
| E4 | §1.0 paragraph | one sentence: checked in Lean, read cold; the Lean name of each result of the table is in §12.3 | plan B1 |
| E5 | §1.3 | the folded cube's edges: «two pairs are joined once for each pair of words, one from each, that differ in one letter» counted each edge twice (`(x, x+e_i)` and `(x+𝟙, x+𝟙+e_i)`); now `{x, x + 𝟙}` is joined to `{x + e_i, x + 𝟙 + e_i}` once for each `i`, and each edge is the image of two edges of `Q_n`. The next sentence (the Cayley graph), the proofs and the numbers always used the right graph | cold reading of the Lean certificate, F-ERR-4 |
| E6 | §11, question 6 | «No part of this paper has been checked by a proof assistant…» (now false) → «The tilting modules in Lean»: the identification of the dance lattices with the tilting modules is not formalized, and the proof does not need it | plan B1 |
| E7 | §12.3, new | «The Lean certificate»: what Lean proves (with Lean names), nothing cited, the one point of trust, how, the cold reading, what Lean does not state, where | plan B1; certificate [LC26] |
| E8 | §13 | new bullet «Checked in Lean 4 with Mathlib»; «Not done: a human referee» (formal verification removed); closing sentence | plan B1 |
| E9 | Acknowledgements | one paragraph: Aristotle (Harmonic) wrote the Lean proofs; instances of Claude wrote the pieces, audited, compiled, read the certificate cold | plan B1 |
| E10 | Appendix A | one entry «Formal verification» (6–10 October; read cold 11 October) | plan B1 |
| E11 | References | [dMU21] Lean 4, [Har26] Aristotle, [LC26] the certificate with the placeholder **`[LC-DOI]`** (filled in step D, after the Zenodo DOI is reserved), [mC20] Mathlib | plan B1 |

**Builder.** `build_v9.sh` and `md2html_v9.py` are copies of version 8's, with one rule added to `md2html_v9.py`: (68) a Lean name `Namespace.Name` (and `sorry`, `propext`, `v4.28.0`) is printed as code, in pieces that may break after a dot. Checked: version 8's md built with `md2html_v9.py` gives an html byte-identical to the one built with `md2html_v8.py`.

**Acceptance** (`checks_v9/acceptance.py`): v8's nine checks plus three: (10) no sentence saying that no proof assistant checked the paper; (11) every Lean name printed exists in `logs/CertCubo.log` (17 names, all found); (12) `[LC-DOI]` exactly once in the md and in the pdf. Result: 12/12 PASS (`logs/acc_v9.log`); control: 12/12 FAIL (`logs/acc_v9_control.log`). One declared exception in check 5: page 45 is 83.8 % full because the next row of the §12.2 table (Lemma 7.9, a tall row) does not split; looked at on the page; the exception holds only while page 46 begins with that table's header.

**Pdf.** 51 pages (v8: 50). Pages 6–42 are identical to pages of v8 pixel by pixel (40 dpi); pages 1–5 and 43–51 were looked at one by one.

**Files.** md `79f4d7f9…`, pdf `fd7d8d1a…`, html `e350bfa6…`.

## After cold reading 11 («Grepy Cotejo», 11 October 2026)
The reading (reports/LECTOR_FRIO_11/delivered/REPORT_COLD_11.md, graded HIGHEST in CALIFICACION_LECTOR_FRIO_11_v1.md) found five false or inexact new sentences and three points of presentation, none touching a theorem. Its replacements were applied word for word by `v9_edits/reader11_replacements.py`; the result is byte-identical to the reader's own `scratch/v9_with_replacements.md` except the line of P-B16, which the reader left with the placeholder:
- E-B2 §1.0: §12.3 gives the Lean names except Theorems O and F (Theorems 6.2 and 7.8);
- E-B3 §1.3: the two-edges sentence is for `n ≥ 2`; at `n = 1`, one vertex with one loop;
- E-B9 §12.3: 416 Lean files and 60 964 lines (with the main file);
- E-B10 §12.3: the one sentence the first Lean reading found false was this paper's §1.3 of version 8;
- E-B14 §13: «every proved result above»;
- P-B5: the sentence on piece numbers removed; P-B11: «([LC26], §1.3 and §2)»; P-B16: [LC26] carries the DOI 10.5281/zenodo.23296708, reserved on Zenodo for the Lean record before the build.
Acceptance list: check 12 rewritten to require that DOI once and no placeholder; check 6's three known non-text lines (table row, display (K), matrix labels) moved back to their v7 positions, looked at on pages 9, 11, 35 at 85 dpi, same gaps. Result: 12/12 PASS, control 12/12 FAIL (`logs/acc_v9_cotejo.log`, `logs/acc_v9_cotejo_control.log`). 52 pages (one more than before the reading); pages 2, 5, 48, 49, 52, which carry the changes, looked at. Files: md `eaf7f912…`, pdf `e20a90ee…`. Before the reading: `historico/THE_DANCING_SAND_THEOREM_v9_antes_de_la_lectura_11.*`. No further reading (termination rule).
