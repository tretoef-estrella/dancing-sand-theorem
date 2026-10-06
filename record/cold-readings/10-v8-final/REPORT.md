# REPORT_COLD_10 — cold reading 10 of «The Dancing Sand Theorem», version 8

Reader: Grepy el lector frío del cubo 10.

## 0. First lines

- **Did anything mathematical change from version 7 to version 8? NO.** The five hunks of the diff touch the header, §1.0, §13, the Acknowledgements and Appendix A only; no numbered statement, proof, table of §12 or number of a result changed or disappeared. My own `diff -u` equals the given diff (§1). The stop rule was not triggered.
- **Is every new sentence true? NO — one clause is false** (§2.1 #10): §1.0 says that «what was corrected, and what was left as it was, is listed with its source in the record kept with the project». The record of corrections lists what was corrected with its sources, but not what was left: reading 7's PD17, PD18, PD24, PD26 and P2.7-b are listed nowhere in it, and reading 7 found the «left as they are» list of version 5 incomplete. Every other new sentence holds, among them «none of these readings found a gap or an error in the mathematics» and the list of §13 of the numbered statements changed after version 1 (checked on versions 1, 2, 3 and 7 by my own script, with a control). The sentences on the readings of «each/every later version» hold for version 8 too, because my verdict on (a) is that no mathematics changed.
- **Is anything broken on the pages? NO.** 50 of 50 pages looked at, at 90 dpi; the pdf text differs from v7 only in the five places (word comparison, and identical character multisets in the body §1.1–§12 and in the references).
- **Does the acceptance list pass, and do its controls fail? YES.** 9 of 9 PASS on v8; 9 of 9 FAIL in control mode, each damage acting on its own check. The three non-text lines of check 6 are the same lines as in v7, with the same gaps (14.37, 12.77, 11.11 pt), and look right; the damage of check 5, moved to page 12, acts.
- **The list of replacements (one):**
  - **R1 — §1.0, the paragraph under the table** (md l. 32; pdf p. 2, lines 12–13 of the paragraph). ERROR of the record, not of the mathematics.
    - Remove: «what was corrected, and what was left as it was, is listed with its source in the record kept with the project (Appendix A).»
    - Print: «the list of corrections of each version, with its sources, and every report are kept with the project (Appendix A).»
    - The sentence then reads: «Between them, they found false or inexact sentences in the record of the work and in §12, points of presentation, and defects of typesetting; the list of corrections of each version, with its sources, and every report are kept with the project (Appendix A).» It says only what Appendix A says («the list of corrections of each version with its sources, every report and every grading are kept with the project»).

## 1. (a) The hunks of the diff

**My own diff.** `diff -u` of the two md files (logs/owndiff.log, VIGIA-FIN-OK): 61 lines; the body (all but the two header lines with timestamps) is byte-identical (`cmp`) to `DIFF_v7_to_v8.txt`. Only the timestamps differ. The md goes from 1187 to 1180 lines. **The given diff is the whole change of the md.**

Five hunks:

1. **Header (line 6).** Removes «version 7», adds «version 8». Not mathematical.
2. **§1.0, the paragraph under the table (line 32).** The table of results above it is context, unchanged. Removes: «Version 1 … Version 2» (replaced by «The first version … The second version»), «by a fourth reader» (→ «by another reader»), from the account of reader 4 the clause «two rows of §12.1 that said more than their code, and points of presentation», and the five sentences on the readings of versions 3, 4, 5, 6 and the sentence «The changes of version 7 have not yet been read cold (§13, Appendix A)». Adds: «also», the sentence «The changes of each later version were read cold in turn …; none of these readings found a gap or an error in the mathematics», the sentence «Between them, … (Appendix A)». Lemmas 7.2(b), 7.9, 10.6(a) are only named; no statement, proof or number of a result is touched.
3. **§13, the bullets.** The bullet «Proved …» keeps exactly the same list of results (Main Theorem; Theorem D; Theorems O and F; Theorem DW and Corollary 1.4; Corollaries 1.5, 1.6, 1.7); only its account of the readings is shortened. «Added in version 3 …» loses its second sentence, which becomes the new bullet «Numbered statements changed after the first version …». The four bullets «Changed in version 4/5/6/7» are removed. «Measured, not proved» is context, unchanged. «Not done» loses «a cold reading of the changes of version 7». No result changes grade, none disappears.
4. **Acknowledgements.** Removes «The work took five days, from 2 to 6 October 2026. It began» → «The work began». Not mathematical.
5. **Appendix A.** Removes the entries «Version 3» … «Version 7»; adds the entry «Later versions». The numbers removed with them (7 634, 7 620, 14, 301, 192 024, 9 880) were descriptions of the readings; they remain printed in §12 (grep of the v8 md, §12 = l. 1055–1113: 7 634 at l. 1100; 7 620 at l. 1100, 1112; 192 024 at l. 1068, 1101; 9 880 at l. 1102, 1112; «301 clocks» at l. 1065; 14 in the row of l. 1100) — no number of a result disappears. (Corrected: I first wrote that some of them were also in the «Version 2» entry; that entry holds 7 874, not these.)

**Verdict (a): NOTHING mathematical, and no number of a result, changed or disappeared from version 7 to version 8.** No hunk touches a numbered statement, a proof, a table of §12, or a number of a result. The stop rule is not triggered.

## 2. (b) The new sentences, one by one

Evidence read (all in `material/evidence/`): REPORT_COLD_9, _8, _7, _5 whole; REPORT_COLD_6 §0, §1 items 1, 7–9, §2, §3, §6.1, §9; REPORT_COLD_3 §0 and grep; REPORT_COLD_4 §0, §1.1 and grep; gradings 9, 8, 7 whole, 4 and 3 by grep; CORRECTIONS v1→v2 … v6→v7 whole. Versions 1–7 compared by my own script (below).

**My own comparison of the numbered statements** (`scratch/py/stmts.py`, logs `logs/stmts.log`, `logs/stmts_control.log`, both VIGIA-FIN-OK). It cuts every numbered statement (label to «*Proof.*», keeping the lists under a statement, so the (Cut) of Theorem 7.8 is inside its block — checked, the block is printed at the end of the log), normalizes typography only (ℤ/ℚ/𝔽 → Z/Q/F, `’`, `⋯`, no-break and thin spaces, `**`, backticks, `> `) and compares word by word, version to next version and v1→v7, v3→v7. Control: a copy of v7 with «even» removed from Lemma 10.6(a) and «(Cut)» changed to «(Cot)»: both reported, nothing else (it can fail). Results:
- **v1 → v2** (15 statements differ, and §9 renumbered): Lemma 7.2(b) restated; Theorem 7.8 (Cut) gains «and these cuts are strict … (`b ≠ ∅`, since `J_H(∅) = 0`)»; the rest is notation and names (`σ_r → β_r`, `σ → sat`, `τ → ψ`, `ρ_h, κ_h → out_h, in_h`, `ε_L → e_L`, `φ → ϑ`, «doblar»/«paso» → «twist move»/«split move»: CORRECTIONS_v1_to_v2 §7), one title (Proposition 9.5 «the ceiling» → 9.6 «a ceiling for the big clocks»), and **Lemma 3.3**, whose parenthesis «an extension of two lattices is a lattice» gains its justification (Weyl, Newton's forward differences; CORRECTIONS_v1_to_v2 §6) — same claim. **§9:** v1 has 74 numbered statements, v2 has 75. The new number is **Lemma 9.5 (Lemma K)**, which in v1 is stated, with the same text, inside the proof of Proposition 9.5 as «*(K) Lemma K.*» (v1 l. 647); v2 numbers it and shifts 9.5–9.9 to 9.6–9.10 (CORRECTIONS_v1_to_v2 §6; REPORT_COLD_4 l. 59 «the extraction of Lemma K as Lemma 9.5 (same text)»). A renumbering, not a new or changed statement.
- **v2 → v3** (6): Lemma 7.9 «integer separation» → «integrality» (strengthened); Lemma 10.6(a) gains «even»; Lemma 10.10 gains «For every `L ≥ 0` and every floor `f`»; Corollary 1.6 set as a list, Proposition 3.1 «`e = 0, 1`» moved into the lead-in, Corollary 10.2 reordered — same content.
- **v3 → v4** (2), **v4 → v5** (5): wording only («In `R`,» in Lemma 2.1 — `R` is defined just above; [GMM19] → [MGM19]; «Moreover» in Lemma 2.4; quantifier moved to the front in Lemma 3.3; «and» dropped in Theorem 4.4; Corollary 10.9 parenthesis → clause; «The set `𝒦`»). Same content; this agrees with readings 6 and 7.
- **v5 → v6, v6 → v7, v7 → v8:** 0 differences.

So the list of §13 is complete and exact: **HOLDS** (details in 2.3).

### 2.1 §1.0, the new paragraph (sentence by sentence)

| # | sentence or clause | evidence | verdict |
|---|---|---|---|
| 1 | «Every proof behind the table was re-derived by a reader other than its author.» (unchanged from v7) | carried over; Appendix A (flights audited, chains read cold); not re-checkable from `evidence/` (the flights and readings 1–2 are not given) | not new; I did not verify it |
| 2 | «The chains of the Main Theorem and of Theorem DW were read cold before this text was written, by readers with no access to the audits.» (unchanged) | idem; CORRECTIONS_v1_to_v2 §5 | not new; not verifiable here |
| 3 | «The first version of this text was read cold as a whole on 5 October 2026 by a reader with no access to the constructors' reports, the audits or the earlier readings: «holds with gaps».» | REPORT_COLD_3 §0 «HOLDS WITH GAPS», version 1; date 2026-10-05 (l. 481); access not contradicted anywhere | **HOLDS** |
| 4 | «It found one gap: the integer part of Lemma 7.2(b) was false as stated, and four proofs used it; no theorem was affected.» | REPORT_COLD_3 §0 item 2: «false as stated», used in Theorem F step 1, Lemma 7.9, Theorem 7.10 (U2) (with the `i = 0` deletion) and Prop. 9.5 (H) — four proofs; «The conclusions survive» | **HOLDS** |
| 5 | «The second version repaired it (§7.1, §7.4, §7.5, §9.2), and its changes were read cold the same day by another reader: **the repair holds**.» | CORRECTIONS_v1_to_v2 §1 (Lemma 7.2(b) §7.1, Theorem 7.8 §7.4, Lemma 7.9 and Theorem 7.10 §7.5, Prop. 9.6 §9.2); REPORT_COLD_4 l. 3 «Started 2026-10-05», §0 «The repair holds» | **HOLDS** |
| 6 | «That reader also found one false sentence, in a remark used nowhere (the author then found the same missing hypothesis in Lemma 10.6(a), harmless because its only use is for an even system), and found, with a two-line proof, that the fit of every house is integral (Lemma 7.9).» | REPORT_COLD_4 §0 «one false sentence in the rewritten Remark (2) … the remark is used nowhere»; CORRECTIONS_v2_to_v3 §1.1 «I found the same gap in Lemma 10.6(a)»; REPORT_COLD_5 §1.7 (only use: `σ^{(α)}_c`, even); REPORT_COLD_4 l. 140 «my own two lines … `fit(x_H)` takes integer values» | **HOLDS** |
| 7 | «The changes of each later version were read cold in turn, each time by a new reader;» | readings 5 (v3), 6 (v4), 7 (v5), 8 (v6, and its whole pdf), 9 (v7), five different readers; and this reading 10 (v8) | **HOLDS** (for v8: true by my reading, given my verdict (a) = no mathematics changed) |
| 8 | «none of these readings found a gap or an error in the mathematics.» | R5 §0 «I found no GAP and no ERROR»; R6 §0 «No gap and no error in the mathematics»; R7 §0 «The mathematics of every change holds»; R8 §0/§2.2 «no false mathematical statement, no step that does not follow»; R9 §0 «Nothing mathematical is affected». Their errors were of the record (§13, App. A, Acknowledgements, §12 rows) | **HOLDS** |
| 9 | «Between them, they found false or inexact sentences in the record of the work and in §12, points of presentation, and defects of typesetting;» | R6 (7 634 cells, «this text»), R7 (§13 R1), R8 (E1, E2, E3 in §12.2, D1), R9 (App. A v7 entry); points of presentation and typesetting in R5–R8 | **HOLDS** |
| 10 | «what was corrected, and what was left as it was, is listed with its source in the record kept with the project (Appendix A).» | the record of corrections (`evidence/corrections/`, which MISSION §1 names as «that record») lists what was corrected with its source, but **not what was left as it was**: (i) CORRECTIONS_v5_to_v6 lists neither as corrected nor as left reading 7's PD17 (runs not aligned), PD18 (light mathematics in bold headings), PD24 (a word alone before a display), PD26 (title page, p. 5) and P2.7-b ([TW21], [LZ22]); they appear only in REPORT_COLD_8 §6.1 («not a defect by §1», «not fixed»); it also lists PD11 as fixed (rule G27), which reading 8 found «not fixed»; (ii) reading 7 found the «left as they are» list of version 5 incomplete by seven kinds (REPORT_COLD_7 item 2.5-bis; grading 7 «ACCEPTED»), and CORRECTIONS_v4_to_v5 carries no erratum; (iii) CORRECTIONS_v3_to_v4 lists reading 5's row 20 as corrected, and reading 6 found it «not fixed in substance» (REPORT_COLD_6 §6.1); (iv) reading 8's four taste points not applied are recorded only in its grading, not in CORRECTIONS_v6_to_v7. The fate of every finding can be reconstructed from the next reading's report, but it is not «listed» by the record of corrections | **ERROR** (of the record, not of the mathematics). Replacement in §0 item R1 |
| 11 | «No human expert has refereed this work.» / «The words of our own … §1.7; … §1.8.» (unchanged) | — | not new; HOLDS as far as I know |

### 2.2 Acknowledgements

«The work began on 2 October 2026 as a search, inside another project of the author, for open problems within reach of the same methods.» The sentence is in every version since v1 (v1 l. 991); only «The work took five days, from 2 to 6 October 2026.» was removed. Nothing in `evidence/` contradicts the start date (gradings 8 and 9 accept «from 2 to 6 October»). The removal leaves no sentence about the end of the work, so no date can become false. **HOLDS.**

### 2.3 §13, the bullets

- **Header «version 8»:** HOLDS.
- **«Proved, …» — «Their proofs were read cold as text in the first version of this text, which had one gap (Lemma 7.2(b)); the repair was read cold in its turn, and so were the changes of every later version (Appendix A).»** v1 by reader 3, the repair by reader 4, v3–v7 by readers 5–9; v8 by this reading. The list of results is the same as in v7. **HOLDS** (for v8, given my verdict (a)).
- **«Added in version 3, audited, read cold: Lemma 7.9 in its new form (integrality of the fit), found and proved by the fourth reader, re-proved by the auditor, and re-derived by the fifth reader.»** (first sentence unchanged) REPORT_COLD_4 l. 140; CALIFICACION_4 l. 13 «I re-proved it by pencil»; REPORT_COLD_5 §1.1. **HOLDS.**
- **«Numbered statements changed after the first version: version 2 restated Lemma 7.2(b) and added the strictness of the cuts to the (Cut) of Theorem 7.8; version 3 strengthened Lemma 7.9, added the hypothesis «even» to Lemma 10.6(a), and added the explicit quantifier … to Lemma 10.10.»** My comparison: exactly these five changes of content in v1→v2→v3, none later. The (Cut) is the list item under Theorem 7.8, inside the block compared. **HOLDS.**
- **«No other numbered statement changed in what it states; numbers, notation and typesetting changed.»** The other differences are names and notation (CORRECTIONS_v1_to_v2 §7), the numbering of §9 (Lemma K numbered 9.5 in v2, same text as in v1), the justification inside the parenthesis of Lemma 3.3, and rewordings with the same content. **HOLDS.** (Style doubt 6.1: «numbers» is ambiguous.)
- **«Not done: a human referee; a formal verification.»** HOLDS (the cold reading of v8 is this one).

### 2.4 Appendix A, the entry «Later versions»

| # | sentence or clause | evidence | verdict |
|---|---|---|---|
| A1 | «Each later version made corrections asked for by the reading before it;» | v3 ← reading 4 (via its grading, CORRECTIONS_v2_to_v3 §1), v4 ← 5, v5 ← 6, v6 ← 7, v7 ← 8 (each CORRECTIONS names its source). v8 removes the whole version-by-version entry that contained the false sentence found by reading 9 (grading 9: its two corrections «become moot») | **HOLDS** (for v8 in substance: the false sentence is gone, not replaced as reading 9 proposed) |
| A2 | «version 4 also set the mathematics anew, and version 5 the page.» | CORRECTIONS_v3_to_v4 §2–§3 (`phtml.py`: letters italic, digits and operators upright, stacked scripts); CORRECTIONS_v4_to_v5 §3 (GD1–GD32: accents, number sets, matrices, page numbers, tables) | **HOLDS** |
| A3 | «No numbered statement changed in what it states after version 3 (§13).» | my comparison v3→v4→…→v8: wording only | **HOLDS** |
| A4 | «The changes of each version were read cold by a new reader (cold reader 5 and each later one, from 5 October 2026), with no access to the flights or the audits,» | readers 5 and 6 on 5 October (R5 l. 3, R6 l. 3), 7–9 on 6 October (gradings dated 6 October); no report cites a flight or an audit; R9 §6 checked this for reader 8. Reader 5 later became the auditor (MISSION §1), but read v3 as a cold reader. Access cannot be proved from the reports, only not contradicted | **HOLDS** (consistent; not refutable from `evidence/`) |
| A5 | «who checked every changed passage against the version before it,» | R5 §3 (38 hunks, normalized), R6 §1–§2 (29 hunks, `normcmp.py`), R7 §2 (135 blocks), R8 §1.1 (word diff), R9 §1 (10 hunks) | **HOLDS** |
| A6 | «re-counted or re-ran with code of its own the numbers and checks it concerned,» | R5 own gate; R6 `cells.py`; R7 `counts.py`; R8 `counts.py`, `pooling_counts.py`; R9 re-counted the houses (arithmetic, §2.4) and re-ran the author's `gate_strict_cut.py` (not its own code) | **HOLDS** under the reading «re-counted, or re-ran with code of its own» (style doubt 6.2) |
| A7 | «and looked at the pdf: at every page, or at the changed pages after comparing all the pages by image.» | R5 47/47, R6 49/49, R7 51/51, R8 52/52 pages; R9 compared all 52 page bitmaps by md5 and looked at the 14 that changed | **HOLDS** |
| A8 | «None of these readings found a gap or an error in the mathematics.» | as 2.1 #8 | **HOLDS** |
| A9 | «Between them, they found false or inexact sentences in this record and in §12, points of presentation, and defects of typesetting.» | as 2.1 #9 | **HOLDS** |
| A10 | «This summary replaces a version-by-version account; that account, the list of corrections of each version with its sources, every report and every grading are kept with the project.» | versions 1–7 (with the old account), CORRECTIONS v1→v2 … v6→v7 (each names its source), reports 3–9, gradings 3, 4, 6–9 are in `evidence/` (reading 5 has no grading, so «every grading» is every one that exists). This sentence claims that the list exists, not that it is complete | **HOLDS** |

**Note required by MISSION §2(b).** The sentences that speak of the readings of «each later version» / «every later version» include version 8, whose reading is this one. I judge them true **because my verdict on (a) is that no mathematics changed from version 7 to version 8** (§1).

**Verdict (b): NO — one clause is false** (2.1 #10). Every other new sentence is true.

## 3. (c) The pages (the list is in `checks/PAGES.md`)

**Render** (`logs/render.log`, VIGIA-FIN-OK, 19 s, 20 MB): v7 52 pages, v8 50 pages at 72 dpi; v8 also at 90 dpi (`scratch/p90/`). md5 of every page bitmap: **no v8 page is identical to any v7 page** (0 common md5). Expected: page 1 carries «version 8», §1.0 is shorter so every later page moves up, and every folio changes.

**Word comparison of the pdf text** (`scratch/py/wordcmp.py`: `pdftotext -layout` of both pdfs, the folio line of each page removed, `difflib` on the word sequences; `logs/wordcmp.log`, VIGIA-FIN-OK). 34 374 words in v7, 33 298 in v8; **98 differing runs**. Control (`logs/wordcmp_control.log`): one word of §7 deleted and one number of §12 changed in the v8 word list → 100 runs, the two damages listed (the check can fail). Every run placed by the headings before it (`scratch/py/wordcmp_where.py`, `logs/wordcmp_where.log`):
- header 1, §1.0 19, §13 15, Acknowledgements 1, Appendix A 29 — **the five places**;
- **33 runs in the unchanged body (§1.1–§12):** each one read (`scratch/body_runs.txt`). They are (i) the repeated header of a §12 table, which now falls at another page turn (v7 pp. 45–46 → v8 pp. 44–45: the same words, moved), and (ii) words of displays with stacked scripts that `pdftotext` reads in another order when the display sits at another height on the page (pp. 12, 17, 29, 34, 35, 36, 40). To make sure that nothing else is hidden there, `scratch/py/bodychars.py` (`logs/bodychars.log`, VIGIA-FIN-OK) compares the multisets of characters of the whole body §1.1–§12: **107 045 = 107 045 characters, identical multisets**; the references: **3 695 = 3 695, identical**.
- So **the text of the pdf differs from v7 only in the five places.**

**md = pdf on the new text** (`scratch/py/mdpdf_added.py`, `logs/mdpdf_added_v8.log`): every line added by the diff, cut at sentence ends, is found word for word in the v8 pdf text, except two pieces that differ only typographically (`'` printed `’` in «constructors’ reports»; `L`, `f` printed as math italic 𝐿, 𝑓 in §13) — both looked at in the text (`scratch/v8.txt` l. 94, 3232). Control (`logs/mdpdf_added_v7control.log`): on the v7 pdf, 26 pieces are missed.

**Every page at 90 dpi** (`scratch/p90/`, one line per page in `checks/PAGES.md`): 50 of 50 looked at, in order. **Nothing is broken.** The new text sits on p. 1 (header), p. 2 (§1.0), p. 47 (§13, Acknowledgements) and p. 49 (Appendix A, «Later versions»); each passage is whole and reads right on its page. The pages under 90 % full (`fill.py`, `logs/loose_fill_v7v8.log`) are p. 1 (title page), p. 7 and p. 23 (89.3 % each, before §1.7 and §7.2), and the last page; none is under the 85 % of check 5.

**Verdict (c): nothing is broken; the text of the pdf differs from v7 only in the five places.**

## 4. (d) The acceptance list and its controls

**The two runs** (exactly the commands of MISSION §2(d); `logs/acc_v8.log`, `logs/acc_v8_control.log`, both VIGIA-FIN-OK, 2 s, ≤ 111 MB): on v8 **9 of 9 PASS**; in control mode **9 of 9 FAIL** («controls fired: 9 of 9»). **The author's claim holds.** Details on v8: check 1 every numbered item found; 2: 13 914 words, none lost; 3: right edge 542 pt, 0 beyond; 4: no widow; 5: every page 2–49 ≥ 85 % (no exception needed; `fill.py` alone: under 90 % only p. 1, p. 7 and p. 23 at 89.3 %, p. 50); 6: no text line at 3× (the three named non-text lines only); 7: 126 fonts, all embedded, 0 missing glyphs; 8: 57 breaks listed, read: all right; 9: 32 keys, all cited and listed, unresolved only the five external items, numbers md = pdf (§12 108 = 108, §1.0–§1.4 7 = 7, §13 + App. A 6 = 6; v7 had 16 there — the numbers of the removed version-by-version account), DIFFERENCES 0.

**The two places where the list changed** (`diff` of `acceptance_v7_for_comparison.py` and `acceptance.py`, `logs/accdiff.log`): exactly two hunks, both with a comment signed «Grepy Escribano».

**(i) Check 6, `NOT_TEXT`:** `{('11','228'), ('9','276'), ('35','482')}` → `{('11','154'), ('9','168'), ('34','702')}`. I ran `loose.py 2.0` (the measure check 6 uses) on the bbox of both pdfs (`logs/loose_fill_v7v8.log`). The lines at 3× the median or more are, in both, exactly three:

| v7 | v8 | gap | kind | content |
|---|---|---|---|---|
| p11 y=228 | p11 y=154 | 14.37 pt (4.11× / 4.13×) | formula | the band of scripts of display (K): `(s) (r) min(r,s) (r−j) (s−j) (K)` |
| p9 y=276 | p9 y=168 | 12.77 pt (3.66× / 3.67×) | text | the §1.7 table row «formal dance; positions; covariant system» (three cells) |
| p35 y=482 | p34 y=702 | 11.11 pt (3.18× / 3.19×) | formula | the inline block matrix `[P C; B Dd]` with `G^{10}, G^{11}, G^{00}, G^{01}` |

**Same three lines, same gaps to the hundredth of a point**, as the new comment says; the medians are 3.49 and 3.48 pt. I looked at each at 200 dpi (`scratch/zoom/p11-11.png`, `p9-09.png`, `p34-34.png`): the (K) display with its limits set under and over the sum and its tag at the right; a table row whose cells are separated by the column gutter; a text line carrying a small bracketed matrix. **They look right; none hides a loose text line.** The positions are the new page and height of the same objects: p. 11 and p. 9 keep their page (§1.0 is shorter by about a sixth of a page, and those pages begin higher), p. 35 → p. 34. **HOLDS.**

**(ii) The damage of check 5:** `PGS[10]` → `PGS[12]` (page 10 → page 12 loses every word with `yMin` 450–799). `PGS = B.split('<page ')` has the text before the first page at index 0, so `PGS[12]` is page 12. The comment's reason is right: in v8 page 11 begins with the heading «2.2 The hyperalgebra and the dictionary» (seen on p. 11), so a page 10 cut short would be «a short page before a new section» — allowed — and check 5 would pass: the old damage would be dead. On page 12 it acts: the control log says **«p. 12: 54.0 % (next page begins «(c) On a vector of weight 𝑤 + 2𝑠, Ω ≡ (𝐻»)»**, FAIL, and page 13 does not begin a section (seen). And without the damage page 12 passes (v8 run: no page under 85 %). **The damage still acts on the check it is meant for. HOLDS.**
- One slip in the comment (not in the paper, not in the code): «page 13 begins inside §2.3». Page 13 begins inside the proof of Proposition 3.1, part (c), in **§3.1** (seen on pp. 12–13). The code does not depend on it. Style doubt 6.4.
- As reading 9 noted for v7, the damage of check 5 also makes check 2 fail (the control output lists 46 words as «lost», 45 of them from the cut of p. 12); check 2's own damage is visible in its own output («off: md 6, pdf 5»). Same in v8; not new.

The other controls act as in v7 (same code): 1 «2. (Λ).»; 3 a word past the margin; 4 «widow end.» on p. 2; 6 «alpha beta gamma delta» at 3.45×; 7 one missing glyph; 8 «spa-/ces»; 9 the 43 691 and the «Lemma 7.99» damages.

**Verdict (d): YES — the list passes 9 of 9 on v8, and its controls fail 9 of 9, each damage acting on its own check. The two changes of the list are right.**

## 5. After everything else (§4)

Opened only after §0–§4 of this report were on disk (diary line «BEFORE §4 of the mission: opening material/read_after/ now»). Read whole: `CORRECTIONS_v7_to_v8.md`, `text_edits.py`.

**`text_edits.py` does only what the diff shows.** Five replacements, each asserted unique: header, the §1.0 paragraph (one md line), the §13 bullets (closing paragraph kept), the Acknowledgements sentence, the Appendix A entries «Version 3» … «Version 7». I replayed it (`scratch/text_edits_copy.py` = the script with only its path changed to a copy of the v7 md; `logs/text_edits_replay.log`, VIGIA-FIN-OK): it prints «ok» five times, no «CHECK» line, and **its output is byte-identical (`cmp`) to the v8 md**. So the script, applied to v7, gives exactly v8, and the diff is its whole effect.

**The author's account against my findings:**

| account (CORRECTIONS_v7_to_v8) | my finding | agree? |
|---|---|---|
| §1: only five places; five hunks; nothing else | §1: the same (own diff = given diff; replay = v8) | **yes** |
| «No mathematical statement changed, no proof changed, and no number of a result changed» | §1, §2: the same (statement comparison v7 → v8: 0 differences) | **yes** |
| the numbers removed are «the 7 634 cells, the 301 clocks, the 192 024 cells, the 9 880 cells, and the 32 kinds …», «still in §12» | also removed from App. A: 7 620 and 14 (both still in §12.2, p. 45). The list is incomplete; nothing false follows | yes, incomplete |
| §2: «what was corrected, and what was left as it was, is listed with its source» was printed in place of a false «all were corrected»; checked against CORRECTIONS_v3_to_v4 and the «Not changed» list of CORRECTIONS_v5_to_v6 | the author checked that some things were left and are listed; not that **everything** left is listed. It is not: PD17, PD18, PD24, PD26, P2.7-b of reading 7 are in no list of corrections; reading 7's «seven kinds» of v5 have no erratum. This is my R1 | **no** — the clause the author wrote to repair a false sentence is itself too strong |
| §2: «only version 4 set the mathematics anew, and version 5 the page» | §2.4 A2 | yes |
| §2: «re-counted or re-ran with code of its own» (reader 9 re-ran the author's gate and wrote scripts of its own) | §2.4 A6 | yes |
| §2: «at every page, or at the changed pages after comparing all the pages by image» | §2.4 A7 | yes |
| §2: «none of these readings found a gap or an error in the mathematics … must be rechecked after reader 10» | I found none (§1); readers 7 and 8 also wrote «holds with gaps» (the account names only 6 and 9), likewise of the record | yes |
| §2: §13 checked by extracting every numbered statement of v1 … v7 (v1 → v2: Lemma 7.2(b), (Cut), Lemma 3.3 justification, Lemma K renumbering, renamed symbols; v2 → v3: Lemmas 7.9, 10.6(a), 10.10; v3 → v7: typography) | my `stmts.py` gives the same, and also the wording changes of v3 → v5 (Lemma 2.1 «In `R`,», Lemma 2.4 «Moreover», Lemma 3.3 order, Theorem 4.4, Corollary 10.9, Lemma 10.13), which the account calls «typography only»; they are wording, same content | yes (the account is slightly loose: «typography only» v3 → v7 is «typography and wording») |
| §3: check 6, same three lines, same gaps 14.37, 12.77, 11.11 pt; new positions (11,154), (9,168), (34,702) | §4 (i): the same, measured on both pdfs and looked at at 200 dpi | **yes** |
| §3: control of check 5 moved to page 12, fires «p. 12: 54.0 %»; «(page 13 begins inside §2.3)» | §4 (ii): fires as said. Page 13 begins inside **§3.1** (proof of Proposition 3.1(c)), not §2.3 | yes, with one slip (also in the comment of `acceptance.py`) |
| §3: 9/9 PASS, 9/9 FAIL in control | §4: the same | **yes** |
| §3: word diff of pdftotext: changes only in the five places; the rest is reading order, table headers, and «two words now hyphenated across a page turn («dis-/joint», pp. 18–19; «rea-/son», pp. 41–42)» | §3: the same result. The two page turns are **pp. 19–20** and **pp. 42–43** (seen on the pages; `logs/pageturn.log`: «joint. Hence» on p. 20, «son, such» begins p. 43) | yes, the page numbers in the account are one off |
| §3: 50 pages, all bitmaps differ from v7; every page looked at, nothing broken | §3: the same | **yes** |

**Verdict (§4):** the account agrees with what I found, except (a) the clause of §1.0 that I find false (R1), which the account presents as checked, and (b) three slips of the account itself, which do not reach the paper (the «§2.3» of page 13, the page numbers of the two page-turn hyphenations, the incomplete list of removed numbers). The edit script does exactly the diff.

## 6. Style doubts (not counted)

- **6.1** §13, «numbers, notation and typesetting changed»: «numbers» can be read as the numbering (Lemma K numbered 9.5 in v2, and §9 renumbered) or as numbers in the text. True either way.
- **6.2** Appendix A, «re-counted or re-ran with code of its own»: the scope of «with code of its own» is ambiguous. Reader 9 re-counted the houses by arithmetic and re-ran the author's gate; the sentence is true when read «re-counted, or re-ran with code of its own». «re-counted the numbers and re-ran the checks it concerned, with code of its own or the author's» would be unambiguous.
- **6.3** Appendix A, «with no access to the flights or the audits»: no report contradicts it, and none can prove it. Reader 5 later became the auditor (MISSION §1); its reading of v3 was cold.
- **6.4** `acceptance.py` (comment of the control of check 5) and CORRECTIONS_v7_to_v8 §3: «page 13 begins inside §2.3» — it begins inside §3.1. The code does not depend on it.
- **6.5** Appendix A, «Each later version made corrections asked for by the reading before it»: for version 8 the false sentence found by reading 9 was removed with the whole entry, not replaced as reading 9 proposed (grading 9: «moot»).
- **6.6** §12.2 (unchanged): «Six readers of the project (Appendix A)». Appendix A now names cold readers 1–4 and «cold reader 5 and each later one»; reader 6 is no longer named there, but the pointer still holds.
- **6.7** The control of check 5 still also makes check 2 fail (as reading 9 noted for v7), so «9 of 9 fired» alone does not show check 2's own damage; the output does («off: md 6, pdf 5»).

## 7. Sealed predictions, hits and failures

Sealed in `checks/SEALED.md` (md5 `f1df3a68fd87e477f286caa27651708a`, diary line «SEALED») before any measurement. **11 predictions: 10 hits, 1 failure.**

| # | prediction | result |
|---|---|---|
| P1 | no hunk touches mathematics (95 %) | **hit** (§1) |
| P2 | own diff = given diff, timestamps aside (90 %) | **hit** (`logs/owndiff.log`) |
| P3 | pdf text differs only in the five places (85 %) | **hit** (§3; 33 runs in the body are reading order and a moved table header, character multisets identical) |
| P4 | no page broken (85 %) | **hit** (50/50) |
| P5 | 9/9 pass, 9/9 fail in control (85 %) | **hit** |
| P6 | the two changes of the list: check 6 positions and the damage of control 5 (70 %) | **hit** on what changed; my guess of *why* the damage moved («its target text was removed») was wrong: it moved because page 11 now begins a section |
| P7 | check 6: same lines, same gaps, look right (70 %) | **hit** |
| P8 | the damage of check 5 still acts (55 %) | **hit** |
| P9 | at least one new sentence false (65 %) | **hit**, but not at any of the three places I ranked (App. A pdf clause, «Each later version made corrections…», §13 list): those hold. The false clause is in §1.0 («what was left … is listed») |
| P10 | «none of these readings found a gap or an error in the mathematics» holds (75 %) | **hit** |
| P11 | the corrections files list what was left, with sources (60 %) | **failure** — this is finding R1 |

## 8. My errors

- **M1.** Twice I wrote a word starting with `=` in zsh (`echo =====` in my very first command, after `cat MISSION.md`; `echo =======CONTROL` while reading the acceptance logs). Each time zsh stopped there; both commands were read-only, and I re-ran what was missing. The mission warns about exactly this.
- **M2.** Work outside `vigia.sh`: the `python3` heredocs that spliced sections into this report and `checks/PAGES.md` (eight, seconds, a few MB); one `pdftotext` of each pdf into `scratch/v7.txt`, `scratch/v8.txt` to look at two lines; the `cp` and `sed` that made `scratch/te_v8.md` and `scratch/text_edits_copy.py`; `pdfinfo`. All light; every computation that produced a result went through the watchdog (logs listed in §10).
- **M3.** In `checks/PAGES.md` I first wrote that p. 46 «ends about one sixth short»; `fill.py` puts it at 90 % or more. Corrected in the file and in §3, and noted in the diary.
- **M4.** In §4 I first wrote «37 words» lost in the control of check 2 (a number remembered from reading 9); the v8 control log lists 46 (45 from the cut). Corrected.
- **M5.** A mismatched quotation mark in §2.1 #10, fixed at once.
- **M6.** Some commands left the shell in `material/paper/` or `material/evidence/` (`cd` in a compound command); the next commands there were read-only. Nothing was written in `material/` (§10).
- **M7.** My first md5 check of the material excluded `ESTADO.md`, because I had already rewritten it with its first STATE line; so the md5 of the `ESTADO.md` I received was not checked.
- **M8.** In §1, hunk 5, I first wrote that some of the removed numbers were also printed in the «Version 2» entry of Appendix A; a grep shows they are all in §12 only (that entry holds 7 874). Corrected there.

## 9. What I did not read

- **The unchanged parts of the paper** (as the mission says): I looked at every page as a page and read only what the questions needed. I re-proved nothing.
- **§1.0, sentences 1–2** («Every proof behind the table was re-derived by a reader other than its author»; the chains read cold before the text): unchanged from v7, and not checkable here — the flights, the audits and the reports of cold readers 1 and 2 are not in `evidence/`.
- **The access of each reader** («no access to the flights or the audits»): not provable from the reports; only not contradicted.
- **Reports:** REPORT_COLD_3 only §0 and lines found by grep; REPORT_COLD_4 §0, §1.1 and lines found by grep; REPORT_COLD_6 §0, §1 items 1, 7–9, §2, §3, §6.1, §9 (not §1 items 2–6, §4, §5, §6.2–§6.5, §7, §8, §10); REPORT_COLD_5, _7, _8, _9 whole.
- **Gradings:** 7, 8, 9 whole; 3 and 4 by grep only; **6 not read.**
- **Versions 1–6:** only through my statement script and greps; not read as texts.
- **The html files** of v7 and v8: not read.
- **Tools:** read `acceptance.py`, `acceptance_v7_for_comparison.py` (by diff), `fill.py`, `loose.py`; not read `xrefs.py`, `md_vs_pdf.py`, `xrefs_reader8.py`, `numbers_reader8.py`, `margins.py`, `glyphs.py`. The «NOT a subsequence» lines that `md_vs_pdf.py` prints «for reading» (§1.0 table) are known artefacts (reading 9) and were not investigated.

## 10. Files with md5

Computed under the watchdog (`logs/md5_final.log`, `logs/md5_extra.log`, VIGIA-FIN-OK). **Material unchanged:** every file of `MANIFEST_md5.txt` but `ESTADO.md` (47 files: `material/`, `MISSION.md`, `CLAUDE.md`, `vigia.sh`) still has its md5 at the end (`logs/md5_material.log`: no «CHANGED» line); `material/tools/` still holds its 10 files and no `__pycache__`. Not in the table, because they change after it: `REPORT_COLD_10.md` (its md5 is on the last line of `logs/DIARY.md`), `logs/DIARY.md`, `ESTADO.md`, `logs/md5_final.log`, `logs/md5_extra.log`. `scratch/tmp/` holds the 2 temporary folders of `acceptance.py`. Nothing in `scratch/_BORRAR/`. Nothing was written outside this folder. `scratch/te_v8.md` (the replay of `text_edits.py`) has the md5 of the v8 md, as it must.

| md5 | file |
|---|---|
| c50849abac49d8fdf56d9a7eb378e4e7 | checks/PAGES.md |
| f1df3a68fd87e477f286caa27651708a | checks/SEALED.md |
| df21d1f287a34182c4f4928828fe7c6d | scratch/py/bodychars.py |
| 7fdf6f33099fa5e3a150f00c864a9d69 | scratch/py/mdpdf_added.py |
| efbad493afb87988a74da2d7d28f2a50 | scratch/py/stmts.py |
| 44e84228e5befff1c2c734b06de08c0a | scratch/py/wordcmp.py |
| a25edd9e4a7492ca76367d45ee91ac87 | scratch/py/wordcmp_where.py |
| ce4b33c944079debcf42166830d4faec | scratch/text_edits_copy.py |
| 8c656f70ae9a67fdb9b271b1a69de90a | scratch/te_v8.md |
| 4b574cf15a248d27ec62f0d567ebc90c | scratch/owndiff.txt |
| 6291611bdc41c08487984e2043789056 | scratch/body_runs.txt |
| f573ab029e52c241d8e4274981e3d94f | scratch/v7.txt |
| 2e700f75ad530838b82303d2a4cb3a71 | scratch/v8.txt |
| 763064fe2a6e5e7acef4cd7cd6b24ac1 | scratch/md5_r7.txt |
| c5c246eeba03665cf92d0a4c8b3fdfa8 | scratch/md5_r8.txt |
| df64f6ddd82de3f4d7996f4df3d099c0 | scratch/bbox_v7.html |
| dbf6dbc0e43f6a6c3cfcf6bfd10fcb48 | scratch/bbox_v8.html |
| c998dea44b1a53f9dfc32557aaca58b6 | scratch/sec2.md |
| ecda51c3f8e30a1413a05ad9686435cc | scratch/sec3.md |
| 8f765be259a6f846288fd117a90739fb | scratch/sec3b.md |
| bc511656756d39b7a192f78b0df63688 | scratch/sec4.md |
| db65d04f48ee22f6c862da1f28666cd0 | scratch/sec5.md |
| 8488d934061d49e331c4302b88c79639 | scratch/sec69.md |
| 2d31c6124d5a3a4aede275abc0b2be9a | logs/acc_v8.log |
| a57bb4dc9bf8c5ef34e9ac98c06ff0d0 | logs/acc_v8_control.log |
| b69b464cbb032089c9d5a5fb1bb2cc9b | logs/accdiff.log |
| 2d4ae1bdd3ad399391a9c2e89b337bd4 | logs/bodychars.log |
| abbeaa7d2be87517bea24828fd5acc69 | logs/loose_fill_v7v8.log |
| 6a1d31702c8e59d487e53c04b98fd24c | logs/md5_material.log |
| 04b1d4ed5251d986502ac4e66ad7b7f5 | logs/md5check.log |
| 8da4b90d8f9cc66596809b4c904ac966 | logs/mdpdf_added_v7control.log |
| c2da47098c59f5364fd31269338da9a7 | logs/mdpdf_added_v8.log |
| b65c86d59d791766e3cbb5ce705adfc4 | logs/owndiff.log |
| aad37c35e29bb48d8a1f7decd102aa96 | logs/pageturn.log |
| 2f67b7c340a6576b8b46007e2c05bd2a | logs/render.log |
| c3f8cab7774f39d9be0c50b4fdd6d533 | logs/stmts.log |
| 221fcf6b4804aa5c3ff604f17f3782ba | logs/stmts_control.log |
| f5dcbddb25eac50b92af20f236bdf583 | logs/text_edits_replay.log |
| 974e4beff7abd3baf5ea823e3e68f98c | logs/wordcmp.log |
| 70ed0f141d7a00af0799b3aeff3bd2db | logs/wordcmp_control.log |
| ee6d3b14c8097a853b2e324d9c3c5576 | logs/wordcmp_where.log |
| 1920af61574361b7f4febdb266044c70 | logs/zoom3.log |
| 0fdcd6d182c86075f289bcabbd465eb4 | scratch/p90/ (50 files, md5 of the sorted md5 -r list) |
| ca4b57f2ef33c6df9ea2f40da465850c | scratch/r7/ (52 files, md5 of the sorted md5 -r list) |
| d17141293152b67772c5c8043afac93c | scratch/r8/ (50 files, md5 of the sorted md5 -r list) |
| 35b8f8c88e0c05eb1c5a5c3717e736aa | scratch/zoom/ (3 files, md5 of the sorted md5 -r list) |
| 68a26a22ca9e2fa849eeb4451bf3bbc8 | scratch/v7_control.md |
