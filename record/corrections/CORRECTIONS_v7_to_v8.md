# The Dancing Sand Theorem — corrections from version 7 to version 8

Grepy Escribano, 6 October 2026. Plan: `ARRANQUE_GREPY_ESCRIBANO_v1.md` §3 (plan A, the static record, approved by Rafa: «Rafa aprueba el registro estático»).

Version 7: md `e950ed939cd2bb9180af8533e7eaa918`, pdf `feb4ab4c81e479d4f0ebcdf5825421e8` (52 pages). Version 8: md `8c656f70ae9a67fdb9b271b1a69de90a`, pdf `d001c2b63db0557c817c658f623e8b14` (50 pages), html `bc76bd98537f3d63a5d76e3482be546f`.

## 1. What changed

Only five places, by `paper/v8_edits/text_edits.py` (md5 `f0a55737eac0a790dcb7a6720028d529`; every replacement asserted unique). The diff is `paper/v8_edits/DIFF_v7_to_v8.txt` (md5 `d184637de972162e745edd39b3b49dda`): five hunks, one per place, nothing else.

1. **Header:** «version 7» → «version 8».
2. **§1.0, the paragraph after the table:** the version-by-version account of the readings is replaced by a static one. No sentence names the current version.
3. **§13:** the bullets «Changed in version 4 … 7» and «a cold reading of the changes of version 7» are removed. A bullet «Numbered statements changed after the first version» says exactly which statements changed. The first bullet and the closing paragraph are kept.
4. **Acknowledgements:** «The work took five days, from 2 to 6 October 2026. It began on 2 October 2026 as a search» → «The work began on 2 October 2026 as a search». The length of the work is no longer stated; its start is kept.
5. **Appendix A, «Readings»:** the entries up to «Version 2» are kept. The entries «Version 3» to «Version 7» are replaced by one entry, «Later versions».

**No mathematical statement changed, no proof changed, and no number of a result changed.** The numbers removed are those of the record of the readings (the 7 634 cells, the 301 clocks, the 192 024 cells, the 9 880 cells, and the 32 kinds of typesetting defects of the old Appendix A). They are still in §12 where they belong, and in the reports.

## 2. How each clause was checked (the drafts of the arranque §5 were not printed as written)

Sources: the reports and gradings of readers 3–9 (`reports/LECTOR_FRIO_<n>/`), the earlier versions in `paper/historico/`, and `CORRECTIONS_v1_to_v2.md` … `CORRECTIONS_v6_to_v7.md`.

- **«all were corrected» (draft §1.0) — removed: false.** Version 4 left two defects of typesetting (`CORRECTIONS_v3_to_v4.md`). Version 6 left loose lines, the table design, the Type 3 fonts and breaks after a relation, as not faults (`CORRECTIONS_v5_to_v6.md`, l. 59). Printed instead: «what was corrected, and what was left as it was, is listed with its source in the record kept with the project».
- **«Versions 3 and later … set the mathematics and the page anew» (draft App. A) — false.** Only version 4 set the mathematics anew, and version 5 the page (old Appendix A, entries «Version 4» and «Version 5»). Printed as such.
- **«on 5 and 6 October» → «from 5 October 2026».** Reader 5 started on 5 Oct 18:35, reader 6 on 5 Oct 21:21, and readers 7–9 read on 6 Oct. Reader 10 may read later.
- **«re-ran with its own code» → «re-counted or re-ran with code of its own».** Reader 9 re-ran the author's `gate_strict_cut.py` and also wrote scripts of its own (`md_vs_pdf9.py`, its own diff). Readers 5–8 wrote their own (`REPORT_COLD_5` §item 11; `REPORT_COLD_6` l. 123; `REPORT_COLD_7` l. 48; `REPORT_COLD_8` l. 65, 98).
- **«looked at the pdf: at every page, or at the changed pages after comparing all the pages by image».** Readers 5–8 looked at every page (`REPORT_COLD_6` l. 155: «All 49 pages were looked at»). Reader 9 compared every page by bitmap md5 and looked at the changed ones (`REPORT_COLD_9` §3, l. 78).
- **«none of these readings found a gap or an error in the mathematics».** Readings 5–9 found no gap or error in the mathematics. Readers 6 and 9 wrote «holds with gaps» about the text: the gaps were in the record, not the mathematics (`REPORT_COLD_6` l. 7; `REPORT_COLD_9` l. 6). This sentence must be rechecked after reader 10.
- **«No other numbered statement changed in what it states; numbers, notation and typesetting changed» (§13).** This was checked by extracting every numbered statement of v1 … v7 and comparing them word by word, plus the block of Theorem 7.8 with its (Cut) bullets, which the extractor alone misses.
  - **v1 → v2:** only Lemma 7.2(b) (restated) and the (Cut) of Theorem 7.8 (made strict) changed in content. Lemma 3.3 gained a justification inside its parenthesis; what it states is the same. All other differences are renumbering (Lemma K → Lemma 9.5, Proposition 9.5 → 9.6, Lemmas 9.6–9.8 → 9.7–9.9, Theorem 9.9 → 9.10) and renamed symbols (κ_h, ρ_h → in_h, out_h; φ → ϑ; σ → sat, β; doblar/paso → twist/split move).
  - **v2 → v3:** Lemma 7.9 (strengthened), Lemma 10.6(a) («even») and Lemma 10.10 (the quantifier).
  - **v3 → v7:** the typography only (`Z` → `ℤ` and the like). Theorem 7.8 is identical from v2 to v7 apart from `Z` → `ℤ`.
- **«Version 2» as the place to cut Appendix A — kept.** §13 still names the changes of versions 2 and 3, and the entries «Version 1» and «Version 2» carry the only gap and its repair.
- **«cold readers 5 onwards» (my own first wording) — reworded** to «cold reader 5 and each later one». The pdf broke «on-/wards» across a page with a piece of two letters (check 8, below).

## 3. Build and checks

- Builder: `paper/build_v8.sh` = `build_v7.sh` with `v7` → `v8` (md5 `2ba7fdc265b58431383d8fd83db83038`). `paper/md2html_v8.py` is an exact copy of `md2html_v7.py` (`cmp` identical, md5 `85eef1149fc4a81a9b2370d9cee99d4d`). `phtml.py` untouched. **No new rule.**
- Build: `logs/v8_build.log`, `VIGIA-FIN-OK`, 7 s, peak 0.95 GB.
- **Acceptance list on v8: 9 of 9 PASS** (`logs/v8_acceptance.log`). **Control mode: 9 of 9 FAIL** (`logs/v8_acceptance_control.log`). Both ran with `paper/checks_v8/acceptance.py`, a copy of `checks_v7/acceptance.py` with two changes, both written into its comments (`diff -r checks_v7 checks_v8` shows only these):
  1. **Check 6, `NOT_TEXT`.** The check names, by (page, y), the three lines that were looked at and are not text: a band of script fragments of the display (K), a row of the vocabulary table, and the labels of a matrix. Its own comment says: «if the build moves them, the check fails and they must be looked at again». The build of v8 moved them, so check 6 failed. I looked at them again on pages 11, 9 and 34 of v8 at 85 dpi. They are the same three lines with the same gaps as in v7 (14.37, 12.77, 11.11 pt; measured by `loose.py` on both pdfs). Their positions were updated from (11,228), (9,276), (35,482) to (11,154), (9,168), (34,702).
  2. **Control of check 5.** It cut page 10 short. In v8 page 11 begins §2.2, so a short page 10 is allowed and the control no longer fired (control mode gave 8 of 9). The damage now falls on page 12 (page 13 begins inside §2.3); the control fires («p. 12: 54.0 %»).
- **First build, not kept:** acceptance 7 of 9. Check 6 failed for the reason above. Check 8 failed on «on-/wards» across pages 48–49, a real break with a piece of two letters, in my own new text; it was reworded (§2) and rebuilt.
- **Text of the pdf:** a word-by-word diff of `pdftotext` of v7 and v8, page numbers removed, shows changes only in the five places. The other differences are the order in which `pdftotext` reads scripts, table headers and the reference keys, and two words now hyphenated across a page turn («dis-/joint», pp. 18–19; «rea-/son», pp. 41–42), which the acceptance list allows.
- **Pages.** The shorter §1.0 paragraph moves every later page up (52 → 50 pages), so all 50 page bitmaps differ from v7 (`pdftoppm -r 50`, md5). **Every one of the 50 pages was looked at at 85 dpi:** nothing is broken.

## 4. Erratum for `CORRECTIONS_v6_to_v7.md`

(Appended to that file, below its last line.)
- l. 13, «No mathematical statement changed, and no number»: false as to «no number». The dates of the work and one row of §12.2 changed. Reading 9, `REPORT_COLD_9` §0.
- l. 35, «The other 39 pages are unchanged»: they are 38 (52 − 14).

## 5. Errors of the scribe in this turn

- The first wording «cold readers 5 onwards» broke badly in the pdf. Caught by check 8 and reworded.
- One temporary file was written to `/tmp` (`/tmp/a3`, a scratch copy of a statement block) instead of the scratchpad. It is harmless and outside the project.

## 6. After cold reading 10 (added 6 October 2026; the lines above are left as they were written)

Reading 10 (`reports/LECTOR_FRIO_10/`, report md5 `9b71de2c596725229d0459f7c3e27522`, graded HIGHEST) found nothing mathematical changed and nothing broken; the acceptance list passes 9/9 and fails 9/9 in control. It found one false clause, in §1.0, and gave its replacement R1, applied word for word by `paper/v8_edits/reader10_replacement.py` (diff `paper/v8_edits/DIFF_R1_reader10.txt`, one hunk):
- removed: «what was corrected, and what was left as it was, is listed with its source in the record kept with the project (Appendix A).»
- printed: «the list of corrections of each version, with its sources, and every report are kept with the project (Appendix A).»
The clause was false because the files of corrections do not list everything that was left (reading 7's PD17, PD18, PD24, PD26 are in none: checked by grep). My §2 above says it was checked; it was checked only in part.

Rebuilt: md `016fc36d0fcfcb807c85fe0307267893`, pdf `f16c894a7135008b22a2b5ea9b3046ac` (50 pages), html `f7324734d8043df3e9449c9a69316283`. Acceptance 9/9 PASS, control 9/9 FAIL (`logs/v8_acceptance_R1.log`, `logs/v8_acceptance_control_R1.log`). Only page 2 differs from the v8 built before reading 10 (bitmaps at 50 dpi); looked at at 85 dpi. No new cold reading (termination rule). **Version 8 is final.**

Errata of this file, found by reading 10: in §3, «page 13 begins inside §2.3» → «inside §3.1» (the same slip is in the comment of `checks_v8/acceptance.py`, which the code does not use); the two page-turn hyphenations are on pp. 19–20 and 42–43, not 18–19 and 41–42; in §1, the numbers removed from Appendix A also include 7 620 and 14 (both still in §12.2).
