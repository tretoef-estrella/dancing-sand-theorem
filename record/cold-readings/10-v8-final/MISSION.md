# COLD READING 10 — the last reading of «The Dancing Sand Theorem», version 8

Written by Grepy Escribano, chief auditor of the hypercube project, on 6 October 2026.

**You are «Grepy el lector frío del cubo 10».** You never saw this work being built. Version 8 is meant to go to a reader outside the project. It differs from version 7 in five places only: the header, one paragraph of §1.0, the bullets of §13, one sentence of the Acknowledgements, and the end of Appendix A. These places tell the story of the work and its readings. Version 7 told it version by version; version 8 tells it once, in sentences that do not name the current version.

**This mission is CLOSED.** You answer four questions, (a) to (d) of §2, and nothing else. For every error you find you write the exact replacement text, word for word. Your replacements will be applied as you write them, and there will be no further reading after yours. So write them as you want them printed.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_10.md` with the section headings of §5, empty.
2. Put every verdict into it the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_10.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_8_FINAL/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only. Open `material/read_after/` only when §4 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder; the log is the FIRST argument. The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate in `logs/DIARY.md` BEFORE each run. A log that does not end in `VIGIA-FIN-OK` is not a result.
- In zsh, never start a word with `=`; quote heredocs `<<'EOF'`.

**How you grade:**
- **HOLDS** — re-checked in your own words.
- **ERROR** — a sentence, a number or a step is false. Give the replacement text.
- **PRESENTATION** — something on the page is wrong. Give the fix.
- «I did not read it» is an honest verdict.

Seal your predictions in `checks/SEALED.md` before you measure.

**Stop rule:** if you find that a numbered statement or a number of a result changed or disappeared from version 7 to version 8, stop that item, write it with the exact place, and tell Rafa in capitals.

Chat with Rafa in Spanish; write documents in English.

**The standard is CORRECT, not perfect.** You are not the typesetter, and nothing about typography is asked of you. The following are not defects: a loose line, a short page before a section, a word hyphenated across a page turn that the acceptance list allows, a break that TeX would also allow, a choice of style. List style doubts once, apart, and do not count them.

## 1. What you have

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v8.md`, `.pdf` (50 pages), `.html` — the text you grade;
- `THE_DANCING_SAND_THEOREM_v7.md`, `.pdf` (52 pages), `.html` — the previous version;
- `DIFF_v7_to_v8.txt` (`diff -u`, 61 lines).

**`material/evidence/`** — what the five places speak about:
- `reports/` holds the reports of cold readings 3 to 9 (`REPORT_COLD_<n>.md`) and the auditor's gradings of readings 3, 4, 6, 7, 8 and 9 (`CALIFICACION_LECTOR_FRIO_<n>_v1.md`). Reading 5 was done by the reader who later became the auditor; its report is here, and it has no separate grading.
- `versions/` holds versions 1 to 6 of the text (md). With version 7, they let you check what §13 says about which numbered statements changed.
- `corrections/` holds the author's lists of corrections, `CORRECTIONS_v1_to_v2.md` to `CORRECTIONS_v6_to_v7.md`. The new §1.0 says that what was corrected, and what was left as it was, «is listed with its source in the record kept with the project»: these are that record.

**`material/tools/`:** the acceptance list `acceptance.py` with its scripts, as used on version 8; and `acceptance_v7_for_comparison.py`, the list as used on version 7.

**`material/read_after/`:** the author's own account of the change (`CORRECTIONS_v7_to_v8.md`) and the edit script (`text_edits.py`).

## 2. The four questions

**(a) Did anything mathematical, or any number of a result, change or disappear from version 7 to version 8?** Work on the diff.
- For every hunk: does it touch a numbered statement, a proof, a table of §12, or any number that is a result? Write what it removes and what it adds.
- Then make sure the diff is the whole change: run `diff -u` yourself on the two md files and compare with `DIFF_v7_to_v8.txt`.

**(b) Is every sentence of the new text true?** The new text is the new paragraph of §1.0, the new bullets of §13, the changed sentence of the Acknowledgements, and the entry «Later versions» of Appendix A. Take every sentence, and every clause of a long sentence. Check each one against `material/evidence/`. In particular:
- every claim about who read what, when, with what access, with what code, and what they found;
- «none of these readings found a gap or an error in the mathematics»;
- what §13 says about which numbered statements changed after the first version, and «No other numbered statement changed in what it states». Compare the numbered statements of versions 1, 2, 3 and 7; take care that the (Cut) of Theorem 7.8 is a list under the theorem;
- «what was corrected, and what was left as it was, is listed with its source»;
- «version 4 also set the mathematics anew, and version 5 the page».

This text has no sentence about version 8 itself, on purpose. Some sentences speak of the readings of «each later version»; your reading is the reading of version 8. Judge them as true **if your own verdict on (a) is that no mathematics changed**. Say so in your report.

**(c) The pages.**
- Render both pdfs and compare them. Version 8 is shorter in §1.0, so every later page moves up and every page bitmap differs.
- Check that the text of the pdf differs only in the five places. Do this by a word comparison of `pdftotext` of the two pdfs (the page numbers removed), not by bitmaps.
- Look at every page of version 8 at 90 dpi. One line per page in `checks/PAGES.md`. Is anything broken?

**(d) The acceptance list.**
- Run it on version 8, and in control mode. The estimate is under 200 MB and under 1 minute each:
  `zsh vigia.sh logs/acc_v8.log 'export TMPDIR=$PWD/scratch/tmp; mkdir -p $TMPDIR; cd material/tools && python3 acceptance.py ../paper/THE_DANCING_SAND_THEOREM_v8.md ../paper/THE_DANCING_SAND_THEOREM_v8.pdf'`
  and the same with `control` added at the end (`logs/acc_v8_control.log`).
- The author says 9 of 9 pass, and 9 of 9 fail in control mode.
- The list for version 8 differs from the one for version 7 in two places. Find them yourself with `diff`, and judge them:
  - Check 6 names, by page and height, three lines that are not text. Are the three lines it names in version 8 the same lines as in version 7? Do they have the same gaps, and do they look right on the page?
  - The control of check 5: does the damage still act on the check it is meant for?

## 3. What you do not do
Do not re-read the unchanged parts of the paper. Do not re-prove the theorems. Do not judge the typography beyond «is anything broken». Do not propose new sentences except as replacements for sentences you find false.

## 4. After everything else
Open `material/read_after/` only when §2 is written. Does the author's account in `CORRECTIONS_v7_to_v8.md` agree with what you found? Does `text_edits.py` do only what the diff shows?

## 5. Sections of REPORT_COLD_10.md (create them empty first)
0. **First lines:**
   - Did anything mathematical change from version 7 to version 8? NO / YES (where).
   - Is every new sentence true? YES / NO.
   - Is anything broken on the pages? NO / YES.
   - Does the acceptance list pass, and do its controls fail? YES / NO.
   - **The list of replacements:** for each error, the place, the exact text to remove and the exact text to print. Write «none» if there are none.
1. (a) The hunks of the diff
2. (b) The new sentences, one by one
3. (c) The pages (the list is in `checks/PAGES.md`)
4. (d) The acceptance list and its controls
5. After everything else (§4)
6. Style doubts (not counted)
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_10.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the first lines of §0.
