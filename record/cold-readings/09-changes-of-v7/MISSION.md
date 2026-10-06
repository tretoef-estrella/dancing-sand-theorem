# COLD READING 9 — the changes of version 7 of «The Dancing Sand Theorem»

Written by Grepy Muchas Pilas, chief auditor of the hypercube project, on 6 October 2026.

**You are «Grepy el lector frío del cubo 9».** You never saw this work being built. Version 7 is meant to go to a reader outside the project. Your question is one, and it is narrow: **are the changes of version 7 correct?**

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_9.md` with the section headings of §5, empty.
2. Put every verdict into it the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_9.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_7_CHANGES/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only. Open `material/read_after/` only when §4 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder; the log is the FIRST argument. The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate in `logs/DIARY.md` BEFORE each run. A log that does not end in `VIGIA-FIN-OK` is not a result.
- In zsh, never start a word with `=`; quote heredocs `<<'EOF'`.

**How you grade:** HOLDS (re-checked in your own words) / GAP / ERROR (a sentence, number or step is false) / PRESENTATION (something on the page is wrong). «I did not read it» is an honest verdict. Seal predictions in `checks/SEALED.md` before measuring. **Stop rule:** if you find a counterexample to a numbered statement, stop that item, write it with the exact input, and tell Rafa in capitals. Chat with Rafa in Spanish; write documents in English.

**The standard is CORRECT, not perfect.** A loose line, a short page before a section, a break that TeX would also allow, or a choice of style is not a defect. List style doubts once, apart, and do not count them.

## 1. What you are reading

**`material/paper/`:** `THE_DANCING_SAND_THEOREM_v7.md`, `.pdf` (52 pages), `.html` — the text you grade; `THE_DANCING_SAND_THEOREM_v6.md`, `.pdf` — the previous version; `DIFF_v6_to_v7.txt` (`diff -u`, 124 lines); `CORRECTIONS_v6_to_v7.md` — the author's list of the changes.

**`material/evidence/`:** what you need to check the changed facts:
- `family_lattice_31_10.log`, `family_lattice_63_8.log` — the two logs of the check behind the changed row of §12.2 on the lattices `T(λ)`;
- `REPORT_COLD_4.md` — use it ONLY to check the range of houses that §12 and Appendix A give to the fourth reader (search for «65 532»); do not read the rest;
- `gate_strict_cut.py` — to check the range of `k` of the 16 380 houses.

**`material/sources/`:** the source of [LZ22]. **`material/tools/`:** the acceptance list `acceptance.py` with its scripts.

## 2. The work

1. **Every hunk of the diff.** Does it touch a numbered statement or a proof step? Does it change content? Report any change of a symbol, a number, a quantifier or a hypothesis.
2. **Every changed sentence, against the text and the evidence:**
   - §13: the sentence on what changed in versions 2 to 7 — check every statement it names against the text of version 7 (Theorem 7.8, Lemma 7.2(b), Lemma 7.9, Lemma 10.6(a), Lemma 10.10) and against Appendix A; is «no other numbered statement changed» true as far as the record lets you see?
   - §12.2, the row on the lattices `T(λ)`: every number against the two logs.
   - §12 and Appendix A, the ranges of houses (`k = 0` included or not): check `43 690`, `65 532`, `16 380` by arithmetic (the number of houses with given `k` and `α` is `4^k`, see §7.3: `I ⊆ [0, k)`, `0 ≤ ℓ < 2^k`), against the evidence.
   - §1.7 «Why dance»: against Propositions 4.1 and 4.2.
   - Proposition 9.6 (H): «if `Z_1` is positive there» — is it exact?
   - [LZ22]: against the source.
   - The record: §1.0, §13, Appendix A, the Acknowledgements (dates). Is every sentence about what was read cold, when and by whom exact, inside the text itself? Is anything said to be left undone?
3. **The pages that changed.** The author says pages 1, 2, 3, 9, 30, 44 and 46–52 differ from version 6. Check this yourself (render both pdfs and compare), and look at every changed page at 90 dpi. One line per page in `checks/PAGES.md`.
4. **md and pdf say the same** on the changed passages.
5. **The acceptance list.** Run it on version 7 and in control mode (estimate: under 200 MB, under 1 minute each):
   `zsh vigia.sh logs/acc_v7.log 'export TMPDIR=$PWD/scratch/tmp; mkdir -p $TMPDIR; cd material/tools && python3 acceptance.py ../paper/THE_DANCING_SAND_THEOREM_v7.md ../paper/THE_DANCING_SAND_THEOREM_v7.pdf'`
   and the same with `control` added at the end (`logs/acc_v7_control.log`). The author says 9 of 9 pass, and in control mode 9 of 9 fire. Read the damages of the control mode in `acceptance.py`: does each one act on the check it is meant for?

## 3. What you do not need to do
Do not re-read the unchanged parts of the paper, and do not re-prove the theorems. The previous reading read the whole paper.

## 4. After everything else
Open `material/read_after/` only when §2 is written: the report of the previous reading (`REPORT_COLD_8.md`) and its grading. Is every defect it found fixed in version 7, with the fix it proposed or an equivalent one?

## 5. Sections of REPORT_COLD_9.md (create them empty first)
0. **First lines:** Do the changes of version 7 hold as written? HOLDS / HOLDS WITH GAPS / DOES NOT HOLD. Is version 7 ready to be sent? YES / AFTER CORRECTIONS (the exact list, with page, line and fix) / NO.
1. The hunks of the diff
2. The changed sentences, one by one
3. The changed pages (the list is in `checks/PAGES.md`)
4. md against pdf on the changed passages
5. The acceptance list and its controls
6. After everything else (§4)
7. Style doubts (not counted)
8. Sealed predictions, hits and failures
9. My errors
10. What I did not read
11. Files with md5

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_9.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the first lines of §0.
