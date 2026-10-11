# COLD READING 11 — the changes of «The Dancing Sand Theorem», version 9, and the corrections of its Lean certificate

Written by Grepy Escribano, chief auditor of the hypercube project, on 11 October 2026.

**You are «Grepy Cotejo».** You never saw this work being built. The paper «The Dancing Sand Theorem» determines the whole 2-part of the sandpile group of the hypercube. Version 8 is public. Its whole proof has since been checked in the proof assistant Lean 4 with Mathlib, and a **Lean certificate** describes that check. The certificate was read cold by another reader («Grepy Lacre»), who found four errors in the certificate's own record and none in a statement; the author corrected them. Version 9 of the paper adds the account of the Lean check and corrects one sentence of §1.3.

You read **two things, and only the places that changed:**
1. the changes from version 8 to version 9 of the paper (the diff, 14 hunks);
2. the corrections made to the Lean certificate after the first cold reading (the diff before/after, 14 hunks, and the regenerated Table 6a).

**This mission is CLOSED.** You answer the five questions (a) to (e) of §2, and nothing else. For every error you find you write the exact replacement text, word for word. Your replacements will be applied as you write them, and there will be no further reading after yours. So write them as you want them printed.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_11.md` with the section headings of §5, empty.
2. Put every verdict into it the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_11.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_9_CHANGES/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only (check it against `MANIFEST_md5.txt` at the start and at the end). Open `material/read_after/` only when §4 says so.

**How you run.**
- Run every Python with `PYTHONDONTWRITEBYTECODE=1` set, so that nothing is written into `material/`.
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder; the log is the FIRST argument. The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate in `logs/DIARY.md` BEFORE each run. A log that does not end in `VIGIA-FIN-OK` is not a result.
- No Lean is run in this reading (the Lean sources are here to be counted and read, not compiled).
- In zsh, never start a word with `=`; quote heredocs `<<'EOF'`.

**How you grade:**
- **HOLDS** — re-checked in your own words or with your own code.
- **ERROR** — a sentence, a number or a step is false. Give the replacement text.
- **PRESENTATION** — something on the page is wrong. Give the fix.
- «I did not check it» is an honest verdict.

Seal your predictions in `checks/SEALED.md` before you measure.

**Stop rule:** if you find that a numbered statement of the paper, or a number of a result, changed or disappeared from version 8 to version 9, stop that item, write it with the exact place, and tell Rafa in capitals.

Chat with Rafa in Spanish; write documents in English.

**The standard is CORRECT, not perfect.** Nothing about typography is asked of you beyond «is anything broken». A loose line, a short page that the acceptance list declares, or a choice of style is not a defect. List style doubts once, apart, and do not count them.

## 1. What you have

**`material/paper/`:** `THE_DANCING_SAND_THEOREM_v9.md`, `.pdf` (51 pages), `.html` — the text you grade; the same for version 8 (50 pages); `DIFF_v8_to_v9.txt` (`diff -u`).

**`material/evidence/`** — what the changes speak about:
- `certificate/`: the Lean certificate as it is now (`LEAN_CERTIFICATE_DANCING_SAND_v1.md`, `.pdf`, and its source `.src.md`), the same before the first cold reading (`*_antes_de_la_lectura_fria.*`), `DIFF_certificate_before_after.txt`, the scripts that generate it (`fill.py` cuts every Lean statement out of `../final_checks/CertCubo.log`; `make_tables.py` builds Tables 6a and 6b from `data/` and from the brute-force logs; `cold_fixes_LACRE.py` applies the corrections), and `make_tables_antes_de_la_lectura_fria.py`.
- `cold_reading/REPORT_CUBO_LEAN_1.md`: the report of the first cold reading of the certificate.
- `final_checks/`: `CertCubo.log` (every Lean statement and definition as Lean prints it), `CheckCubo_postclean.log`, `DepsCubo_postclean.log`, and the 68 final check logs of the pieces (`checkC<p>.log`; for C31 `checkC31b.log`).
- `brute_force/`: the brute-force logs of the 68 pieces (`chkC<p>.log`), with some earlier runs kept under longer names.
- `lean/`: the Lean sources (`project/RequestProject/`, 416 files with `Main.lean`; the lake files), the clean-rebuild log and the source manifest.
- `sources/`: Gao, Marx-Kuo, McDonald, Yuen, arXiv:1912.06919v3 (text), and Bai 2003 (text).

**`material/tools/`:** the acceptance list `acceptance.py` with its scripts, as used on version 9; `acceptance_v8_for_comparison.py`, the list as used on version 8.

**`material/builder/`:** the scripts that build the paper: `md2html_v8.py`, `md2html_v9.py`, `phtml.py`, `pmath.py`, `build_v8.sh`, `build_v9.sh` (the last two use the author's paths; read them, do not run them).

**`material/read_after/`:** the author's account of the change (`CORRECTIONS_v8_to_v9.md`), the edit script (`text_edits.py`), and the author's grading of the first cold reading.

## 2. The five questions

**(a) Did anything mathematical, or any number of a result, change or disappear from version 8 to version 9?** Work on the diff.
- For every hunk: does it touch a numbered statement, a proof, a table of §12.1–§12.2, or a number that is a result? Write what it removes and what it adds.
- Make sure the diff is the whole change: run `diff -u` yourself on the two md files and compare with `DIFF_v8_to_v9.txt`.

**(b) Is every new sentence of version 9 true?** The new text is: the bold sentence of the Abstract; the sentence added to the paragraph of §1.0; the sentence of §1.3 on the edges of the folded cube; question 6 of §11; all of §12.3; the bullets and the closing sentence of §13; the paragraph added to the Acknowledgements; the entry «Formal verification» of Appendix A; the four new references. Take every sentence, and every clause of a long sentence. Check each one against `material/evidence/`. In particular:
- §1.3: is the new description of the folded cube right, and is it the same graph as «the Cayley graph of `𝔽_2^n/⟨𝟙⟩` with the images of the unit vectors»? Check `n = 2` and `n ≥ 3`. Is «each edge of `Q_n/⟨𝟙⟩` is the image of two edges of `Q_n`» true?
- §12.3, «What Lean proves»: does each Lean name there exist in `CertCubo.log`, and does its statement, as Lean prints it, say what the sentence says (the range of `n`, «for `n ≥ 2`», «Theorem 4.1 for `n ≥ 3`»)? Is Gao et al.'s Theorem 4.1 stated for `n ≥ 2` in the source?
- §12.3, «Nothing is cited», «no `sorry`», «three standard axioms»: against `CheckCubo_postclean.log`, the final check logs and your own search of the sources.
- §12.3, «415 Lean files, 60 940 lines and 3 449 theorem and lemma declarations», «416 modules … exit code 0»: recount them yourself from `lean/project/` and `lean/clean_rebuild_2026-10-10.log`. Say how you count (a declaration preceded by an attribute such as `@[simp]` is a declaration; a comment is not).
- §12.3, «Read cold»: every claim about what the first cold reader did and found, against `cold_reading/REPORT_CUBO_LEAN_1.md`.
- §12.3, «What Lean does not state»: against §2 of the certificate.
- §12.3, the sentence on groups and `ℤ_2`-modules: is the argument right?
- The four new references: are the bibliographic data right, as far as you can tell without the internet? Say which you could not check.

**(c) Are the corrections of the Lean certificate right?** Work on `DIFF_certificate_before_after.txt` and on Table 6a.
- For each of the four errors and seven presentation points of the first cold reading (its §3), is it corrected, and is the correction itself true?
- Table 6a, column «Brute force before sending»: it is now generated from the brute-force logs. For every one of the 68 rows, does the number of checks (and «in K kinds» where the log reports counts by kind only) agree with `brute_force/chkC<p>.log`? Write your own parser; do not run `make_tables.py`.
- §4 of the certificate: 885 lines of `#print axioms` (868 / 12 / 4 / 1) over the 68 final check logs.
- §7: «Theorem and lemma declarations in code: 3 449», and the 213 declarations preceded by an attribute.
- Is any sentence of the certificate that the corrections did not touch now false because of them?

**(d) The pages.**
- Version 9 has 51 pages, version 8 has 50. The author says pages 6–42 of version 9 are identical, image by image, to pages of version 8, and that the other 14 were looked at. Check it: render both at 40 dpi and compare.
- Check by a word comparison of `pdftotext` (page numbers removed) that the text of the pdf differs only where the md does.
- Look at every page that differs, at 90 dpi, and at every page of the certificate's pdf that the diff touches. One line per page in `checks/PAGES.md`. Is anything broken?

**(e) The acceptance list and the builder.**
- Run the list on version 9, and in control mode. The estimate is under 200 MB and under 1 minute each:
  `zsh vigia.sh logs/acc_v9.log 'export TMPDIR=$PWD/scratch/tmp; mkdir -p $TMPDIR; export CERTLOG=$PWD/material/evidence/final_checks/CertCubo.log; cd material/tools && python3 acceptance.py ../paper/THE_DANCING_SAND_THEOREM_v9.md ../paper/THE_DANCING_SAND_THEOREM_v9.pdf'`
  and the same with `control` added at the end (`logs/acc_v9_control.log`). The author says 12 of 12 pass, and 12 of 12 fail in control mode.
- Find the differences from the list of version 8 with `diff`, and judge them: the three new checks (10, 11, 12) and their controls; the declared short page of check 5 (is page 45 really a table row that does not split, and is the exception narrow?).
- The builder: `md2html_v9.py` differs from `md2html_v8.py` by one rule (68). Judge it, and check the author's claim that version 8's md built with `md2html_v9.py` gives a byte-identical html (`PYTHONDONTWRITEBYTECODE=1 python3 md2html_v8.py IN OUT 'The Dancing Sand Theorem'`; run from `material/builder/`, writing OUT into `scratch/`; the variable keeps Python from writing a `__pycache__` folder into `material/`).

## 3. What you do not do
Do not re-read the unchanged parts of the paper or of the certificate. Do not re-prove the theorems. Do not compile Lean. Do not judge the typography beyond «is anything broken». Do not propose new sentences except as replacements for sentences you find false.

## 4. After everything else
Open `material/read_after/` only when §2 is written. Does the author's account in `CORRECTIONS_v8_to_v9.md` agree with what you found? Does `text_edits.py` do only what the diff shows? Does the author's grading of the first cold reading agree with what you found in (c)?

## 5. Sections of REPORT_COLD_11.md (create them empty first)
0. **First lines:**
   - Did anything mathematical change from version 8 to version 9? NO / YES (where).
   - Is every new sentence of version 9 true? YES / NO.
   - Are the corrections of the certificate right, and is Table 6a right? YES / NO.
   - Is anything broken on the pages? NO / YES.
   - Does the acceptance list pass, do its controls fail, and is the builder's new rule harmless? YES / NO.
   - **The list of replacements:** for each error, the document (paper v9 or certificate), the place, the exact text to remove and the exact text to print. Write «none» if there are none.
1. (a) The hunks of the paper's diff
2. (b) The new sentences of version 9, one by one
3. (c) The corrections of the certificate, and Table 6a
4. (d) The pages (the list is in `checks/PAGES.md`)
5. (e) The acceptance list, its controls, and the builder
6. After everything else (§4)
7. Style doubts (not counted)
8. Sealed predictions, hits and failures
9. My errors
10. What I did not check
11. Files with md5

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_11.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the first lines of §0.
