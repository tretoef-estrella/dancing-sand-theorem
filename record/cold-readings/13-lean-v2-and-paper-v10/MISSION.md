# COLD READING 13 — the small cases in Lean (piece C53), version 2 of the Lean certificate, and the changes of version 10 of «The Dancing Sand Theorem»

Written by Grepy Escribano, chief auditor of the hypercube project, on 11 October 2026.

**You are «Grepy Remate».** You never saw this work being built.

**The paper.** «The Dancing Sand Theorem» determines the whole 2-part of the sandpile group of the hypercube. Version 9 is public.

**The Lean check.** Its whole proof was checked in Lean 4 with Mathlib in 68 pieces. A **Lean certificate** (version 1, public) describes that check, and two cold readers have read it.

**What is new.** Version 1 proved four results for fewer values of `n` than the paper states:
- the equivalent form of Theorem DW, its count `L1` and the `𝔽_2`-rank `R`, for `n ≥ 2` instead of `n ≥ 1`;
- Gao et al.'s Theorem 4.1, for `n ≥ 3` instead of `n ≥ 2`.

A 69th piece, **C53**, proves the missing cases and states the four results for every `n`. **Version 2 of the certificate** adds it. **Version 10 of the paper** updates its §12.3, the Appendix A line on formal verification and the reference [LC26]. Nothing else changes.

You read **three things, and only what changed:**
1. the Lean of piece C53 (four files), against the piece it was asked to prove;
2. the changes of the certificate from version 1 to version 2;
3. the changes of the paper from version 9 to version 10.

**This mission is CLOSED.** You answer the six questions (a) to (f) of §2, and nothing else. For every error you find you write the exact replacement text, word for word. Your replacements will be applied as you write them, and there will be no further reading after yours. So write them as you want them printed.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_13.md` with the section headings of §5, empty.
2. Put every verdict into it the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_13.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_LEAN_2_PAPER_10/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only. At the start and at the end, check it against `MANIFEST_md5.txt`; the compiled files under `material/project/.lake/` are not in the manifest.
- Open `material/read_after/` only when §4 says so.

**How you run.**
- Run every Python with `PYTHONDONTWRITEBYTECODE=1` set.
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument. The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate in `logs/DIARY.md` BEFORE each run. A log that does not end in `VIGIA-FIN-OK` is not a result.
- **Lean is allowed in this reading, with three limits:**
  1. Only `lake env lean FILE`, from `material/project/`. **Never `lake build`.**
  2. Only one Lean run at a time, with the Lean cap:
     `TOPE_KB=4718592 TOPE_S=900 zsh ../../vigia.sh ../../logs/NAME.log 'lake env lean FILE'`
  3. A Lean file of your own goes in `scratch/` and is given by its path, for example `lake env lean ../../scratch/MyCheck.lean`. It imports `RequestProject.SmallCases.All` (or other modules of the project).
  - The author ran `checks/CheckC53.lean` in this very clone: 189 s, peak 1.5 GB, exit 0.
- In zsh, never start a word with `=`; quote heredocs `<<'EOF'`.

**How you grade:**
- **HOLDS** — re-checked in your own words or with your own code.
- **ERROR** — a sentence, a number or a step is false. Give the replacement text.
- **PRESENTATION** — something on the page is wrong. Give the fix.
- «I did not check it» is an honest verdict.

Seal your predictions in `checks/SEALED.md` before you measure.

**Stop rule:** if a Lean statement of C53 says something other than the piece, or a number of a result of the paper changed from version 9 to version 10, stop that item, write it with the exact place, and tell Rafa in capitals.

Chat with Rafa in Spanish; write documents in English.

**The standard is CORRECT, not perfect.** Nothing about typography is asked of you beyond «is anything broken». List style doubts once, apart, and do not count them.

## 1. What you have

- **`material/c53/`** — the piece and what came back:
  - `C53_the_small_cases.md`: the piece;
  - `msgC53.txt`: the text actually pasted into Aristotle, the instruction followed by the piece;
  - `instrC53.txt`;
  - the brute force `chkC53.py` and its log `chkC53.log`;
  - Aristotle's returned project `aristotle_C53.tar.gz`, tarball (69);
  - the build script `buildC53.sh` and its logs `buildC53*.log`;
  - the log of the author's check file, `CheckC53.log`.
- **`material/project/`** — a clone of the compiled project as it is now: `RequestProject/` with the new folder `SmallCases/`, the check files `checks/`, the lake files, and Aristotle's `ARISTOTLE_SUMMARY.md` of the C53 run.
- **`material/final_checks/`:**
  - `CertCubo.log` and `CertCubo2.log`: every statement and definition as Lean prints it, versions 1 and 2;
  - `CheckCubo_postclean.log` and `CheckCubo2.log`;
  - `DepsCubo_postclean.log` and `DepsCubo2.log`;
  - the source manifests `MANIFEST_md5_416.txt` (version 1) and `MANIFEST_md5_420.txt` (version 2).
- **`material/certificate/`:**
  - the certificate, versions 1 and 2, each as `.md`, `.pdf` and source `.src.md`;
  - `DIFF_certificate_v1_to_v2.txt`;
  - the scripts that make version 2: `make_v2.py` (the anchored edits), `make_tables_v2.py` (Tables 6a and 6b) and `fill_v2.py` (cuts the Lean blocks out of `CertCubo2.log`);
  - their data, `data_v2/`;
  - `make_tables.py` of version 1, for comparison.
- **`material/paper/`:** versions 9 and 10 (`.md`, `.pdf`; also `.html` of 10) and `DIFF_v9_to_v10.txt`.
- **`material/tools/`:** the acceptance list of version 10 (`acceptance.py` and its scripts); `acceptance_v9_for_comparison.py`.
- **`material/builder/`:** `build_v10.sh`, `build_v9.sh`, `md2html_v9.py`, `phtml.py`, `pmath.py`. They use the author's paths: read them, do not run them.
- **`material/read_after/`:** the author's edit script for version 10 and the author's audit note of C53.

**Two placeholders that are not errors:**
1. Item 9 of §2 of the certificate reads `[[V2READ]]`. The author will fill it with an account of your reading after it, in the form of item 7. You may propose its text.
2. The DOIs `10.5281/zenodo.23298436` (certificate version 2) and `10.5281/zenodo.23298437` (paper version 10) are reserved on Zenodo and resolve only after publication. Do not count «does not resolve» against them.

## 2. The six questions

**(a) Is the Lean of C53 right, faithful and clean?**
- Extract the tarball into `scratch/`.
  - Is `RequestProject/` there identical, file by file, to `material/project/RequestProject/`?
  - Are the 416 files of version 1 identical to `MANIFEST_md5_416.txt`?
  - Is `SmallCases/` the only new folder?
- Read the four files of `SmallCases/`. For each of the fourteen statements of the piece, is the Lean statement the one of the piece?
  - Compare symbol by symbol: the range of `n`, the types, `Fin (BaiCounts.aN n)`, `twoM`, `l0`, `l1`, `cExp`, `gmax`, `v2`, the casts to `ℤ`.
  - The item «(L1-1)» is the Lean name `L1_one`. Is that the only renaming?
- Search the four files for `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`, `extern`, `set_option`, `partial`.
- Run `checks/CheckC53.lean`. Then write your own check file in `scratch/`, which restates the four `_all` statements and `T0` by hand (with `example`) and prints `#print axioms` for each.
- Are the proofs of the cases mathematically right, in your own words?
  - (S1): an elementary abelian 2-group `S` with `|S/2S| = 1` is trivial; Lean uses Bai's count at `n = 1`.
  - (S3): `lapBar A 1 = 0`.
  - (T0): `K(Q_2) ≅ ℤ/4` from the exponent multiset `{2}`.
  - (G1-2): both sides equal 2.
  - The `_all` forms: a case split on `n = 1`, resp. `n = 2`.
- Did the first 68 pieces' theorems really leave out exactly these cases? Read the hypotheses of `FoldLaw.DW'`, `FoldLaw.L1`, `FoldLaw.R` and `PodiumCor.G1` in `CertCubo.log`.

**(b) Did anything mathematical, or any number of a result, change from version 9 to version 10 of the paper?** Work on the diff.
- For every hunk: write what it removes and what it adds.
- Run `diff -u` yourself and compare with `DIFF_v9_to_v10.txt`.

**(c) Is every new sentence of version 10 true?** The changed text is: the header; three bullets of §12.3 «What Lean proves»; the paragraph «How»; the last sentence of «Read cold»; the bullet removed from «What Lean does not state»; «Where»; the entry «Formal verification» of Appendix A; the reference [LC26]. Take every clause. In particular:
- Each Lean name: does it exist in `CertCubo2.log`, and does its statement say what the sentence says?
- «420 Lean files (419 in its 69 folders, and the main file), 61 285 lines and 3 470 theorem and lemma declarations»: recount them yourself from `material/project/RequestProject/`. Say how you count. A declaration preceded by an attribute such as `@[simp]` is a declaration; a comment line is not.
- «the four modules of the 69th piece were then compiled from their sources, with the sources of the other 416 unchanged»: check against `buildC53*.log` and the two manifests.
- Is the removed bullet now really stated in Lean, and does nothing else of «What Lean does not state» become false?
- Is it now true that every result of the paper is proved in Lean for every `n` for which the paper states it? Check against the paper's own statements of Theorem DW, its equivalent form, §10.8, and Corollaries 1.4–1.6.

**(d) Are the changes of the certificate from version 1 to version 2 right?** Work on `DIFF_certificate_v1_to_v2.txt`. For every hunk, is the new text true? In particular:
- §0, §1.3, «Generality», §1.4, the new §1.5: against the Lean and the logs. Do the four Lean blocks of §1.5 match `CertCubo2.log` byte for byte? Do the first 21 lines of `CheckCubo2.log` equal `CheckCubo_postclean.log`?
- §3: the new row C53, and the sentence on the piece pasted as text. Is `msgC53.txt` really the piece file preceded by an instruction?
- §3.3: the four cones and the union of twenty (8 019 declarations, 344 modules). Are they in `DepsCubo2.log`? Are the lines of version 1 there unchanged? Is «the 76 outside it are the same 75 and `SmallCases.All`» right (420 − 344 = 76)?
- §4:
  - `decide` in 17 files;
  - 420 files with no forbidden construct;
  - the 14 axiom lines of C53;
  - Aristotle's register (541) — say what you can and cannot check.
- §6: the new rows of Tables 6a and 6b, against `chkC53.log`, `buildC53*.log`, the tarball's md5 and `data_v2/`. Do not run `make_tables_v2.py` in place; if you want to run it, copy the folder to `scratch/`.
- §7 totals: the 69 folders, «419 | 61 261 | 3 258 | 877», and 3 470.
- §8: the version-2 paragraph and the manifest's md5.
- Is any sentence of version 1 that the changes did not touch now false because of them?

**(e) The pages.**
- Paper: versions 9 and 10 both have 52 pages. Render both at 40 dpi and compare page by page. The author expects only pages 1 and 48–52 to differ (check it).
- Check by a word comparison of `pdftotext` (page numbers removed) that the text of the pdf differs only where the md does.
- Look at every page that differs at 90 dpi.
- Certificate: look at every page of the version 2 pdf that the diff touches, at 90 dpi.
- One line per page in `checks/PAGES.md`. Is anything broken?

**(f) The acceptance list.**
- Run the list on version 10 and in control mode. The estimate is under 200 MB and under 1 minute each:
  `zsh vigia.sh logs/acc_v10.log 'export TMPDIR=$PWD/scratch/tmp; mkdir -p $TMPDIR; export CERTLOG=$PWD/material/final_checks/CertCubo2.log; cd material/tools && python3 acceptance.py ../paper/THE_DANCING_SAND_THEOREM_v10.md ../paper/THE_DANCING_SAND_THEOREM_v10.pdf'`
  Then the same with `control` added at the end (`logs/acc_v10_control.log`).
  The author says 12 of 12 pass, and 12 of 12 fail in control mode.
- Judge the two changes from the list of version 9 (`diff`): check 11 reads `CertCubo2.log`, and check 12 looks for the new DOI.

## 3. What you do not do
- Do not re-read the unchanged parts of the paper or of the certificate. Do not re-prove the theorems of the first 68 pieces.
- Do not run `lake build`.
- Do not judge the typography beyond «is anything broken».
- Do not propose new sentences except as replacements for sentences you find false (and, if you wish, the text of item 9).

## 4. After everything else
Open `material/read_after/` only when §2 is written. Does the author's audit note of C53 agree with what you found? Does `text_edits.py` do only what the diff shows?

## 5. Sections of REPORT_COLD_13.md (create them empty first)
0. **First lines:**
   - Is the Lean of C53 right, faithful and clean? YES / NO.
   - Did anything mathematical change from version 9 to version 10? NO / YES (where).
   - Is every new sentence of version 10 true? YES / NO.
   - Are the changes of the certificate right? YES / NO.
   - Is anything broken on the pages? NO / YES.
   - Does the acceptance list pass, and do its controls fail? YES / NO.
   - **The list of replacements:** for each error, the document (paper v10 or certificate v2), the place, the exact text to remove and the exact text to print. Write «none» if there are none.
   - **Proposed text for item 9 of §2 of the certificate** (optional).
1. (a) The Lean of C53
2. (b) The hunks of the paper's diff
3. (c) The new sentences of version 10, one by one
4. (d) The changes of the certificate
5. (e) The pages (the list is in `checks/PAGES.md`)
6. (f) The acceptance list and its controls
7. After everything else (§4)
8. Style doubts (not counted)
9. Sealed predictions, hits and failures
10. My errors
11. What I did not check
12. Files with md5

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_13.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the first lines of §0.
