# COLD READING 8 — «The Dancing Sand Theorem», version 6, the version meant to be final

Written by Grepy Muchas Pilas, chief auditor of the hypercube project, on 6 October 2026.

**You are «Grepy el lector frío del cubo 8».** You never saw this work being built, and that is why your reading is worth something. This is meant to be the last version before publication. Your question is one: **is it correct?**

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_8.md` with the section headings of §6, empty.
2. Put every verdict into `REPORT_COLD_8.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_8.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_6_FINAL/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder. Everything you need is here.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only. Open `material/read_after/` only when §5 says so.
- **Do not run** `material/read_after/builder/build_v6.sh` or `text_edits.py`: they point outside this folder. Read them only.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate of memory and time in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time.
- In zsh, never start a word with `=` (write `echo '-----'`, not `echo =====`). Quote heredocs: `<<'EOF'`.

**How you grade, item by item:**
- **HOLDS** — you re-derived or re-checked it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or a statement, a number or a sentence is false;
- **PRESENTATION** — the mathematics is fine, but something in the writing or on the page is wrong.

**Honesty rules.**
- «I did not read it» is an honest verdict. Write it as such. Do not stamp «HOLDS» on what you only skimmed.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds. Publish your failures in the same size of type as your hits.
- A check whose control cannot fail is not a check.
- **Stop rule:** if you find a counterexample to a numbered statement, stop that item. Write it down with the exact input, and tell Rafa in capitals.
- Chat with Rafa in Spanish; write documents in English.

## 1. The standard: CORRECT, not perfect

Rafa's words for this version: «Haz lo que deje el pdf CORRECTO, renunciamos a la perfección. Si hay dos líneas más separadas de lo normal no importa. Que quede CORRECTO.»

So:
- **A defect is something wrong:** a false statement, sentence or number; a step that does not follow; the md and the pdf saying different things; a lost or wrong number, label or reference; a word or symbol missing or cut; a formula that cannot be read or reads as something else; a page that looks broken; a font or glyph missing.
- **Not a defect:** a loose line; a page short before a new section; a break that TeX would also allow; a choice of style you would make differently. Do not list these. If you are unsure whether something is «wrong» or «taste», write it once, in a short separate list «doubtful, my taste», and do not count it.
- A missing comma is accepted.

## 2. What you are reading

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v6.md`, `.pdf` (52 pages, A4) and `.html` — the text you grade;
- `THE_DANCING_SAND_THEOREM_v5.md` and `.pdf` — the previous version, only to see what changed;
- `DIFF_v5_to_v6.txt` — the line diff (`diff -u`, 143 lines);
- `CORRECTIONS_v5_to_v6.md` — the author's list of the changes. It cites files you are not given. Some of them you get in §5.

**`material/sources/`:** the cited papers that are freely available, each as a PDF and a text extraction.

**`material/tools/`:** the author's fixed acceptance list for this version, `acceptance.py`, and the scripts it calls (`fill.py`, `loose.py`, `xrefs.py`, `md_vs_pdf.py`, `margins.py`, `glyphs.py`). `fill.py` and `loose.py` were written by the previous cold reader. Read each script before you trust it.

**You are NOT given** the constructors' reports, the audits, or the earlier cold readings, except what §5 opens at the end. **The paper must stand on its own.**

**What version 6 says about itself** (§1.0, §13, Appendix A): the changes of version 5 were read cold; that reading found one false sentence in the record and defects of the page; version 6 corrects them; no mathematical statement and no number changed; the changes of version 6 have not yet been read cold. **You are that reading, and more: you read the whole pdf.**

## 3. The work

### 3.1 The changes of version 6 (20 % of your effort)
1. For every hunk of `DIFF_v5_to_v6.txt`, decide whether it touches a numbered statement or a proof step, and whether it changes content. Report any change of a symbol, a number, a quantifier or a hypothesis.
2. Each item of `CORRECTIONS_v5_to_v6.md` §1 and §2: is it done, in the md AND in the pdf, and is the new wording exact? In particular:
   - the sentence of §13 on what changed in versions 2 to 6 (check it against Appendix A and against the text of Theorem 7.8 and Lemma 7.2(b));
   - «the house `H'` of Lemma 7.7» and `fit(x_{H'})` in Proposition 9.6 (H) and around it;
   - the «Why dance» sentence (§1.7), against Propositions 4.1 and 4.2 for every move;
   - the cells of §12 (7 634, 10 455; «none for Propositions 5.3 and 5.4, Lemma 7.5 and (H)»): consistent with each other and with the ranges stated? No row may say more than a check of its kind can show.
3. The record sentences (§1.0, §13, Appendix A): is every sentence about what was read cold, and when, exact? Is anything said to be left undone, or half done? (Nothing should be.)

### 3.2 The whole pdf, read for correctness (55 % of your effort)
1. **Every page, looked at, in order.** Render with `pdftoppm -r 90 -png`, and `-r 200` for any doubtful region. Write one line per page in `checks/PAGES.md`: «p. N — OK» or the defect. No page skipped; a page you did not look at is written down as such.
2. **Read the text as a reader.** Not re-proving every theorem (earlier readings did), but reading every statement, every definition and every proof step, and stopping at anything that is false, does not follow, uses an object not yet defined, or reads wrongly. Give page and line.
3. **md and pdf say the same.** Every theorem statement, every number of the tables of §1 and §12, every list number (in particular the numbered steps of the proof of Theorem 7.8), every proof step, every bold label. Report any difference that is not purely typographic.
4. **Cross-references and citations.** Every «Lemma x.y», «Theorem x.y», «§x.y», «Corollary», «Remark (n)» points to an item that exists and says what is claimed. Every citation key is in the reference list; every reference is cited; the references are exact against `material/sources/` where you have the source.
5. **Things that look broken:** a formula split so that it reads wrongly; a symbol missing or replaced by a box; a script detached from its base; a table cut or overflowing; a word past the margin; a heading alone at the foot of a page; a statement whose label is separated from its text.
6. **Fonts and metadata:** `pdffonts` (all embedded), no missing glyph; title, author and page count in the metadata.

### 3.3 The acceptance list (15 % of your effort)
1. Read `material/tools/acceptance.py` and the scripts it calls.
2. Run it on version 6: `zsh vigia.sh logs/acc_v6.log 'export TMPDIR=$PWD/scratch/tmp; mkdir -p $TMPDIR; cd material/tools && python3 acceptance.py ../paper/THE_DANCING_SAND_THEOREM_v6.md ../paper/THE_DANCING_SAND_THEOREM_v6.pdf'` (estimate: under 300 MB, under 2 minutes). `acceptance.py` writes temporary files through Python's `tempfile`; the `TMPDIR` above keeps them in `scratch/`. If anything stops it, copy the tools to `scratch/tools/` and run from there.
3. Run its controls: `control` mode on version 6 (every check but 9 must FAIL), and the plain mode on version 5 (the author's run fails checks 1, 4 and 8 there; check 5 passes, because its pages under 85 % come before a new section — judge that).
4. Judge each check: does it measure what its name says? Can its control fail? Is any threshold or exception (the `NOT_TEXT` set of check 6, the «page before a new section» of check 5, the statement-label exception of check 4) hiding a real defect? Look at each exception on the page yourself.

### 3.4 The mathematics of the record (10 % of your effort)
The sentences of §1.0, §13 and Appendix A that say what each version changed and what each reading found: check each one against the text of version 6 itself (what Lemma 7.2(b) and Theorem 7.8 say now) and against the diff. A record sentence that is false is an ERROR.

## 4. What you do not need to do
- Do not re-prove the unchanged theorems, except where a doubt from your reading of the text needs it.
- Do not recompute the Main Theorem against the graphs.
- Do not grade typographic taste (see §1).

## 5. After everything else
Open `material/read_after/` only when §3 is written.
- **`cold_reading_7/`**: the report of the previous reading (`REPORT_COLD_7.md`, its `checks/`, its `scratch/` scripts) and its grading by the auditor. Make a table: each defect it found that made the pdf incorrect (its list PD1–PD28 and R1–R3, P2.x) — fixed in version 6 / not fixed / not a defect by the standard of §1 — with the page.
- **`builder/`**: `build_v6.sh`, `md2html_v6.py`, `phtml.py`, `pmath.py`, `chrome_pdf.sh`, `pdf_meta.py`, and the two edit scripts. For each defect you found, which rule caused it, or which is missing. Read only; do not run `build_v6.sh` or `text_edits.py`.
- **`ESTRATEGIA_PDF_A_LA_PRIMERA_v1.md`**: why the standard is «correct». Did version 6 do what its §4 and §6 say?
- **`gates_of_the_paper/`**: you may run any of them under the watchdog if a row of §12 makes you doubt it.

## 6. Sections of REPORT_COLD_8.md (create them empty first)
0. **First lines:**
   - Do the changes of version 6 hold as written? HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is the pdf correct? YES / NO, with the number of defects found (by the standard of §1).
   - Is version 6 ready for publication? YES / AFTER CORRECTIONS / NO. If AFTER CORRECTIONS: the exact list, each with page, line and the fix.
1. The changes of version 6 (§3.1, item by item)
2. The whole pdf, read for correctness (§3.2; the page list is in `checks/PAGES.md`)
3. md against pdf, cross-references, citations (§3.2 items 3–4)
4. The acceptance list and its controls (§3.3)
5. The mathematics of the record (§3.4)
6. After everything else (§5)
7. Doubtful, my taste (not counted)
8. Sealed predictions, hits and failures
9. My errors
10. What I did not read
11. Files with md5

## 7. Order and budget
1. **Part 1 (5 %):** §1.0, §13 and Appendix A of version 6, and a first pass over the diff.
2. **Part 2 (20 %):** §3.1.
3. **Part 3 (55 %):** §3.2, the whole pdf.
4. **Part 4 (15 %):** §3.3 and §3.4.
5. **Part 5 (5 %):** §5 and the final writing, with the md5 of every file you wrote.

If an item gives you ten minutes without traction, write down what you have, mark the item, and go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_8.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the three first lines of §0.
