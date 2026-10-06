# COLD READING 6 — the changes of version 4 of «The Dancing Sand Theorem», and its pdf

Written by Grepy Muchas Pilas, chief auditor of the hypercube project, on 5 October 2026.

**You are «Grepy el lector frío del cubo 6».** You never saw this work being built. That is why your reading is worth something. Read it as a referee and a typesetter of a top journal would, and try to break it.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order):
1. Before you read anything, create `REPORT_COLD_6.md` with the section headings of §6, empty.
2. Put every verdict into `REPORT_COLD_6.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_6.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_4_CHANGES/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder. Everything you need is here.
- Never use `rm` (move to `scratch/_BORRAR/`). Never read a Desktop screenshot.
- `material/` is read-only. `material/read_after/` is read only when §5 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate (memory, time) in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Use integers and exact fractions only, or exact modular arithmetic.
- In zsh, never start a word with `=`. Quote heredocs: `<<'EOF'`.

**How you grade, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, the writing or the typesetting is not.

**Honesty rules.**
- «I did not read it» is an honest verdict: write it as such. Do not stamp «HOLDS» on what you only skimmed.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds. Publish your failures in the same size of type as your hits.
- A check whose control cannot fail is not a check.
- **Stop rule:** if you find a counterexample to a numbered statement, stop that item, write it down with the exact input, and tell Rafa in capitals.
- Chat with Rafa in Spanish; write documents in English.

## 1. What you are reading

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v4.md`, `.pdf` (49 pages, A4) and `.html`: the text you grade;
- `THE_DANCING_SAND_THEOREM_v3.md` and `.pdf`: the previous version, only to see what changed;
- `DIFF_v3_to_v4.txt`: the line diff (`diff -u`, 381 lines);
- `CORRECTIONS_v3_to_v4.md`: the author's list of the changes. It cites files you are not given; that is deliberate.

**`material/sources/`:** the cited papers that are freely available (PDF and a text extraction of each).

**`material/tools/`:** seven page checks written by an earlier reader, copied unchanged: `gaps_text_words.py`, `structure.py`, `widows.py`, `formula_lines.py`, `margins.py`, `md_vs_pdf.py`, `xrefs.py`. Most read the html that `pdftotext -bbox` writes. Read each script before you trust it.

**You are NOT given** the constructors' reports, the audits, or the earlier cold readings (except what §5 opens at the end). **The paper must stand on its own.**

**What version 4 says about itself** (§1.0, §13, Appendix A):
- the changes of version 3 were read cold, and they hold;
- that reading found points of presentation and defects of typesetting;
- version 4 corrects them and sets the mathematics anew: letters italic; digits, brackets, operators and operator names upright; scripts stacked; displays in display style; no statement, display, table row or short proof broken across a page;
- no mathematical statement changed, and no number, except the ranges of §12 that the fifth reader checked against the code;
- **its changes have not yet been read cold. You are that reading.**

## 2. The changes of the text (35 % of your effort)

Grade each item in your own words, with the exact line of any doubt.

1. **No mathematical statement changed.** For every hunk of `DIFF_v3_to_v4.txt`, decide whether it touches a numbered statement (theorem, lemma, proposition, corollary, definition) or a proof step. Any change of a symbol, a number, a quantifier or a hypothesis inside one is to be reported, with the hunk.
2. **The presentation edits must not change content.** Many sentences became displays, and some displays were split by hand into two lines. Write a small normalizing comparison yourself, and say how it works. For each such hunk, check that the mathematics is the same, up to line breaks, spaces and the backticks of the md. One hunk adds three words to Corollary 1.6, item 1 («every dancer is»): judge it.
3. **The new sentences about strictness** after Lemma 7.9. They say where strictness of (Cut) is used as written, where a cut suffices with Lemma 7.9, and that it is indispensable only in Proposition 9.6 (H), twice. Check each claim against the proofs of Theorems 7.8 and 7.10, Lemma 7.9 and Proposition 9.6.
4. **The new sentences in the proof of Lemma 10.6(a)**, that the twist move and the split move are clean. Do they follow from Propositions 4.1 and 4.2 as cited?
5. **«Why dance» (§1.7)**, the sentence on the payments: is it exact for every move?
6. **§1.2, the citation of «the rounding never acts»**, and §1.4 item 1, the change of variables «up to the sign `(−1)^{|S|}`» in the proof of [GMMY24, Proposition 2.5]. Check the second against `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.*`.
7. **The reading record:** §1.0, §13 and Appendix A. Is every sentence exact about what was read cold and what was not?
8. **§12.1 and §12.2, the changed rows:**
   - the ranges of Propositions 5.2–5.4 and of Theorem 7.8 (`λ ≤ 126`);
   - the row of Lemma 7.9 with its 7 634 cells;
   - the two rows of the fifth reader, with all their numbers.
   Is each row stated no more strongly than a check of that kind can show? Is each control described as it is? The numbers of the fifth reader's rows are checked against its log in §5.
9. **The references:** the renamed keys ([MGM19], [DEGJPP23]), their order, and every citation of them in the text.

## 3. The pdf: only perfection is accepted (50 % of your effort)

Rafa's words: «Solo aceptamos la perfección». The standard: a referee and a typesetter of a top journal would find nothing to correct. Report every defect as PRESENTATION, with page and line, and with the fix you propose.

1. **Every page, looked at, in order.** Render with `pdftoppm -r 90 -png`, and with `-r 200` for any doubtful region. Look at all 49 pages one by one. Write one line per page in `checks/PAGES.md`: «p. N — OK» or the defect. No page may be skipped; a page you did not look at is written as such.
2. **The setting of the mathematics: the heart of this version.** Judge it against TeX's math style:
   - letters italic; digits, brackets, operators and operator names (`max`, `coker`, `Syl`, `dim`, `mod`, …) upright;
   - scripts stacked when both are present, and at the right height and size;
   - the spaces around relations, binary operators and punctuation;
   - displays in display style (limits under `Σ`, `∏`, `⊕`);
   - multi-line displays (first line left, continuation right);
   - double-struck and calligraphic letters (`𝟙`, `𝒦`, `𝒮`, `𝔡`, `ℎ`);
   - the end-of-proof mark.
   Look in particular at §4.4 (Theorem 4.4), §7.4 (Theorem 7.8), §10.3–§10.7, the tables of §1.0, §1.6, §1.7, §12, and the reference list. Report every formula that a TeX user would see as wrong.
3. **Line breaking inside formulas.** No break inside a short bracket group; no line that starts with a relation or a binary operator; no exponent or index separated from its base; no relation with three characters or fewer after it alone at the end of a line.
4. **Margins.** With `pdftotext -bbox`, find any word that runs past the right text margin. Measure the margin yourself from the body text; report the largest `xMax` found.
5. **Loose lines.** Use `material/tools/gaps_text_words.py` (read it first). Judge whether any loose line is visible to the eye.
6. **Structure:**
   - no heading alone at the foot of a page;
   - no numbered statement split across pages;
   - no table row split, cut or overflowing;
   - no single line of a paragraph alone at the top or the foot of a page;
   - two consecutive displays not separated by a page break.
   The author accepted two short pages: p. 7 (84 % full; §1.7 and its table start on p. 8) and p. 42 (75 % full, the end of §11 before §12). Judge them as a typesetter.
7. **Glyphs and fonts.** Run `pdffonts`. Is every font embedded? Look for missing-glyph boxes or wrong fallbacks. The fonts are Type 3 (Chrome embeds the STIX Two fonts that way): say whether that matters, and to whom.
8. **md and pdf say the same.** Compare `pdftotext` of the pdf with the md: every number of the tables of §1 and §12, and every theorem statement. Report any difference.
9. **Cross-references and citations.** Every «Lemma x.y», «Theorem x.y», «§x.y», «Corollary» and «Remark (n)» must point to an item that exists and says what is claimed. Every citation key must be in the reference list, and every reference must be cited.
10. **File names and code** are never hyphenated or broken. **The references** are set consistently. **The metadata:** title, author, subject, page count.

## 4. What you do not need to do

- Do not re-grade the statements that did not change, except where a changed sentence depends on them.
- Do not recompute the Main Theorem against the graphs. Earlier readings did that.

## 5. After everything else

Only when §2 and §3 are written, open `material/read_after/`:
- `cold_reading_5/REPORT_COLD_5.md` (§4 there lists 8 global and 28 specific defects of the pdf of version 3), `PAGES.md`, `gate_cold5.py` and `gate_cold5_full.log`:
  - is every defect of that reading fixed in version 4? Make a table: defect, fixed or not, page;
  - do the numbers of the two rows of §12.2 attributed to the fifth reader appear in that log, exactly?
- `builder/`: `build_v4.sh`, `md2html_v4.py` (read the rules (27)–(42) in its header), `phtml.py` (the setting of the mathematics), `pmath.py`, `chrome_pdf.sh`, `pdf_meta.py`. For each pdf defect you found, say which rule should have prevented it, or which rule is missing.
- `author_checks/`: the author's page checks. Do they measure what `CORRECTIONS_v3_to_v4.md` §6 says they measure?
- `gates_of_the_paper/`: you may run any of them under the watchdog, if a changed row of §12 makes you doubt it.

## 6. Sections of REPORT_COLD_6.md (create them empty first)

0. **First lines:**
   - Do the changes of the text hold as written: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is the pdf perfect: YES / NO (number of defects found).
   - Is version 4 ready for publication: YES / AFTER CORRECTIONS / NO.
1. The changes of the text (§2, item by item)
2. The presentation edits: content unchanged? (§2 items 1–2, with your comparison)
3. The pdf, page by page (summary; the full list is `checks/PAGES.md`)
4. The setting of the mathematics (§3 items 2–3)
5. The pdf, the other checks (§3 items 4–10)
6. After everything else (§5): the defects of reading 5, the builder, the author's checks
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

## 7. Order and budget

1. **Part 1 (5 %):** §1.0, §13 and Appendix A of version 4, and a first pass over the diff.
2. **Part 2 (30 %):** §2.
3. **Part 3 (50 %):** §3, the pdf.
4. **Part 4 (10 %):** §5.
5. **Part 5 (5 %):** the final writing, with the md5 of every file you wrote.

If an item gives you ten minutes without traction, write what you have, mark it, and go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_6.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the three first lines of §0.
