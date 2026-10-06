# COLD READING 7 — the changes of version 5 of «The Dancing Sand Theorem», and its pdf

Written by Grepy Muchas Pilas, chief auditor of the hypercube project, on 5 October 2026.

**You are «Grepy el lector frío del cubo 7».** You never saw this work being built, and that is why your reading is worth something. Read the paper as a referee and a typesetter of a top journal would, and try to break it.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END.** This is Rafa's permanent order.
1. Before you read anything, create `REPORT_COLD_7.md` with the section headings of §6, empty.
2. Put every verdict into `REPORT_COLD_7.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md`, your re-entry note, up to date with one STATE line after each part. If your window is compacted, re-read `CLAUDE.md`, `MISSION.md`, `ESTADO.md` and `REPORT_COLD_7.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside this folder (`~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_5_CHANGES/`). Scratch files go in `scratch/`, never in `/tmp`.
- **Never open** `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder. Everything you need is here.
- Never use `rm`; move a file to `scratch/_BORRAR/` instead. Never read a Desktop screenshot.
- `material/` is read-only. Open `material/read_after/` only when §5 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate of memory and time in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time.
- In zsh, never start a word with `=` (write `echo '-----'`, not `echo =====`). Quote heredocs: `<<'EOF'`.

**How you grade, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, but the writing or the typesetting is not.

**Honesty rules.**
- «I did not read it» is an honest verdict. Write it as such. Do not stamp «HOLDS» on what you only skimmed.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds. Publish your failures in the same size of type as your hits.
- A check whose control cannot fail is not a check.
- **Stop rule:** if you find a counterexample to a numbered statement, stop that item. Write it down with the exact input, and tell Rafa in capitals.
- Chat with Rafa in Spanish; write documents in English.

## 1. What you are reading

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v5.md`, `.pdf` (51 pages, A4) and `.html` — the text you grade;
- `THE_DANCING_SAND_THEOREM_v4.md` and `.pdf` — the previous version, only to see what changed;
- `DIFF_v4_to_v5.txt` — the line diff (`diff -u`, 883 lines, 50 hunks);
- `CORRECTIONS_v4_to_v5.md` — the author's list of the changes, with measures. It cites files you are not given. That is deliberate. Some of them you get in §5.

**`material/sources/`:** the cited papers that are freely available, each as a PDF and a text extraction.

**`material/tools/`:** seven page checks written by an earlier reader, copied unchanged: `gaps_text_words.py`, `structure.py`, `widows.py`, `formula_lines.py`, `margins.py`, `md_vs_pdf.py`, `xrefs.py`. Most of them read the html that `pdftotext -bbox` writes. Read each script before you trust it.

**You are NOT given** the constructors' reports, the audits, or the earlier cold readings, except what §5 opens at the end. **The paper must stand on its own.**

**What version 5 says about itself** (§1.0, §13, Appendix A):
- The changes of version 4 were read cold, and they hold.
- That reading found one false number and one false sentence in the record of the readings, inexact sentences, and defects of typesetting.
- Version 5 corrects them, «except as stated in Appendix A». It also sets the page anew:
  - accents centred;
  - the number sets in double-struck letters;
  - matrices as matrices;
  - limits under max and min;
  - enlarged brackets;
  - page numbers;
  - the end-of-proof mark at the right margin;
  - tables with horizontal rules only;
  - no sentence of the running text beginning with a formula;
  - no break inside a short formula, a bracket group, a pure tensor or a citation;
  - fourteen passages reworded to remove loose lines.
- No mathematical statement changed, and no number changed, except the description of the 7 634 cells.
- **Its changes have not yet been read cold. You are that reading.**

## 2. The changes of the text (30 % of your effort)

Grade each item in your own words, and give the exact line of any doubt.

1. **No mathematical statement changed.** For every hunk of `DIFF_v4_to_v5.txt`, decide whether it touches a numbered statement (theorem, lemma, proposition, corollary, definition) or a proof step. Report, with the hunk, any change of a symbol, a number, a quantifier or a hypothesis inside one.
2. **The rewordings must not change content.**
   - Twenty-five sentences were reworded so that none begins with a formula.
   - Fourteen passages were reworded to remove loose lines.
   - Write a small normalizing comparison yourself, and say how it works. Check that each reworded sentence says the same mathematics as before. Pay attention to small words that carry meaning: «the word `w`», «where» against «and», «so that», «Moreover», «Finally».
3. **The number sets.**
   - Z became ℤ, Q became ℚ and F_2 became 𝔽_2 where they denote sets.
   - They were kept as letters where they are variables, matrices or sets of the proof: `Z_1`, `Z_2` (Lemma 7.3, Theorem 7.8), the matrix `Z` (§10.7), the sets `F_1`, `F_2` (step 7 of Theorem 7.8), the block `Q` (§10.4), and the cubes `Q_n`.
   - Find every place where the choice is wrong, either way.
4. **The new sentences.** For each, decide whether it is exact:
   - Proposition 9.6 (H), in the base cell: «which keeps the level sets of the child because `d_1` changes only at strict cuts (Lemma 7.2(b))». Check it against the proof of Theorem 7.8 (step 1) and Lemma 7.2(b).
   - «Why dance» (§1.7): each move «replaces the payments of two adjacent floors by minus half their product». Check it against Propositions 4.1 and 4.2 for every move.
   - §1.8 and §2.1: the basis is that of Gao et al. «up to the sign `(−1)^{|S|}`». Check it against `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.*`, the proof of their Proposition 2.5.
   - Remark (2) of §10.5: «(proof of Lemma 10.6(a), …)».
   - The 2019 poster is by «three of them», [MGM19].
5. **The reading record: §1.0, §13 and Appendix A.** Is every sentence exact about what was read cold and what was not? Is the list of what was «left as it is» in the version 5 bullet complete, as far as your own look at the pdf shows (§3)?
6. **§12.1 and §12.2, the changed rows.**
   - the meaning of «none» and «fires»;
   - the row of Propositions 5.2–5.4, which now names matrix entries, clocks and clocks;
   - the reworded row of the fourth reader («the 7 634 cells … other than the 240 with `i = 0` and `I ≠ ∅` (the 7 620 with `i ≥ 1`, and the 14 with `i = 0` and `I = ∅`, where `M = 0`)»);
   - the new row of the sixth reader.

   You cannot check the readers' logs. Check that the numbers are consistent with each other and with the ranges stated. Check that no row says more than a check of its kind can show.
7. **The references.** arXiv numbers were added to [DJ14], [RT14] and [LZ22]. Check them against `material/sources/`. Check that the list is consistent in form.

## 3. The pdf: only perfection is accepted (55 % of your effort)

Rafa's words: «Solo aceptamos la perfección». The standard is a referee and a typesetter of a top journal who find nothing to correct. Report every defect as PRESENTATION, with page and line, and with the fix you propose.

1. **Every page, looked at, in order.**
   - Render with `pdftoppm -r 90 -png`, and with `-r 200` for any doubtful region.
   - Look at all 51 pages one by one.
   - Write one line per page in `checks/PAGES.md`: «p. N — OK» or the defect.
   - No page may be skipped. A page you did not look at is written down as such.
2. **The setting of the mathematics.** Judge it against TeX's math style:
   - letters italic; digits, brackets, operators and operator names upright;
   - accents (bars, hats, tildes) centred over their letters, and readable at reading size;
   - scripts stacked and at the right height;
   - the spaces around relations, binary operators and punctuation;
   - displays in display style, with limits under `Σ`, `∏`, `⊕`, `max`, `min` and `mean`;
   - matrices, stacked fractions and enlarged brackets;
   - multi-line and aligned displays;
   - double-struck, calligraphic and Fraktur letters;
   - the end-of-proof mark: right margin, on the last line, never alone.

   Look in particular at:
   - §4.4 (Theorem 4.4);
   - §7.3–§7.4;
   - §10.3–§10.7;
   - the tables of §1.0, §1.6, §1.7 and §12;
   - the reference list.
3. **Line breaking.**
   - No break inside a short formula or a short bracket group.
   - No line that starts with a relation or a binary operator.
   - No exponent or index separated from its base.
   - No pure tensor split at «⊗».
   - No citation broken inside.
   - No hyphenation that leaves fewer than three letters on either side or breaks a hyphenated compound.
4. **Margins.** With `pdftotext -bbox`, find any word that runs past the right text margin, and report the largest `xMax`.
5. **Loose lines.** Use `material/tools/gaps_text_words.py`, and read it first. The author says that two lines reach twice the median word space, and that both carry a small matrix in the text (p. 33 and p. 35). Judge this, and judge whether any loose line is visible to the eye.
6. **Structure.**
   - No heading alone at the foot of a page.
   - No numbered statement split across pages.
   - No table row split, cut or overflowing.
   - No single line of a paragraph alone at the top or the foot of a page.
   - Two consecutive displays are not separated by a page break.

   The author accepted two pages under 90 % full: p. 1 (the title page with the abstract) and p. 5 (89 %). Judge them as a typesetter.
7. **Glyphs and fonts.**
   - Run `pdffonts`, and check that every font is embedded.
   - The author says that only STIX Two Text, STIX Two Math and Menlo are used: check it.
   - Look for missing-glyph boxes or fallbacks.
8. **md and pdf say the same.** Compare `pdftotext` of the pdf with the md: every number of the tables of §1 and §12, and every theorem statement. Report any difference that is not purely typographic.
9. **Cross-references and citations.**
   - Every «Lemma x.y», «Theorem x.y», «§x.y», «Corollary» and «Remark (n)» points to an item that exists and says what is claimed.
   - Every citation key is in the reference list, and every reference is cited.
10. **Code and metadata.**
    - File names and code are never broken.
    - The metadata: title, author, subject, page count.

## 4. What you do not need to do

- Do not re-grade the statements that did not change, except where a changed sentence depends on them.
- Do not recompute the Main Theorem against the graphs. Earlier readings did that.

## 5. After everything else

Open `material/read_after/` only when §2 and §3 are written.

- **`cold_reading_6/`**: the report of the previous reading, `REPORT_COLD_6.md`, with its lists `checks/PDF_DEFECTS.md` (GD1–GD32) and `checks/PAGES.md`, and its scripts in `scratch/`.
  - Is every defect of that reading fixed in version 5, or honestly listed as left? Make a table: defect, fixed / left and said / left and not said, page.
  - Run its scripts on version 5 (`lines2.py`, `stmt_cmp.py`, `pdfcheck.py`, `xref2.py`, `apos.py`, …) under the watchdog, and compare with the measures of `CORRECTIONS_v4_to_v5.md` §5.
- **`builder/`**: `build_v5.sh`, `md2html_v5.py` (rules (43)–(59) in its header), `phtml.py` (rules G9–G21), `pmath.py`, `chrome_pdf.sh`, `pdf_meta.py`. For each pdf defect you found, say which rule should have prevented it, or which rule is missing.
- **`author_checks/`**: the author's page checks. Do they measure what `CORRECTIONS_v4_to_v5.md` says they measure?
- **`gates_of_the_paper/`**: you may run any of them under the watchdog, if a changed row of §12 makes you doubt it.

## 6. Sections of REPORT_COLD_7.md (create them empty first)

0. **First lines:**
   - Do the changes of the text hold as written? HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is the pdf perfect? YES / NO, with the number of defects found.
   - Is version 5 ready for publication? YES / AFTER CORRECTIONS / NO.
1. The changes of the text (§2, item by item)
2. The rewordings: content unchanged? (§2 items 1–3, with your comparison)
3. The pdf, page by page (a summary; the full list is in `checks/PAGES.md`)
4. The setting of the mathematics and the line breaking (§3 items 2–3)
5. The pdf, the other checks (§3 items 4–10)
6. After everything else (§5): the defects of reading 6, the builder, the author's checks
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

## 7. Order and budget

1. **Part 1 (5 %):** §1.0, §13 and Appendix A of version 5, and a first pass over the diff.
2. **Part 2 (25 %):** §2.
3. **Part 3 (55 %):** §3, the pdf.
4. **Part 4 (10 %):** §5.
5. **Part 5 (5 %):** the final writing, with the md5 of every file you wrote.

If an item gives you ten minutes without traction, write down what you have, mark the item, and go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_7.md listo`, with the md5 of the report. Then tell Rafa, in Spanish, the three first lines of §0.
