# COLD READING 5 — the changes of version 3 of «The Dancing Sand Theorem», and the perfection of its pdf

Written by Grepy Bross, the outgoing auditor of the hypercube project, on 5 October 2026.

**You are «Grepy Muchas Pilas».** You are the NEW chief auditor and only scribe of the hypercube project, and this cold reading is your first job. You never saw this work being built. That is why the reading is worth something: read it the way a referee for a top journal would, and try to break it. Only after your report is written do you learn the history of the project (stage 2 of `ARRANQUE_GREPY_MUCHAS_PILAS_v1.md`).

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in, «ultracode» included.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order):
1. Before you read anything, create `REPORT_COLD_5.md` with the section headings of §6, empty.
2. Every verdict goes into `REPORT_COLD_5.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `ESTADO.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `MISSION.md`, `ESTADO.md` and `REPORT_COLD_5.md`, and go on.
5. What is not on disk does not exist.

**Where you work during this reading (stage 1).**
- Write only inside `HYPERCUBE/reports/LECTOR_FRIO_5/`. Scratch files go in `scratch/` there, never in `/tmp`.
- **Until `REPORT_COLD_5.md` is finished, open NOTHING of `HYPERCUBE/` outside this folder**: no audits, no flights, no earlier readings, no notes, no `BITACORA.md`. The two `CLAUDE.md` files that the session loads by itself cannot be avoided; do not go looking for what they point to. Everything you need is in `material/`.
- Never use `rm` (move to `scratch/_BORRAR/`). Never read a Desktop screenshot.
- `material/` is read-only. `material/read_after/` is read only when §5 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate (memory, time) in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Integers and exact fractions only, or exact modular arithmetic.
- In zsh, never start a word with `=`. Quote heredocs: `<<'EOF'`.

**How you grade, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, the writing or the typesetting is not.

**Honesty rules.**
- «I did not read it» is an honest verdict: write it as such. Do not stamp «HOLDS» on what you only skimmed.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds, and publish your failures in the same size of type as your hits.
- A check whose control cannot fail is not a check.
- **Stop rule:** if you find a counterexample to a numbered statement, stop that item, write it down with the exact input, and tell Rafa in capitals.
- Chat with Rafa in Spanish; write documents in English.

## 1. What you are reading

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v3.md`, `.pdf` (47 pages, A4) and `.html`: the text you grade;
- `THE_DANCING_SAND_THEOREM_v2.md` and `.pdf`: the previous version, only to see what changed;
- `DIFF_v2_to_v3.txt`: the line diff (`diff -u`, 512 lines);
- `CORRECTIONS_v2_to_v3.md`: the author's list of the changes. It cites files you are not given; that is deliberate.

**`material/sources/`:** the cited papers that are freely available (PDF and a text extraction of each).

**`material/tools/`:** `gaps_text_words.py` and `gaps_all.py`, the author's measure of loose lines (they read the html that `pdftotext -bbox` writes; see §3).

**You are NOT given** the constructors' reports, the audits, or the earlier cold readings. **The paper must stand on its own.** If a changed step can only be understood with material the paper does not print or cite, that is a GAP of the paper.

**What version 3 says about itself** (§1.0, §13, Appendix A): the repair made in version 2 (a strict cut in Theorem 7.8) was read cold and holds; that reading also showed that every «house fit» is integral, so the rounding never acts; version 3 makes this Lemma 7.9 («integrality») and **its changes have not yet been read cold. You are that reading.**

## 2. The mathematics of the changes (45 % of your effort)

Grade each item in your own words, with the exact line of any doubt.

1. **Lemma 7.9, integrality — the heart.** Prove it yourself before you read the proof. Then read the proof: the induction on `|I|`, the real part of Lemma 7.2(b) at non-strict cuts, Lemma 7.3, the penalty shifts, and the deletion at a cut. Is every step right? Is the base case right?
2. **Every use of Lemma 7.9.** §8, Proposition 9.6 (H) and (K), Theorem 7.10. Does each use get exactly what it needs from integrality? The text says that strictness of (Cut) is now needed only in Proposition 9.6 (H): check that claim in both directions (is it needed there? is it really not needed anywhere else?).
3. **§1.2 «the rounding never acts in the cube»** and the vocabulary row «raw clocks; pooling». Do they follow from Lemma 7.9 as stated, and no more?
4. **§7.1, «a strict drop of the fit is a cut»,** and the proof of Lemma 7.2(b).
5. **Theorem 7.8, step 3:** case (c) «`T = 0`, `sat = 1`, `J' ≢ 0`» and case (d) with Lemma 7.7. Are the cases exhaustive now?
6. **Proposition 9.6 (H):** «`Z_1 ≤ 0`», and «the largest big clock is the integral mean `μ`».
7. **«Even» payment systems:** Remark (1) and Remark (2) of §10.5, and Lemma 10.6(a). Does the proof of 10.6(a) need the evenness exactly where it divides by 2? Is «even» needed anywhere else in §10 and missing?
8. **The reading record:** §1.0, §13 and Appendix A. Is every sentence exact about what was read cold and what was not?
9. **§1.7 and §1.8:** the four rewordings of §1.7, and the quotation of [Aky26] against `material/sources/TwoAdicAllOnesSquare_arXiv2609.10625.*` (whole, and with its own meaning).
10. **§12.1 and §12.2:** is every row stated no more strongly than a check of that kind can show? Are the controls described as they are?
11. **The presentation edits must not change content.** Many sentences became displays (formulas on their own lines). For every hunk of `DIFF_v2_to_v3.txt` that the author lists as presentation, check that the text is the same up to line breaks and spaces (write a small normalizing comparison yourself; say how). Any hunk that changes a symbol, a number or a word is to be reported.
12. **Your own gate, written from the text alone.** From the definitions of §7.3, compute the house fits for every house with `k ≤ 6` (or as far as the caps allow), and check integrality, and the claim of item 2 about strictness. Its control must be able to fail: for example, a sequence that is not a house, whose fit is not integral.

## 3. The pdf: only perfection is accepted (40 % of your effort)

Rafa's words: «Solo aceptamos la perfección». The standard: a referee and a typesetter of a top journal would find nothing to correct. Report every defect as PRESENTATION, with page and line, and with the fix you propose.

1. **Every page, looked at, in order.** Render with `pdftoppm -r 90 -png` (and `-r 200` for any doubtful region), look at all 47 pages one by one. Write one line per page in `checks/PAGES.md`: «p. N — OK» or the defect. No page may be skipped; a page you did not look at is written as such.
2. **Margins.** With `pdftotext -bbox`, find any word that runs past the right text margin. Measure the margin yourself from the body text (the author used `xMax > 542.5` on this A4 page); report the largest `xMax` found.
3. **Loose lines.** Run `material/tools/gaps_text_words.py` on the bbox file (read the script first). The author reports one justified line with a mean gap above 7 pt and none above 8 pt. Check it, and judge whether any loose line is visible to the eye.
4. **Formulas.** No formula broken inside a sub-expression; no exponent or index separated from its base; no line that starts with a binary operator; no relation or «`= 0`» alone on a line; long formulas set as displays; no end-of-proof mark alone on a line.
5. **Structure.** No heading alone at the foot of a page; no box (theorem, lemma) split across pages; no table row split; no table cut or overflowing; no single line of a paragraph alone at the top or the foot of a page if it can be avoided.
6. **The two blanks the author accepted:** p. 7 ends about a quarter blank, and p. 41 ends about a sixth blank. Judge them as a typesetter: acceptable, or to be fixed? If to be fixed, say how.
7. **Glyphs and fonts.** `pdffonts`: is every font embedded? Look for missing-glyph boxes (`□`) or wrong fallbacks, especially in `𝒦`, `𝒮`, `Ξ`, `η`, `ŷ`, the subscripts and superscripts, and the arrows.
8. **md and pdf say the same.** Compare `pdftotext` of the pdf with the md: every number of the tables of §1 and §12, every theorem statement. Report any difference.
9. **Cross-references and citations.** Every «Lemma x.y», «Theorem x.y», «§x.y», «Corollary», «Remark (n)» points to an item that exists and says what is claimed. Every citation key in the text is in the reference list, and every reference is cited. Every DOI and arXiv number is well formed (you may check them on the web; write each query in `checks/QUERIES.md`).
10. **File names and code** are never hyphenated or broken.
11. **The references** are set consistently (authors, title, journal, volume, year, pages).
12. **The metadata:** the pdf title and the page count.

## 4. What you do not need to do

- Do not re-grade the statements that did not change, except where a changed item depends on them.
- Do not recompute the Main Theorem against the graphs. Earlier readings did that.

## 5. After everything else

Only when §2 and §3 are written, open `material/read_after/`:
- `gates_of_the_paper/`: the author's gates cited in §12.1. Say whether `gate_strict_cut.py` and `gate_sections5to7.py` check what §12.1 says they check, whether their controls can fail, and where your numbers and theirs differ. You may run them under the watchdog.
- `md2html.py` and `build_v3.sh`: the builder. Read its header (rules (1)–(26)). For each pdf defect you found, say which rule should have prevented it, or which rule is missing.

## 6. Sections of REPORT_COLD_5.md (create them empty first)

0. **First lines:**
   - Do the changes hold as written: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is the pdf perfect: YES / NO (number of defects found).
   - Is version 3 ready for publication: YES / AFTER CORRECTIONS / NO.
1. The mathematics of the changes (§2, item by item)
2. My own gate (with controls)
3. The presentation edits: content unchanged? (§2 item 11)
4. The pdf, page by page (summary; the full list is `checks/PAGES.md`)
5. The pdf, the other checks (§3 items 2–12)
6. The author's gates and builder (§5)
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

## 7. Order and budget

1. **Part 1 (5 %):** §1.0, §13 and Appendix A of version 3, and a first pass over the diff.
2. **Part 2 (40 %):** §2 — the mathematics, and your own gate.
3. **Part 3 (40 %):** §3 — the pdf.
4. **Part 4 (10 %):** §2 item 11 and §5.
5. **Part 5 (5 %):** the final writing; the md5 of every file you wrote.

Ten minutes without traction on an item: write what you have, mark it, go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD_5.md listo`, with the md5 of the report. Then go to stage 2 of `HYPERCUBE/ARRANQUE_GREPY_MUCHAS_PILAS_v1.md`.
