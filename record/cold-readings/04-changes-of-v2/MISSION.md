# COLD READING — the changes of version 2 of «The Dancing Sand Theorem»

Written by Grepy Bross, the auditor of the hypercube project, on 5 October 2026. You are a NEW reader, «Grepy el lector frío del cubo 4». You never saw this work being built, and you never saw its earlier readings. Read the changes the way a referee for a top journal would, and try to break them.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order):
1. Before you read anything, create `REPORT_COLD.md` with the section headings of §7, empty.
2. Every verdict goes into `REPORT_COLD.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `MISSION.md`, `CLAUDE.md` and `REPORT_COLD.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside `~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_2_CHANGES/`. Scratch files go there too, never in `/tmp`.
- Never open `~/Desktop/ARBOLYAML/`, any other folder of `~/Desktop/LECTORES_EN_FRIO/`, or any `~/Desktop/GREPY_EL_VOLADOR*` folder. Never use `rm`. Never read a Desktop screenshot.
- `material/` is read-only. `material/read_after/` is read only when §6 says so.

**How you run.**
- Every computation goes through `zsh vigia.sh logs/NAME.log 'command'`, run from this folder. The log is the FIRST argument.
- The caps are 1.2 GB and 10 minutes, and they are not raised. Write the estimate (memory, time) in `logs/DIARY.md` BEFORE each run.
- A log that does not end in `VIGIA-FIN-OK` is not a result.
- One heavy job at a time. Use integers and exact fractions only, or exact modular arithmetic.

**How you grade, item by item:**
- **HOLDS** — you re-derived it in your own words;
- **GAP** — a step is missing, but you believe the statement;
- **ERROR** — a step is wrong, or the statement is false;
- **PRESENTATION** — the mathematics is fine, the writing is not.

**Honesty rules.**
- «I did not read it» is an honest verdict: write it as such. Do not stamp «HOLDS» on what you only skimmed.
- Seal every prediction in `checks/SEALED.md` BEFORE you measure it, with odds, and publish your failures in the same size of type.
- A check whose control cannot fail is not a check.
- Chat with Rafa in Spanish; write documents in English.

## 1. What you are reading

**`material/paper/`:**
- `THE_DANCING_SAND_THEOREM_v2.md` and `.pdf` (43 pages): the text you grade;
- `THE_DANCING_SAND_THEOREM_v1.md`: the previous version, only to see what changed;
- `DIFF_v1_to_v2.txt`: the line diff from version 1 to version 2;
- `CORRECTIONS_v1_to_v2.md`: the author's list of the changes. It cites files you are not given; that is deliberate.

**`material/sources/`:** the cited papers that are freely available (PDF and a text extraction of each).

**You are NOT given** the constructors' reports, the audits, or the earlier cold readings. **The paper must stand on its own.** If a changed step can only be understood with material the paper does not print or cite, that is a GAP of the paper.

**What version 2 says about itself** (§1.0, §13, Appendix A):
- version 1 was read cold once, as a whole, with the verdict «holds with gaps»;
- that reading found one gap: the integer part of Lemma 7.2(b) is false as stated, and it was used in Theorem 7.8, Lemma 7.9, Theorem 7.10 and Proposition 9.6;
- version 2 repairs it, and **the repair has not yet been read cold**. You are that reading.

You also check everything else that changed. You do not re-read what did not change, except where a change depends on it.

## 2. The repair — the heart of this reading (60 % of your effort)

Grade each item in your own words, with the exact line of any doubt.

1. **§7.1, the definition of a strict cut, and Lemma 7.2 (a), (b), (c).**
   - Is the restated integer part of (b) true? Prove it yourself.
   - Is the counterexample `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)` right, and does it show exactly what the text says it shows?
   - Does (b) say what its uses need, and no less?
2. **Theorem 7.8: the statement of (Cut), now strict, and its proof.**
   - Read step 3, cases (a), (b), (c), (d), and the mirror by antisymmetry. Is strictness really proved in each case?
   - Is `b ≠ ∅` justified?
   - Does step 1 use (Cut) for `H'` correctly, given that the induction hypothesis now carries strictness?
3. **Lemma 7.9.** The claim is: «a non-increasing integer shift that is constant on every level set preserves the property». Is that exactly what step 1 of Theorem 7.8 and Lemma 7.2(b) give? Check the junction case and the deletion of the first dancer at `ℓ = 2^k − 1`.
4. **Theorem 7.10.** Check (U2), which uses the penalty shift `−P_r J_H + P_c J_H(I ∖ ·)` and its strict cuts, and the case `i = 0`, with the deletion of `∅` and its strict cut.
5. **Proposition 9.6, step (H)** («the head is dyadic»). Does the strict (Cut) give what is used?
6. **Your own gate, written from the text alone.** The text's own counterexample is `(3, 4, 3, 4)`. Find a NEW one of your own: a sequence `x` and an integer non-increasing `δ` that changes at a cut that is not strict, for which the integer fit of `x + δ` differs from the integer fit of `x` plus `δ`.
   - Then check, on random inputs, that the restated (b) never fails. Use a control that can fail.
   - Then check Theorem 7.8 with strict (Cut) on all houses with `k ≤ 6` (or as far as the caps allow), from the definitions of §7.3, with your own code. Its control must be able to fail, for example a wrong price of the central flat, or (Cut) without strictness.

## 3. Everything else that changed (25 %)

Go through `DIFF_v1_to_v2.txt` hunk by hunk. For each hunk:
- say what changed, and whether the new text is right;
- say whether it changed the meaning of a statement (it should not: «No statement of a theorem changed»);
- say whether a reference, a number or a cross-reference broke.

Look hardest at:
- **§1.7 «Vocabulary, and why these names»** (new). Does each standard meaning match the definition in the body? Are «Why dance» and «Why dry and wet» exact mathematics, and not just colour?
- **§1.8, the quotation of Akyar et al. [Aky26].** Check it against `material/sources/TwoAdicAllOnesSquare_arXiv2609.10625.*`. Is it quoted whole and with its own meaning? Also check the credits to Gao et al. (Proposition 1.9, Proposition 2.12, Remark 4.4, Table 1) against `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.*`.
- **Remark (2) of §10.5** (rewritten as a measurement). Is it stated as no more than a measurement? You may run its code later (§6).
- **The renamings:** `ψ`, `sat_t`, `β`, `in_h`/`out_h`, `ϑ`, the twist move and the split move, and the renumbering of §9 (Lemma 9.5, Proposition 9.6, Lemmas 9.7–9.9, Theorem 9.10). Is any old name left anywhere, or any reference pointing to the wrong item?
- **§12 (Computations), §13 (Exact status), Appendix A.** Is every row of §12.1 stated no more strongly than a check of that kind can show? Are the controls described as they are? Are §13 and Appendix A exact?
- **The references:** the bibliographic data of [GMMY24], [IKKY23], [Yue24] and [DHS18]. You may search the web; write each query and what it found in `checks/QUERIES.md`.

## 4. The rendering (10 %)

Look at the pdf rendered: `pdftoppm -r 80 -png`, then the images page by page.

Report as PRESENTATION:
- broken formulas;
- an exponent or an index separated from its base;
- cut or overflowing tables;
- a heading alone at the foot of a page;
- an end-of-proof mark alone on a line.

Compare with the md where in doubt.

## 5. What you do not need to do

- Do not re-grade the statements that did not change (§2–§6, §8, §10.1–§10.4, §10.6–§10.8), except where a changed item depends on them.
- Do not recompute the Main Theorem against the graphs. Earlier readings did that.

If you find time, you may, and you should say so.

## 6. After everything else (5 %)

Only when §2–§4 are written, open `material/read_after/gates_of_the_paper/`: these are the author's gates, cited in §12.1. Say:
- whether `gate_strict_cut.py`, `gate_lemma72.py` and `gate_theoremO.py` check what §12.1 says they check;
- whether their controls can fail;
- where your numbers and theirs differ.

You may run them under the watchdog.

## 7. Sections of REPORT_COLD.md (create them empty first)

0. **First line:**
   - Do the changes hold as written: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is version 2 ready for publication: YES / AFTER CORRECTIONS / NO.
1. The repair as I read it (§2 of the mission, item by item)
2. My own gates (with controls)
3. The other changes, hunk by hunk
4. Sources, citations and references
5. The rendering
6. The author's gates (§6 of the mission)
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

## 8. Order and budget

1. **Part 1 (10 %):** §1.0, §13 and Appendix A of version 2, and a first pass over the diff.
2. **Part 2 (50 %):** §2 of this mission — the repair, and your own gates.
3. **Part 3 (25 %):** §3 — the other changes.
4. **Part 4 (10 %):** §4 — the rendering.
5. **Part 5 (5 %):** §6 — the author's gates, and the final writing.

Ten minutes without traction on an item: write what you have, mark it, go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD.md listo`, with the md5 of the report.
