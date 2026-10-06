# COLD READING — the paper «The Dancing Sand Theorem», version 1, read whole

Written by Grepy Bross, the auditor of the hypercube project, on 5 October 2026. You are a NEW reader, «Grepy el lector frío del cubo 3». You never saw this work being built. Read the paper the way a referee for a top journal would, and try to break it.

## 0. The order of the house — read before anything

**NO AGENTS. NO SUB-AGENTS. NO WORKFLOWS. YOU DO EVERYTHING YOURSELF, IN THIS ONE WINDOW**, whatever mode the session is in.

**SAVE TO DISK AS YOU GO, NEVER AT THE END** (Rafa's permanent order):
1. Before you read anything, create `REPORT_COLD.md` with the section headings of §7, empty.
2. Every verdict goes into `REPORT_COLD.md` the moment you have it.
3. Write a line in `logs/DIARY.md` BEFORE and AFTER every step and every run. Paste the time from `date`; never type it.
4. Keep `CLAUDE.md` (your re-entry note) up to date: one STATE line after each part. If your window is compacted, re-read `MISSION.md`, `CLAUDE.md` and `REPORT_COLD.md`, and go on.
5. What is not on disk does not exist.

**Where you work.**
- Write only inside `~/Desktop/LECTORES_EN_FRIO/CUBO_PAPER_1/`. Scratch files go there too, never in `/tmp`.
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

## 1. What you are reading, and what you are not given

- `material/paper/THE_DANCING_SAND_THEOREM_v1.md` (the text; 1 026 lines) and `.pdf` (39 pages, the same text rendered).
- `material/sources/`: the cited papers that are freely available (PDF and a text extraction of each).

**You are NOT given** the constructors' reports («flights»), the audits, or the two earlier cold readings. That is deliberate. **The paper must stand on its own.** If a step can only be understood with material the paper does not print or cite, that is a GAP of the paper, even if you believe the statement.

The paper claims (§1.0):
- **the Main Theorem**: the whole `2`-part of the sandpile group `K(Q_n)` of the `n`-cube, for every `n`, by an explicit rule;
- **Theorem DW**, the fold law: `Syl_2 K̄(n) ≅ 2·Syl_2 K(Q_n)`, `K̄(n)` the sandpile group of the folded cube; and **Corollary 1.4**, the whole sandpile group of the folded cube;
- **Corollaries 1.5–1.7**: Bai's counts; the `n + 1` largest factors (Gao et al.'s Theorems 4.1, 4.2, their Conjecture 4.14 and the `(n+1)`-th factor of their 2019 poster); and their Conjecture 5.4.

Its own status line (§13): the Main Theorem, Theorems D, O, F, DW and Corollary 1.4 were read cold before, chain by chain, but **the text as a whole has never been read cold**. Corollaries 1.5–1.7 were read cold only numerically. You are that first reading.

## 2. The mathematics, statement by statement

Grade **every numbered statement** of §2–§10 (Lemma 2.1 to Remark of §10.8: about 80 items), and the proofs of §8 and §10.8 (the assemblies). For each one write in `REPORT_COLD.md`:
- the statement in your own words;
- your verdict;
- the exact line or step where any doubt lives;
- the external facts it uses, and whether they are used correctly. Examples: Kummer's carry theorem, Strassmann's theorem, von Staudt–Clausen, Schur complements, the block-inverse identity, Donkin's tilting theory, isotonic regression.

**Read these hardest — they were never read cold as text:**
1. **§6.2, Theorem 6.2 (Theorem O)**: the proof by «top bits» is new in this text. Is the golden bijection really unique, and does the proof show it?
2. **§9 entire**: Lemmas 9.1, 9.2, 9.6–9.8; Propositions 9.3–9.5; Theorem 9.9. Do they really follow from the Main Theorem? Do they say exactly what Gao et al. conjectured, in Gao et al.'s own notation (check against `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.*` and the poster)?
3. **§10 as organized here**:
   - Lemma 10.8 → Theorem 10.12 (rigidity);
   - Lemmas 10.13, 10.14 → Theorem 10.15 (cleanliness: the ring `𝒦` and the shadow ring `𝒮`);
   - Lemmas 10.18–10.20 → Theorem 10.22 (even families);
   - the continuity step at the shift `i = 0`.

   Is every hypothesis of Theorem 10.12 actually established by Theorem 10.15? Is the induction in Theorem 10.15 well founded?
4. **§8, the proof of the Main Theorem**: does it use every piece it names, and nothing it has not proved?
5. **§1.2–§1.3**: the rule as stated. Could a reader with only §1 compute `Syl_2 K(Q_n)` for, say, `n = 7`? Try it by hand or by code written from §1 alone, before you read §2.

## 3. The numbers, with your own code

Write your own engines in `engines/` from the definitions in the paper. Do not use anything in `material/read_after/` before §6 of this mission.

1. **The rule against the graph.** Implement the rule of §1.2 exactly as printed. Compute `Syl_2 K(Q_n)` and `Syl_2 K̄(n)` from their Laplacians with your own exact `2`-adic Smith form. Do this for `n = 2..11`, and for `n = 12` only if your estimate fits the caps. Compare.
   - **Controls:**
     - the rule with one digit of `I` dropped must fail;
     - the fold law with `a_n` changed by `±1` must fail;
     - the folded cube replaced by `Q_n/⟨x_1x_2⟩` must fail.
2. **Every number printed in §1** (the example of §1.3, the table of §1.0) and **in §9** (the values of the corollaries for small `n`): recompute the ones you can.
3. **One proof by machine.** Pick the step of §6–§7 or §10 that you trust least and gate it with your own code, with a control that can fail.
4. **§12.2**: read the table. Is each claimed range plausible for a laptop? Is any row stated more strongly than what a check of that kind can show?

## 4. Sources, citations and priority

- **Every quotation and every «[X, Theorem n]» against `material/sources/`.** Give page and line, and say whether the quoted words are really there and mean what the paper says. The quotations of §1.1 matter most (Bai, Ducey–Jalil, Chandler–Sin–Xiang, Iga et al., Gao et al., the poster).
- **References not in `material/sources/`** are: Bie93, Wil90, Don93, Jan03, TW21, Kos66, Str28, Kum52, vSt40, Cla40, ABERS55, BBBB72, Hum72, Lor91, Big99, Kli18, EL91, OEIS. For each one:
  - is it used only for a standard fact?
  - is the bibliographic data right?

  You may search the web and download arXiv papers for reading. Write each query and what it found in `checks/QUERIES.md`.
- **Priority:** is anything the paper claims as new already known? Look hardest at:
  - the whole `2`-part of `K(Q_n)`;
  - the fold law;
  - the tilting decomposition of `Z[(Z/2)^n]` with the Laplacian;
  - Gao et al.'s Conjectures 4.14 and 5.4.

  Check §1.7 («Literature and priority») line by line.

## 5. The writing — Princeton quality

The bar is a top journal. Report as PRESENTATION, with the line:
- undefined symbols, symbols used with two meanings, notation that changes between sections;
- claims in the abstract or in §1.0 that the body does not prove, or proves in a weaker form;
- a proof that is longer than it needs to be, or a redundancy;
- §12–§13 and the acknowledgements: are they honest, exact, and not more than a paper should say?
- **the pdf, looked at rendered** (`pdftoppm -r 80 -png`, then look at the images page by page): broken formulas, raw LaTeX, cut or overflowing tables, a heading alone at the foot of a page. Rendering is a real part of this reading.

## 6. After everything else

Only when §2–§5 are written, open `material/read_after/gates_of_the_paper/`: these are the auditor's own gates, cited in §12.2. Say:
- whether they check what §12.2 says they check;
- whether their controls can fail;
- where your numbers and theirs differ.

## 7. Sections of REPORT_COLD.md (create them empty first)

0. **First line:**
   - Does the paper hold as written: HOLDS / HOLDS WITH GAPS / DOES NOT HOLD.
   - Is it ready for submission: YES / AFTER CORRECTIONS / NO.
1. The claims as I read them
2. Statement by statement (§2–§10, and the assemblies §8 and §10.8)
3. The numbers, with my own code (with controls)
4. Sources, citations and priority
5. The writing and the pdf
6. The auditor's gates (§6 of the mission)
7. Sealed predictions, hits and failures
8. My errors
9. What I did not read
10. Files with md5

## 8. Order and budget

- Part 1 (10 %): §1 of the paper, and check 3.1 written from §1 alone.
- Part 2 (45 %): §2–§10, statement by statement. §6.2, §9 and §10.4–§10.7 are the heart.
- Part 3 (15 %): the remaining checks of §3.
- Part 4 (15 %): sources, citations, priority.
- Part 5 (10 %): the writing and the pdf.
- Part 6 (5 %): §6 of this mission, and the final writing.

Ten minutes without traction on an item: write what you have, mark it, go on.

When you finish, the last line of `logs/DIARY.md` is `REPORT_COLD.md listo`, with the md5 of the report.
