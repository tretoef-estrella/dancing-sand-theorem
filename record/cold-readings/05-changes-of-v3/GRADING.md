# SECOND LOOK — cold reading 5 against the history of the project

Grepy Muchas Pilas, 5 October 2026, written after `REPORT_COLD_5.md` was finished (md5 `6c4ef1d935604362cf4e7eb9ecf200a9`, 19:20:38) and after stage 2 of `ARRANQUE_GREPY_MUCHAS_PILAS_v1.md`.

**Read for this look:**
- `LEEME.md`, `CLAUDE.md` (its UPDATE blocks), `MAPA.md`, `GREPY_HYPERCUBE_EN_ESPERA_v32.md`, and `notes/historico/GREPY_HYPERCUBE_EN_ESPERA_v6.md` §2;
- `RELATO/RELATO_DEL_CUBO.md`, and the last 80 lines of `BITACORA.md` (Grepy Bross's builds 1–17 of version 3);
- the four gradings `reports/LECTOR_FRIO_{1,2,3,4}/CALIFICACION_*`, plus targeted greps in the reports of readers 3 and 4;
- `paper/CORRECTIONS_v1_to_v2.md` and `paper/CORRECTIONS_v2_to_v3.md`;
- `reports/VOLADOR_4/AUDIT_FLIGHT_4.md` whole; `reports/VOLADOR_8/AUDIT_FLIGHT_8.md` and `reports/VOLADOR_9/AUDIT_FLIGHT_9.md`, their verdicts and first sections;
- `notes/BARRIDO_LITERATURA_PAPER_DEL_CUBO_v1.md`, `notes/BARRIDO_NOVEDAD_TEOREMA_D_v1.md` (head), [a private note of the author, not published — redacted in this copy], `notes/GLOSARIO_PROPUESTO_v1.md`, `PARA_EL_REPO/README.md`.

**Not read:** the flights' reports themselves, the audits of flights 1–3 and 5–7, and the rest of the two audits 8 and 9. The paper was not re-read whole a second time: I re-read the changed passages with their history beside them.

## 1. My findings, one by one: new, or seen before?

### 1.1 The mathematics and the text (report §1, §3, §5)

| # | finding (report section) | seen before? | comment |
|---|---|---|---|
| 1 | The paragraph after Lemma 7.9 says strictness is needed «only» in Proposition 9.6 (H), but the text still cites it in Theorems 7.8 and 7.10, and 9.6 (H) needs it twice (§1.2). | **Partly.** The sentence is Grepy Bross's, from grading 4 §2.2 («needed only where level sets matter: Proposition 9.6 (H)»), where he corrected reader 4 about `i = 0`. | **New:** «twice in 9.6 (H)» (the base-cell induction as well as the penalty shift); and that the word «only» contradicts the text, which still argues Theorem 7.10 (U2) through strict cuts. |
| 2 | §1.2's «(Lemma 7.9)» needs Proposition 5.3, Lemma 7.5 and Proposition 5.4 as well (§1.3). | **New.** The remark was added in version 3 and had not been read. | |
| 3 | The proof of Lemma 10.6(a) never says that the move is clean; Remark (2) should also cite Proposition 4.2 (§1.7). | **New.** Reader 4 and Bross found the missing «even»; neither looked at whether the proof states cleanliness. | |
| 4 | Appendix A attributes to reader 4 the gap in Lemma 10.6(a), which `CORRECTIONS_v2_to_v3.md` §1.1 says the author found (§1.8). | **New.** The error was introduced in version 3. | |
| 5 | «One false sentence, in a remark used nowhere» understates: Lemma 10.6(a), a lemma that *is* used, had the same gap (§1.8). | **New.** | |
| 6 | §13 grades the Main Theorem «read cold», while its printed proof passes through Lemma 7.9, which was not yet read cold (§1.8). | **CAME BACK.** Reader 4 found the same contradiction in version 2 (its report, line 159: «§13, bullet 1 vs bullet 2»). Version 3 reconciled the bullets for the repair of version 2, and the same inexactness came back with the new Lemma 7.9. | |
| 7 | «keeps the repair of version 2 as it was read»: the words of the repair were edited (§1.8). | **New.** | |
| 8 | §13's list of changed statements omits Lemma 10.6(a) («even» added) and Lemma 10.10 (quantifier added) (§1.8, p45). | **New.** `CORRECTIONS_v2_to_v3.md` itself opens with «No statement of a theorem changed», which is true of theorems only. | |
| 9 | «Why dance»: «at every step each floor pays … `2^α(i + d)`» is true only of the first system (§1.9). | **CAME BACK, half-fixed.** The sentence comes from the glossary draft (`notes/GLOSARIO_PROPUESTO_v1.md`, «At every step each floor p…»). Reader 4 flagged «each floor pays a power of 2». Version 3 changed it to «an even amount, `2^α(i + d)`», which is still exact only at the start. | |
| 10 | §12.1: «`k ≤ 6` (`λ ≤ 127`)»; the last `λ` with a house is 126 (§1.10, §6). | **New.** The gate's command-line bound (127) leaked into the text. | |
| 11 | §12.1, Propositions 5.2–5.4: the range omits `i ≤ 40` and `α` (§1.10, confirmed by the code in §6). | **New.** Readers 3 and 4 corrected other rows of the same table, not this one. | |
| 12 | §12.2, reader 4: «7 634 cells» against «7 874 cells», with no word on the difference (§1.10). | **New.** Grading 4 repeats «7 634 cells» without comment. | |
| 13 | §12.2: «`n ≤ 300 · e ≤ 8`» (§1.10). | **New**, minor. | |
| 14 | Two presentation hunks change words beyond what the author's list says: Lemma 3.5, and Lemma 10.10's quantifier (§3). | **New.** | |
| 15 | §1.4 item 1 cites «[GMMY24, Proposition 2.5]» for the change of variables, which lives in the *proof* of Proposition 2.5 (§5 item 9). | **CAME BACK, half-applied.** Reader 1 gave the exact credit («proof of their Prop. 2.5», grading 1 §3.4); it was applied in §2.1 (md line 225) and not in §1.4 (line 133). | |
| 16 | References: the key [GMM19], the year of [DEGJPP24], a DOI for one entry only, no access date for [OEIS], an issue for [Yue24] only (§5 item 11). | **Mostly new.** The four journal entries were checked against Crossref for version 2 (`CORRECTIONS_v1_to_v2.md` §6), and their data are right; the inconsistencies of form were not raised. | |

### 1.2 The pdf (report §4, §5, §6)

| # | finding | seen before? | comment |
|---|---|---|---|
| 17 | G1, G5, G7: formulas wholly in italic (digits, brackets, operator names, words) | **New**, as far as the records show. No reading and no page look of builds 1–17 mentions it. | It is the most visible typesetting defect, and a builder rule cannot fix it; it needs a math renderer. |
| 18 | G2: indices not stacked | **New** in the records. | Same remark. |
| 19 | G3: bold formulas; G4: no quad between formulas of one display; G8: upright `i` in italic labels | **New.** | |
| 20 | G6: the line stretch goes inside formulas | **Known and accepted by the author, with a measure that cannot see it.** Bross saw it in build 1 («spaces inside formulas stretched by justification»), tried fixed spaces (rule (13)), and dropped them in build 12 because «text gaps > 7 pt: 24 → 2» (BITACORA 17:58:14; `CORRECTIONS_v2_to_v3.md` §2). | **New:** the trade-off was judged with `gaps_text_words.py` only, which measures the gaps between two plain words and is blind to the gaps inside formulas that dropping (13) produced. Only one side of the trade-off was measured. |
| 21 | Five numbered statements split across pages | **New.** Rule (22) keeps *blockquote* statements together; the lemmas and propositions are plain paragraphs. | |
| 22 | Five lines that begin with a relation or an operator; the mechanism of `|` (break class BA) and of a code span that begins with a relation | **The class is known; these instances and the mechanism are new.** Bross found breaks before binary operators in build 1 (p4–p6) and added rules (14) and (16). The surviving cases are where those rules cannot reach. | Likely mechanism, not tested by a rebuild. |
| 23 | Breaks between «]» and «[» (p36, p38) | **CAME BACK in a sibling form.** Bross found «)(» on p32 of build 13 and added rule (23) for «)(» only. | |
| 24 | Displays wrapped by the renderer, continuation centred (p15, p16) | **CAME BACK.** Bross found «p19 `u_1` display wraps» in build 13 and fixed that one by hand; two more remain. | |
| 25 | «`Σ_{t∈I} h_t = 0.`» alone at the end of a paragraph (p19) | **CAME BACK in a new form.** In build 13 the lone fragment was «0.»; rule (24) fixed that case, and now the whole short formula stands alone. | |
| 26 | The p7 and p41 blanks: to be fixed | **Known, accepted by the author** (`CORRECTIONS_v2_to_v3.md` §2, «Accepted»). | I disagree, with the cause of each (rule (22) with the keep of the intro; the column widths of rule (9)). The decision is the author's. |
| 27 | The loose line of p14 (7.4 pt) | **Known** as a number (the one line above 7 pt). | Its visibility to the eye was not stated. |
| 28 | The §12.1 table: unbalanced columns, an orphan row, a path broken at its slash | **New.** The fixed widths come from rule (9) (version 2); rule (25) excludes paths with «/». | |
| 29 | Widow at the top of p21; heading §4.4 with one line; a formula split across p11→12; `min` / `D`; `step` / `1` | **New.** | |
| 30 | Bulleted references; Type 3 fonts; no Author in the metadata | **New.** | |

## 2. Did a finding of an earlier reading come back?

Yes, four:
- **the §13 contradiction** (reader 4 on version 2), now through Lemma 7.9 (row 6);
- **the «Why dance» payment** (reader 4), half-fixed (row 9);
- **the [GMMY24] Proposition 2.5 credit** (reader 1), applied in one place of two (row 15);
- **the pdf classes «display wrapped by the renderer» and «short formula alone»** (Bross's own page look of build 13), which reappear elsewhere after each was fixed where it was seen (rows 24–25), and **«)(»**, which reappears as **«][»** (row 23).

The pattern is the same in each case: a correction is applied *at the place where it was reported*, and the same defect elsewhere in the text is not searched for. The rule I propose for version 4: **every correction is followed by a grep or a scan for the same defect in the whole paper.**

## 3. What the history shows that I missed

- **The process of version 3 was more careful than the pdf suggests:** seventeen builds, each looked at. Pages 1–21 were last looked at on build 13 (`CORRECTIONS_v2_to_v3.md` §4); builds 14–17 changed rules (23)–(26) and later pages, and the author looked at «every page that changed». Some of the defects I found in pp. 1–21 (p14, p15/16, p19) may come from reflow after build 13. I cannot tell from the records which.
- **Reader 4 had already measured my S1 range**: 65 532 houses at `k ≤ 7`, the same strictness control 7 967 of 30 078. My gate agrees exactly with it, and I did not know at the time that I was repeating it. My gate is independent code, so the agreement counts, but the figure is not new.
- **I did not check notation.** Reader 3 asked to rename the overloaded symbols (`τ`, `κ`, `σ`, `φ`, `ε`). Version 2 renamed most of them and declared the rest in §1.6 (`CORRECTIONS_v1_to_v2.md` §7). My reading never looked at this; I have no finding on it either way.
- **Remark (2) of §10.5:** the history (grading 3 §1.2) shows that its measurement exists, with random constant weights. I judged only the word «even», which is right; the numbers in the remark were already traced and published (`gate/remark2/`).
- **The integrality of the fit** was found by reader 4 and proved by Bross before version 3 was written; my derivation is a third reading of it, not a discovery.

## 4. My errors in stage 2

- One `echo` starting with `=` in zsh, against the house rule; it printed an error and did nothing else (BITACORA).

— Grepy Muchas Pilas
