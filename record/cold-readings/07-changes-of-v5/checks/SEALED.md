# SEALED predictions — cold reading 7

Each line is written BEFORE the measure. Odds are my own probability that the prediction comes true.
Outcome column filled only after the measure (HIT / FAIL), never edited before.

## Sealed 2026-10-06 (time from `date` in logs/DIARY.md, entry «SEALED batch 1»), after reading §1.0, §13, App. A, CORRECTIONS, and before reading the hunks

| id | prediction | odds | outcome |
|---|---|---|---|
| S1 | No hunk changes a symbol, number, quantifier or hypothesis inside a numbered statement or proof step (item 2.1). | 80 % || HIT — no change inside a statement or proof step (REPORT §2, item 2.1). |
| S2 | At least one of the 25 formula-initial rewordings or 14 loose-line rewordings changes a small meaningful word in a way I grade ERROR or PRESENTATION (not HOLDS). | 40 % || FAIL — the rewordings keep the content; I grade two of them PRESENTATION (P2.2-a «these», P2.2-b «by subadditivity»), not ERROR. I count this a FAIL because my prediction meant a change of meaning, and there is none. |
| S3 | At least one wrong number-set choice (either way) exists in v5 md. | 55 % || FAIL — no wrong number-set choice found. |
| S4 | The pdf has at least 5 defects I grade PRESENTATION. | 95 % || HIT — 28 kinds, 170 instances. |
| S5 | `pdffonts` lists only STIX Two Text, STIX Two Math and Menlo, all embedded. | 80 % || HIT — STIX Two Text, STIX Two Math, Menlo only, all embedded (Type 3 for STIX). |
| S6 | No word runs past the right text margin (largest xMax within the margin + 0.5 pt). | 80 % || HIT — largest xMax 541.85 pt, right edge 542.0 pt. |
| S7 | The break at «=» in Lemma 2.4 that CORRECTIONS §4 lists as «left» is still in the pdf, and Appendix A does not mention it. | 65 % || HIT — the Lemma 2.4 break is in the pdf (p. 12) and App. A does not mention it. |
| S8 | The arXiv numbers added to [DJ14], [RT14], [LZ22] all match `material/sources/`. | 90 % || HIT — 1308.2335, 1301.2977, 2012.15235 match the sources. |
| S9 | «Why dance»: «replaces the payments of two adjacent floors by minus half their product» is exact for both moves as Props. 4.1–4.2 state them. | 55 % || HIT — exact for the payments of the floors in both moves (remark on couplings, P2.4-b). |
| S10 | «up to the sign (−1)^{|S|}» is exact against GMMY's proof of Prop. 2.5. | 75 % || HIT — s_S = (−1)^{|S|} u_S, exact. |
| S11 | At least one sentence of §1.0 / §13 / App. A about what was read cold is inexact (graded PRESENTATION or ERROR). | 60 % || HIT — R1 (false sentence of §13), R2, R3. |
| S12 | The numbers of the changed rows of §12.1/§12.2 are mutually consistent (no arithmetic contradiction). | 80 % || HIT — every changed number re-counted and consistent (with λ ≥ 1). |

## Sealed batch 2 — before any measure of the pdf (entry «SEALED batch 2» in logs/DIARY.md)

| id | prediction | odds | outcome |
|---|---|---|---|
| S13 | `pdfinfo`: 51 pages, A4 (595.28 × 841.89 pt). | 90 % || HIT — 51 pages, 594.96 × 841.92 pt (A4). |
| S14 | `gaps_text_words.py` on v5 reproduces the author's «14 lines with a gap above 6 pt, 1 above 7 pt». | 55 % || HIT — 718 lines, >6 pt: 14, >7 pt: 1. |
| S15 | At least one line of running text begins with a relation or a binary operator (other than the Lemma 2.4 «=» break). | 55 % || FAIL — no running-text line begins with a relation or binary operator (only display continuations and script fragments). |
| S16 | At least one end-of-proof mark is not at the right margin of the last line, or stands alone. | 20 % || FAIL — every ∎ at the right margin of the last line, never alone. |
| S17 | At least one heading alone at the foot of a page, or a numbered statement split across pages. | 30 % || FAIL — no heading alone at the foot, no statement split (the structural defects found are of other kinds: widows, split display runs, lost step numbers). |
| S18 | The md and the pdf say the same (statements, tables of §1 and §12) up to typography: no non-typographic difference. | 80 % || FAIL — one non-typographic difference: the lost step numbers 2 and 3 of the proof of Theorem 7.8 (PD1). |
| S19 | The pdf metadata (title, author) are right and the page count is 51. | 85 % || HIT — title, author, subject right, 51 pages. |
| S20 | I find at least 10 distinct PRESENTATION defects in the pdf. | 75 % || HIT — 28 kinds. |


## Tally (written after the measures, 2026-10-06)
Batch 1 + 2: 20 predictions; hits 14 (S1, S4–S14, S19, S20), failures 6 (S2, S3, S15, S16, S17, S18). Weighted by my odds, I over-predicted defects of the text (S2, S3) and of line starts and statement splits (S15, S17), and under-predicted the md ≠ pdf difference (S18 at 80 %).
