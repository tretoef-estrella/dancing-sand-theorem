# PAGES — cold reading 9
Method: both pdfs rendered at 72 dpi grey (pdftoppm), md5 of each page bitmap compared (`logs/render_cmp.log`). Both have 52 pages, A4. Changed: 1, 2, 3, 9, 30, 44, 46–52 (14 pages); the other 38 are identical bitmaps. Each changed page of v7 looked at at 90 dpi (`scratch/p90/`, `logs/render90.log`).
Note: the author says «The other 39 pages are unchanged»; 52 − 14 = 38.

| page | what is on it | changed passage seen | verdict |
|---|---|---|---|
| 1 | title, abstract | «version 7» in the byline | OK; the page is short (abstract only), as in v6 — the known short page before §1, not a defect |
| 2 | §1.0 table and record paragraph | «(§7.1, §7.4, §7.5, §9.2)», the new sentence on the eighth reader | OK; text clean, no overfull line |
| 3 | end of §1.0, §1.1, start of §1.2 | «The changes of version 7 have not yet been read cold (§13, Appendix A)» | OK; paragraph carried over from p. 2, nothing broken |
| 9 | §1.7 table end, «Why dance», «Why dry and wet», start of §1.8 | «each move gives every new floor a payment equal to minus half the product of the payments of two adjacent old floors» | OK; the paragraph grew by a few words and still fits; nothing broken |
| 30 | Props 9.3, 9.4, Lemma 9.5, start of Prop 9.6 and its proof (H) | «… the first level set of fit(x_{H'}) if Z_1 is positive there; otherwise Z_1 ≤ 0 …» | OK; Z_1 set as math with subscript; the proof runs on to p. 31, which is the same bitmap as in v6, so the line breaks after the change did not move |
| 44 | §12, §12.1 table, rows 1–9 | «every house with 1 ≤ k ≤ 6, α ≤ 3» in the gate_strict_cut.py row | OK; table rules and cells clean |
| 46 | §12.2 table, rows of readers 3 and 4 | «k ≤ 7 (k = 0 included)»; the new T(λ) row with both runs; «1 ≤ k ≤ 7» twice | OK; the longer T(λ) row pushes one row to p. 47, leaving the lower ~15 % of the page empty — the house rule «no table row broken across a page», not a defect |
| 47 | §12.2 table, rows of reader 5 to the turned lid | «1 ≤ k ≤ 7, α ≤ 3 (65 532)» | OK; header repeated |
| 48 | last §12.2 row (reader 6), §13, start of Acknowledgements | «1 ≤ k ≤ 6»; the new §13 sentence; «Changed in version 6, read cold»; the new v7 line; «Not done: … version 7» | OK; one loose line in §13 («Version 2 added the strictness …», justified wide) — style, not counted |
| 49 | end of Acknowledgements, App. A to the start of «Version 2» | «five days, from 2 to 6 October 2026»; reader 4 «1 ≤ k ≤ 7, α ≤ 3» | OK |
| 50 | App. A, «Version 2» to «Version 5» | none of v7 (reflow only) | OK |
| 51 | App. A end («Version 6», «Version 7»), References [ABERS55]–[Hum72] | the v6 entry on reading 8; the v7 entry | OK on the page; the v7 entry carries the false «and no number» (REPORT §2.9) |
| 52 | References [IKKY23]–[Yue24] | [LZ22] «with an appendix by S. Casalaina-Martin» | OK; last page, half empty, normal |

Summary: 14 changed pages, all looked at; nothing broken on any of them.
