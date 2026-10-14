# Version 10 → version 11 of «The Dancing Sand Theorem» (Grepy el Notario, 14 October 2026)

Rafa's order of 14 October 2026: «corrige el paper, el md y el pdf» (mission `MISION_BETZER_v1.md` §3). Version 11 credits Betzer's earlier proof of [GMMY24, Conjecture 4.14] (D. N. Betzer, Zenodo 10.5281/zenodo.22065778, 23 August 2026), read line by line on 13 October 2026 in `notes/BETZER_LECTURA_v1.md` (verdict: his computation is correct for every `n ≥ 3`; the identification with `c_n(Q_n)` is taken from [GMMY24, Remark 4.13], which is stated there without proof). Version 11 is built from version 10 by `v11_edits/text_edits.py`: anchored replacements, each asserted unique. The diff is `v11_edits/DIFF_v10_to_v11.txt` (12 hunks); the word-level diff is `v11_edits/WORDDIFF_v10_to_v11.txt`. **No statement, proof or number of the mathematics changes.**

| # | Place | Change |
|---|---|---|
| B1 | header | `11 October 2026 · version 10` → `14 October 2026 · version 11` |
| B2 | abstract | «the latest work on it determines its `n − 1` largest cyclic factors» → Gao et al. determined the `n − 1` largest, «and Betzer the `n`-th, through a remark of theirs stated without proof» |
| B3 | abstract | «we prove their Conjectures 4.14 and 5.4» → «we prove their Conjecture 4.14 without that remark, and we prove their Conjecture 5.4» |
| B4 | §1.0, table, Corollary 1.6 | «(proved earlier by Betzer [Bet26] through a remark that we do not use; §1.8)» |
| B5 | §1.0, record of the readings | «up to 11 October 2026»; one sentence: the correction of 14 October 2026 changes no statement, proof or number, was checked against its sources by the auditor and was not read cold |
| B6 | §1.1, the history | one sentence: in a preprint of August 2026 Betzer proved Conjecture 4.14 given [GMMY24, Remark 4.13], stated there without proof; he computes the `2`-adic valuation of the order of the class of `x_1x_2 − 1` in an explicit quotient for every `n ≥ 3` [Bet26, Theorem 11.4] |
| B7 | §1.4, after Corollary 1.6 | one paragraph: the formula for `c_n` was proved earlier by Betzer [Bet26, Theorem 11.4], given [GMMY24, Remark 4.13]; our proof (§9.2) does not use that remark |
| B8 | §1.8, where we searched | «the preprint servers Zenodo and Hexagon (searched on 13 October 2026)» (`notes/BARRIDO_ZENODO_HEXAGON_v1.md`) |
| B9 | §1.8, item 3 | «we found no other proof» now covers only Conjecture 5.4 and the `(n+1)`-th factor; for Conjecture 4.14, «a proof that does not use [GMMY24, Remark 4.13] (Betzer's earlier proof uses it; see below)» |
| B10 | §1.8, what is not ours | three sentences on [Bet26]: what he computes, that the identification with the `n`-th invariant factor comes from the remark, and that we learned of his paper on 13 October 2026, after our proof was written; earlier versions did not cite it |
| B11 | §13 | «up to 11 October 2026»; one sentence on the correction of 14 October 2026 |
| B12 | Appendix A, later versions | one sentence: the correction of 14 October 2026 was prompted by [Bet26], not by a reading; checked against [Bet26] and [GMMY24] by the auditor; not read cold |
| B13 | references | [Bet26] D. N. Betzer, Sandpile groups of Cayley graphs over `𝔽_2^r`: Sylow-2 structure, isospectral counterexamples, and Boolean incidence algebra, preprint, Zenodo (August 2026), DOI 10.5281/zenodo.22065778 |

**Sources of every new sentence.** Betzer's PDF (`sources/BETZER_2026-08-23/`, md5 `94fc82c6180a3af3812c2b3dbc607250`): title and author on p. 1 (`betzer.txt` l. 1–3), Theorem 11.4 at l. 1218–1226 («for n ≥ 3»; «its additive order has 2-adic valuation equal to the displayed quantity»), proof l. 1228–1368, the reliance on Remark 4.13 at l. 1225 and l. 1250, «August 2026» on the title page; Zenodo publication date 2026-08-23. [GMMY24] arXiv v3, `sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt` l. 1151–1160: Remark 4.13 begins «One can show that …» and no proof follows. Our proof of Corollary 1.6 (§9.2) does not cite Remark 4.13 (no «4.13» in version 10).

**Builder.** `build_v11.sh`, the builder of version 10 with only the name changed.

**One wording change during the build.** The first wording of B7 ended with «(§1.1, [Bet26, Theorem 11.4])»; the unbreakable citation stretched the first line of the paragraph to 3.05 times the median word space (check 6). It now reads «Betzer [Bet26, Theorem 11.4], given [GMMY24, Remark 4.13] (§1.1)», same content; looked at on page 6.

**Acceptance** (`checks_v11/acceptance.py`): the twelve checks of version 10, with three declared changes, made after looking at the pages (70 dpi):
- check 5: the declared short page moves from 45 to 46 (the same table row of §12.2; page 47 begins with the table's header), and page 16 is declared short (Proposition 4.2 begins with a paragraph followed by a display and moves whole to page 17);
- check 6: the three non-text lines move (table row «formal dance; positions; covariant system» p. 9, display (K) p. 11, labels of the twist map's block matrix p. 35), same gaps 12.77, 14.37, 11.11 pt as in versions 7–10;
- check 9: [Bet26, Theorem 11.4] added to the external items.

Result: 12/12 PASS (`logs/v11_acceptance_3.log`); control: 12/12 FAIL (`logs/v11_acceptance_3_control.log`). The v11 list run on version 10 gives 12/12 PASS (`logs/v11_acceptance_on_v10.log`), and so does version 10 rebuilt today with Chrome 155 (`logs/v11_acceptance_on_v10_today.log`): the moved positions come from the new text, not from the browser.

**Pdf.** 53 pages (version 10: 52). Word diff of the pdf text against version 10: `v11_edits/PDF_WORDDIFF_v10_to_v11.txt` — the new sentences and nothing else, apart from words that pdftotext reads in another order around displays, page folios inside words split across pages, and line-end hyphens. Looked at: pages 1, 2, 3, 6, 9, 10, 11, 16, 17, 35, 46, 49, 51, 52, 53.

**Not read cold**, on Rafa's judgement (14 October 2026) and the auditor's double check: no statement, proof or number changes; every new sentence is checked against its source above; and the three sentences of the text that say the changes of every version were read cold now say «up to 11 October 2026» and name this correction as the exception.

md `63a72b6bc02c49c9f90dd790cc1c0f8b`, pdf `167fc5b4d5afa76bf734a29d0ab1942c`.
