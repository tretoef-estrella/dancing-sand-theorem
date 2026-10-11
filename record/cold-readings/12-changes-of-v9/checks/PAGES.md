# PAGES — Grepy Cotejo
40 dpi comparison (logs/pages.log): v9 pages 6–42 are pixel-identical (md5 of the 40-dpi ppm) to v8 pages 6–42; v9 pages 1–5 and 43–51 differ. Each differing page looked at 90 dpi (scratch/r90/).

## Paper v9, pages that differ (90 dpi)
- p1: title block, «11 October 2026 · version 9»; Abstract with the new bold sentence at the end; «ref-ereed» hyphenated at the line end. Nothing broken.
- p2: §1.0 table (8 rows) and the paragraph with the new sentence; start of §1.1. Nothing broken.
- p3: end of §1.1, §1.2 opening (text unchanged; the page differs only because p2 grew by two lines and the text reflows). Nothing broken.
- p4: §1.2 rule, Main Theorem box, Example n = 6 (unchanged text, reflowed). Nothing broken.
- p5: §1.3 with the new description of the folded cube (`{x, x + 𝟙}`, `e_i`, «image of two edges»), Theorem DW box, Corollary 1.4, mod-2 layer, start of §1.4; p5 ends where v8's p5 ends (p6 identical). Nothing broken.
- p43: end of §11 with the new question 6, «12. Computations», §12.1 and the first six rows of its table (unchanged text, moved). Nothing broken.
- p44: §12.1 table continued (header repeated), the remark2 paragraph, §12.2 and its first two rows. Nothing broken.
- p45: §12.2 table continued (header repeated), rows to «Lemma 7.2(b), restated»; the page ends about 18 % short, because the next row (p46) is tall and does not split. This is the short page that check 5 of the acceptance list declares (see §5 of the report). Not broken.
- p46: the tall row of reader 4 «Lemma 7.9 (integrality)» starts the page (the row that did not fit on p45), and the table continues. Nothing broken.
- p47: end of the §12.2 table; §12.3 heading and its first five paragraphs. The Lean name `Classical.choice` is broken at the line end after the dot («`Classical.`» / «`choice`»): readable, not broken; style doubt S5. Otherwise nothing broken.
- p48: §12.3 «Read cold», «What Lean does not state», the `ℤ_2` sentence, «Where»; §13 with the new bullets; start of the Acknowledgements. Nothing broken.
- p49: Acknowledgements with the new paragraph (Aristotle, Claude); Appendix A opening. Nothing broken.
- p50: Appendix A continued, the new entry «Formal verification», References [ABERS55]–[DHS18]. Nothing broken.
- p51: References [DJ14]–[Yue24], with [dMU21], [Har26], [LC26], [mC20] in alphabetical place (case-insensitive). **[LC26] prints «DOI [LC-DOI]», an unfilled placeholder** (P-B16 of the report). Otherwise nothing broken.

## Certificate pdf (25 pages), the pages that the corrections touch (90 dpi; located by `scratch/certpages.py`, `logs/certpages.log`)
There is no pdf of the certificate «before» in the material, so these pages were looked at, not compared.
- c-p1: title, the new header line «read cold and corrected the same day (§2 item 7)», §0 with «for `n ≥ 2`, its equivalent form» and «Theorem 4.1 for `n ≥ 3`». The `𝟙` of `Q_n/⟨𝟙⟩` is drawn (zoom at 220 dpi). The unchanged Bai bullet breaks its formula across lines («⊕_{j=1}^n» / «(ℤ/j)^{C(n,j)}»): untouched by the corrections, readable. Nothing broken.
- c-p2: §0 «Read cold» paragraph; §1.1 with «Twenty-four statements are printed here» and the 16/21/24 sentence; the `#check` blocks. Nothing broken.
- c-p7: §1.3 table, the corrected folded-cube row (narrow first column, `{x, x + 𝟙}` and `e_i` drawn; zoom at 220 dpi). Nothing broken.
- c-p9: §1.3 table continued: the corrected DW row («`DW'` is stated for `n ≥ 2`. At `n = 1` … `a_1 = 2^{−1} − 2^{−1} = 0` …») and the Corollary 1.6 row («Gao et al. state their Theorem 4.1 for `n ≥ 2`; the case `n = 2` … is not in Lean»). Nothing broken.
- c-p10: «Generality» (corrected), §1.4 («twenty-one statements of §1.1 named there»), §2 items 1–5. Nothing broken.
- c-p11: §2 item 6 (its «(§3.2)» should be «(§3.3)», untouched by the corrections; report §3.4), the new item 7, item 8, §3 opening. Nothing broken.
- c-p14: end of the §3 table and the corrected sentence «The names in bold are statements printed in §1.1»; §3.1, start of §3.2. Nothing broken.
- c-p15: §3.2, §3.3 with «except the watchdog's final line (time and memory)», the cone table, the 75 outside modules. Nothing broken.
- c-p17: §4 continued: the new paragraph «Besides, one line `attribute [instance]` …» and the unchanged «An instance adds no axiom …» print flush left, outside the bullet «Instances» that they continue (the old paragraph already did so); the corrected «Axioms» bullet (885 = 868 + 12 + 4 + 1); §5 opening. Not broken; style doubt S6.
- c-p18: §5 end, §6 with the corrected bullets («The number of checks is the total the log reports …», «The column «`theorem`/`lemma` lines» …») and the corrected provenance paragraph; Table 6a header and row C1. Nothing broken.
- c-p19: Table 6a rows C2–C35 with the regenerated column (thin spaces in the numbers; «in K kinds» for C2–C16). Nothing broken.
- c-p20: Table 6a rows C35b–C52; **the caption «Table 6b. The Lean folders and their clean rebuild.» stands alone at the foot of the page, its table starting on p21** (orphaned caption; P-D1 of the report). Otherwise nothing broken.
- c-p21: Table 6b rows C1–C33 under the renamed column «`theorem`/`lemma` lines» (the header «Rebuild s» wraps as «Rebuild / s», as before). Nothing broken.
- c-p22: Table 6b rows C34–C50h, header repeated. Nothing broken.
- c-p23: Table 6b end (C51, C52, `Main.lean`, Total 416 / 60 964 / 3 237 / 876 / 416 / 25 236 / 2.46); §7 with the renamed column and the new bullet «Theorem and lemma declarations in code: 3 449»; §8 with the new paragraph «Paths». Nothing broken.
- c-p24: §8 «Clean rebuild» with «except the watchdog's final line (time and memory)»; §9 opening. Nothing broken.

Summary: paper — nothing broken; one printed placeholder «DOI [LC-DOI]» (p51). Certificate — nothing broken; one orphaned table caption (Table 6b, foot of p20).
