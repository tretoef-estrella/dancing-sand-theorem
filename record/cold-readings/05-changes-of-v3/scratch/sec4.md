All 47 pages were looked at, in order, at 90 dpi, with 200-dpi zooms of every doubtful region (`scratch/p90/`, `scratch/z/`). One line per page is in `checks/PAGES.md`; its ADDENDA list the defects that the automatic checks of §5 found afterwards and that I had **not** seen at 90 dpi (nine of them; see §8).

**Verdict: the pdf is not perfect.** It is clean in its large structure (margins, fonts, tables that break with repeated headers, cases on new lines, the cross-references, the citations), but a typesetter of a top journal would correct the following.

**A. Global defects (on every page with mathematics).**

| # | defect | where | fix |
|---|---|---|---|
| G1 | inside formulas everything is italic: digits, brackets, punctuation, operator names (`SL`, `Syl`, `coker`, `max`, `min`, `mod`, `dim`, `rank`, `Hom`, `Ext`, `exp`) | everywhere | digits, brackets and operator names upright; only variables italic |
| G2 | sub- and superscripts on one base are set one after the other, not stacked (`⊕_{j=1}^{n}`, `σ^{(α)}_i`, `Σ_{…}^{…}`) | everywhere | stack them (MathML `msubsup`, or KaTeX/MathJax) |
| G3 | the bold of the md is kept inside displayed formulas (the Main Theorem, Theorem DW, many displays); one display (p35) is half bold | p3–p5, p12, p35, p39, … | no bold in formulas |
| G4 | several formulas in one display separated by «, » and one space | p3, p4, p12, p39, … | a quad between formulas |
| G5 | floor and ceiling brackets slanted; `⌈j/2⌉` reads like «[j/2]» | p2, p27, p32, … | upright delimiters |
| G6 | the stretch of a justified line goes inside the formulas (spaces two to three times normal around `=`, `+`, `≤`) | p10, p11, p12, p19, p20, p23, p26, p27, p29, p30, p31, p34, p38, p40 | fixed spaces inside formulas (no stretch); rephrase the worst lines |
| G7 | words inside formulas are italic («with every exponent raised by one», «on», «coker(σ on R)») | p2, p5, p10, p16 | text inside formulas in roman |
| G8 | in the italic labels «*Step 2* (i ≥ 1)», «*The case* i ≥ 1», «The case i = 0» the `i` is upright | p19, p26, p40 | variable in italic, as in the text |

**B. Specific defects (to be fixed).**

| # | page | defect | fix |
|---|---|---|---|
| 1 | 7 | a quarter of the page blank: §1.7 (heading, introduction, table) is pushed whole to p8 | let §1.7 start on p7; the table breaks with its header repeated anyway |
| 2 | 11→12 | an inline formula broken after «=» across the page break («indeed `F^{(m)}v ⊗ b_1 =` / …») | display it |
| 3 | 14 | the loosest text line of the paper (7.4 pt mean gap), visible: «tions, and their reductions are isomorphic (Lemma 3.5), so they are isomorphic (Corollary 3.4).» | rephrase, or let the formula of the next line break |
| 4 | 15 | a display wrapped by the renderer inside the bracket `[…]`, continuation centred | break by hand after «`π_u(2f) +`», continuation indented |
| 5 | 16 | a display wrapped by the renderer, continuation centred | break by hand |
| 6 | 15→16 | the statement of Proposition 4.2 split across the page break | keep statements together |
| 7 | 16 | heading §4.4 at the foot with one line under it | keep a heading with two lines |
| 8 | 19 | proof of Proposition 5.3: a line begins with «`+ s_2(ξ) − s_2(K + o_E) = …`» | display the formula |
| 9 | 19 | «`Σ_{t∈I} h_t = 0.`» alone on the last line of a paragraph | rephrase as a display |
| 10 | 19→20 | the statement of Proposition 5.4 split across the page break | keep statements together |
| 11 | 20 | «`u_1(D) + min` / `D − min E`»: the operator `min` separated from its argument | no-break space after `min`, `max`, `mod`, `dim`, … |
| 12 | 20→21 | p20 ends about a ninth blank, and the last line of a bullet of the proof of Theorem 6.2 stands alone at the top of p21 (widow) | widow/orphan control for list items |
| 13 | 22→23 | the statement of Lemma 7.3 split | keep statements together |
| 14 | 23→24 | the statement of Lemma 7.6 split | keep statements together |
| 15 | 24→25 | step 1 of Theorem 7.8 ends p24 with «By Lemma 7.3,» and its display is on p25 | keep a lead-in with its display |
| 16 | 27 | proof of Lemma 9.1: a line begins with «`≥ 2` has mean `≥ 2`» | «numbers that are all `≥ 2`», or a no-break space |
| 17 | 28 | «step» / «1 reads»: a word separated from its number | no-break space |
| 18 | 29 | proof of Corollary 1.6, item 1: a line begins with «`≤ g(n − i + 1) ≤ G`», and the sentence «Shifts `i ≥ 2`: `≤ g(n − i + 1) ≤ G`» has no subject | «Shifts `i ≥ 2`: every dancer is `≤ g(n − i + 1) ≤ G`» |
| 19 | 29 | same item: a line begins with «`≤ max_{y≤Y_1} φ(y) ≤ G`» | no-break space before `≤` |
| 20 | 36 | «`R_𝒮 := 𝒮[F^{(m)} : m ≥ 1]` / `[E_t : t ∈ P_h]/(E_t^2)`» broken between «]» and «[» | no break between closing and opening brackets |
| 21 | 38 | the same break in «`R_{Z/4} := (Z/4)[F^{(m)}]` / `[E_t]/(E_t^2)`» | as 20 |
| 22 | 38 | proof of Lemma 10.18: a line begins with «`≡ 0 (mod 4)`» | no-break space before `≡` |
| 23 | 38→39 | the statement of Lemma 10.20 split | keep statements together |
| 24 | 41 | a sixth of the page blank inside the §12.1 table | rebalance the columns (25) |
| 25 | 41–43 | the §12.1 table: the «code» column is wide and mostly says «the same», the «result» column is narrow, so result cells run to 7–11 lines and break words at hyphens («house-/checks», «non-/zero», «non-/integral») | narrow «code», widen «result» |
| 26 | 43 | the last row of the §12.1 table alone at the top of the page under a repeated header | removed by 25 |
| 27 | 43 | the path «`remark2/gate_remark2.py`» broken at the slash | removed by 25 |
| 28 | 46–47 | the references set as a bulleted list | a hanging list, keys aligned, no bullets |

**C. Minor notes (a typesetter might leave them; listed for completeness).** p2: the middle column of the summary table is centred (left alignment reads better). p6: «cheapest `r`-» split at the hyphen of a compound that begins with a formula. p16: «`b_0 ⊗` / `b_1 n`» broken after «⊗». p17: intervals broken inside their brackets (the builder's rule (12) protects only groups of ≤ 40 characters). p17, p23: third-level exponents and a subscript made of words are tiny at print size. p37: the proof of Theorem 10.15 is one long paragraph («*The split move.*», «*The operators.*» would read better on new lines). p40: the box-product sign `□` is slanted. All fonts Type 3 (§5 item 7).

**Count:** 8 global defects, 28 specific defects (of which 9 were found only by the scripts of §5 — rows 3, 6, 8, 10, 12, 16, 18, 19, 22 — see §8), and 8 minor notes.
