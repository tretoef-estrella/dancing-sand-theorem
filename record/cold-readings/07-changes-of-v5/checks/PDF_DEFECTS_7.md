# PDF_DEFECTS_7 — defects of the v5 pdf found by cold reading 7

Each kind (PDn) with its instances (page, place). Pages refer to checks/PAGES.md. Severity: S = would stop a journal typesetter's sign-off; M = must be fixed before publication; m = minor (a careful typesetter fixes it).
Count rule: an «instance» is one place on one page (a loose line is one instance).

## A. Structure and md = pdf

| id | sev | kind | instances | n |
|---|---|---|---|---|
| PD1 | S | Steps 2 «(Λ)» and 3 «(Cut)» of the proof of Theorem 7.8 lost their numbers in the pdf (md l. 642–643 have «2.», «3.»); the list reads 1, –, –, 4, 5, 6 and «Theorem 7.8 (steps 1 and 3)» (§7.5) cannot be followed | p. 26 (two items), p. 27 (the reference) | 2 |
| PD2 | M | Pages under 90 % full that the record does not declare | p. 13 (89.0 %), p. 18 (86.1 %), p. 44 (83.8 %) | 3 |
| PD3 | M | Widow: the last line of a paragraph alone at the top of a page | p. 20 (end of the proof of Prop. 5.2), p. 37 (end of the proof of Lemma 10.10) | 2 |
| PD4 | M | A run of displays split by a page turn | p. 12/13 (E^{2s} formulas), p. 24/25 (window data) | 2 |
| PD5 | m | A formula broken at a relation across a page turn | p. 14/15 («V ⊗ T(2l + 1) = V ⊗ Φ(T(l)) =» / «T(2l + 2)») | 1 |
| PD6 | m | Theorem 10.15: the conclusion «Then the move … is clean» run on into hypothesis (b) | p. 38 | 1 |
| PD7 | m | Bold of the md lost in the pdf (emphasis of a key sentence) | p. 5 (naming trap), p. 38 (Theorem 10.15) | 2 |

## B. Setting of the mathematics

| id | sev | kind | instances | n |
|---|---|---|---|---|
| PD8 | M | Case condition off its baseline | p. 17 (Theorem 4.4, «if D' ⊆ D,» 2 mm above) | 1 |
| PD9 | M | Lower limit touching the big operator, or operator pushed off the axis | p. 17 (Thm 4.4 «d=o_D»; proof, second ∏), p. 18 (Theorem D, Σ), p. 19 (γ(Δ): Σ off axis, limit touching), p. 20 (ψ(D), nearly), p. 37 ((𝔡_2) display), p. 41 (∏_i m_i!) | 7 |
| PD10 | M | Delimiters smaller than the fraction they enclose | p. 41 (±(∏…/∏…)) | 1 |
| PD11 | M | Holes inside displays (wide limits centred under an operator; spurious space) | p. 4 (Main Theorem ⊕ with two-line condition), p. 18 (c^{(h+1)} display), p. 37 ((𝔡_2) display) | 3 |
| PD12 | m | Superscript and subscript touching | p. 17 (K^{(h)}_{DD'}, c^{(h)}_{D∖D'}), p. 18 (K^{(k)}_{DD'}) | 2 |
| PD13 | M | ℓ set with text side bearings (visible spaces around it) | every occurrence in §7.3–§9.2: pp. 24, 25, 30 (and the house/window formulas) | 3 |
| PD14 | m | Spacing glitches | p. 40 («in  = in_k»), p. 20 («R^♯ (D)» against «R^♯(D)»), p. 42 (spaces around □ stretched inside a formula) | 3 |
| PD15 | m | Inline matrices or scripts too small to read at reading size | p. 34 ([x^{00} x^{01}; x^{10} x^{11}], twice), p. 40 (L with stacked ½), p. 41 (glue(W_−, W_+)), p. 13 (Hom_{Dist_{𝔽_2}}), p. 11 (X^ι reads as X′) | 6 |
| PD16 | m | Same object set two ways | L = [1 0; 1/2 1] (p. 33) vs stacked ½ (p. 40); «exp F» (p. 32) vs «exp(F)»; «cosh u» vs «sinh(u)» (p. 33) | 3 |
| PD17 | m | Runs of displays not aligned on «=», or grids with holes | p. 16 (Prop. 4.1), p. 33 (Ψ_{2c}, Ψ_{2c−1}), p. 24 (house grid; window grid with a 4 cm hole), p. 12 (Prop. 3.1 (b) grid) | 4 |
| PD18 | m | Light mathematics in bold headings | §2, §3.2, §6, §7 headings (pp. 10, 13, 21, 22) | 4 |

## C. Line breaking

| id | sev | kind | instances | n |
|---|---|---|---|---|
| PD19 | M | Short formula or short bracket group broken (against G19 or App. A) | p. 38 («(a/2 + 2(χ/2)(2y))», 18 characters), p. 27 («c_4 − c_3»), p. 12 («Dist_A · (v ⊗ b_0)»), p. 17 and p. 18 (intervals broken inside, 3), p. 29 («(2^n − 2m_1(n) − 4m_2(n))/4»), p. 35 («G_0 = G, G_1, …, G_k»), p. 43 (exact sequence) | 10 |
| PD20 | m | Breaks after «=», «≤», «:=», «+», «−» inside formulas of 10–25 characters (TeX allows them; their number does not) | p. 11 (1), p. 15 (1), p. 19 (2), p. 21 (4), p. 24 (3), p. 28 (4), p. 30 (2), p. 31 (7), p. 32 (4), p. 33 (2), p. 37 (2), p. 39 (2), p. 40 (5) | 39 |
| PD21 | M | Hyphenation inside a hyphenated compound, or at a wrong point | p. 11 («Dist_A-mod-ules»), p. 32 («Dist_A-lat-tices»), p. 13 («spa-ces») | 3 |
| PD22 | m | Citation broken inside (allowed by rule (45), denied by App. A) | p. 6 ([Bai03, Lemma 2.2, / Corollary 2.3]), p. 42 ([GMMY24, / Proposition 1.9]) | 2 |
| PD23 | m | Number, initial or «No.» cut from its word | p. 2 («version / 5»), p. 45 («777 240 / non-zero shifts»), p. 43 («48 006 / house-checks»), p. 50 («N. / Terekhov», «Paper No. / e11», «Mathematics / 9», «Pure Math. / 9») | 7 |
| PD24 | m | A word alone on a line before a display | p. 36 («of») | 1 |

## D. Loose lines

| id | sev | kind | instances | n |
|---|---|---|---|---|
| PD25 | M | Lines whose stretched word space is ≥ 1.6× the median (3.48 pt), visible on the page | 57 lines by scratch/loose.py (logs/loose_v5c.log), less 2 false positives (p. 11 script fragments, p. 9 a table row) = 55; of these 10 real lines ≥ 2× (pp. 4, 6, 11, 12, 26 ×3, 31 ×2, 34) and one at 1.99× (p. 49), the worst 9.1 pt (p. 26). None of the ≥ 2× lines carries a matrix. | 55 |

## E. Page-level judgements

| id | sev | kind | instances | n |
|---|---|---|---|---|
| PD26 | m | Title page holding only the abstract (63 %); p. 5 at 89 % (declared by the author) | pp. 1, 5 | 2 |
| PD27 | m | Table design: a narrow column of eleven 2-word lines (p. 46); a labelled matrix as a cramped ruled table (p. 19); a rule between every table row (not booktabs; pp. 2, 7–9, 43–47) | pp. 19, 46 (+ style) | 2 |
| PD28 | m | Production: every STIX font is embedded as Type 3 (only Menlo is CID TrueType); some journal production systems reject Type 3 fonts | whole file | 1 |

## Totals

Kinds: 28 (S: 1, M: 11, m: 16). Instances: 2 + 3 + 2 + 2 + 1 + 1 + 2 + 1 + 7 + 1 + 3 + 2 + 3 + 3 + 6 + 3 + 4 + 4 + 10 + 39 + 3 + 2 + 7 + 1 + 55 + 2 + 2 + 1 = 172.

Not counted as defects (record issues, in REPORT §1): 39 sentences of the running text begin with a formula although App. A says none does (only statements after a bold label are excepted); the break at «=» in Lemma 2.4 (p. 12) that CORRECTIONS lists as left and App. A does not.
