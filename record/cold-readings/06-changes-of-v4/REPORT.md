# REPORT_COLD_6 — cold reading 6 of the changes of version 4 of «The Dancing Sand Theorem», and of its pdf

Reader: «Grepy el lector frío del cubo 6». Started 2026-10-05 21:21:24 CEST.

## 0. First lines

- **Do the changes of the text hold as written: HOLDS WITH GAPS.** The mathematics of every change holds: no symbol, number, quantifier or hypothesis of any numbered statement changed (item 1; my own normalizing comparison, §2), and the new sentences on strictness (item 3), on the cleanliness of the moves (item 4) and on «the rounding never acts» (item 6) are right. No gap and no error in the mathematics; the Stop rule was not triggered. What does not hold as written is the record: one row of §12.2 is arithmetically false («the 7 634 cells with `i ≥ 1` … (7 874 less the 240 with `i = 0`)»: in that range 254 cells have `i = 0` and 7 620 have `i ≥ 1`; item 8, ERROR of the record), and Appendix A still calls version 3 «(this text)» (item 7); further sentences of §1.0, §13, Appendix A and §12 are inexact, and «Why dance» drops a sign (items 5, 7, 8).
- **Is the pdf perfect: NO** — **32 global defects** (GD1–GD32, `checks/PDF_DEFECTS.md`) and **64 page-specific ones** (`checks/PAGES.md`). The gravest: barred and hatted letters are unreadable (`X̄(λ, i) ≅ 2X(λ, i)` reads «X ≅ 2X», `N̄ := N ⊗ F_2` reads «N := N ⊗ F_2», `d̂_r` reads «đ_r»); **no page numbers**; stray bold words in statements; the n-ary `⊕` of the new display of Proposition 10.3 set as the binary sign; «=:» split; matrices written as lists `[[X, 0], …]`; breaks inside short bracket groups and one formula split across a page; visibly loose lines (word spaces up to twice the median).
- **Is version 4 ready for publication: AFTER CORRECTIONS** — of the record (two false sentences, several inexact ones) and of the typesetting; no correction of the mathematics is needed.

## 1. The changes of the text (§2, item by item)

### Part 1 — first pass (written 2026-10-05, before Part 2)

The diff `DIFF_v3_to_v4.txt` is exactly `diff -u` of the two md files given (regenerated here: `logs/regen_diff.log`, IDENTICAL_BODY, 381 lines; sealed S-1, hit). It has 29 hunks:

| # | v3 line | where | kind |
|---|---|---|---|
| H1 | 3 | title block | «version 3» → «version 4» |
| H2 | 29–41 | §1.0 reading record; §1.1 | record rewritten; [GMM19] → [MGM19] |
| H3 | 51–57 | §1.2 Multiplicities (unnumbered definition) | sentence → display |
| H4 | 59–65 | §1.2 Pooling | citation of «the rounding never acts» widened |
| H5 | 121–127 | **Corollary 1.6 (statement)** | citation key [GMM19] → [MGM19] only |
| H6 | 130–136 | §1.5 item 1 | change of variables «up to the sign» |
| H7 | 191–197 | §1.7 «Why dance» | sentence on payments rewritten |
| H8 | 200–210 | §1.8 | two keys renamed |
| H9 | 218–224 | **Lemma 2.1 (statement)** | sentence → display, «In `R`,» added |
| H10 | 277–283 | proof of Proposition 3.1(b) | parenthesis reworded |
| H11 | 362–368 | proof of Proposition 4.1 | display split in two lines |
| H12 | 375–381 | proof of Proposition 4.2 | display split in two lines |
| H13 | 475–484 | proof of Proposition 5.3, steps 1 and 3 | sentences → displays |
| H14 | 486–492 | proof of Proposition 5.4 | sentence → display |
| H15 | 659–665 | paragraph after the proof of Lemma 7.9 | new sentences on strictness |
| H16 | 683–689 | proof of Lemma 9.1 | «numbers ≥ 2» → «numbers that are all ≥ 2» |
| H17 | 737–748 | **Lemma 9.7 (statement)**; proof of Corollary 1.6, item 1 | display; «every dancer is» added |
| H18 | 786–792 | proof of Proposition 10.3 | sentence → display |
| H19 | 849–855 | proof of Lemma 10.6(a) | new sentences: the moves are clean |
| H20 | 920–926 | proof of the lemma on `𝒦` (a) | run-in heads «Products», «Shifts», «Inverses» |
| H21 | 946–952 | Remark (2) after Theorem 10.15 | citation «Lemma 10.6(a), with Propositions 4.1 and 4.2» |
| H22 | 986–998 | proofs of Lemma 10.20 and Corollary 10.21 | displays split / sentence → display |
| H23 | 1004–1010 | proof of Theorem 10.22 | «Lemmas 10.18–10.19» → «Lemmas 10.18 and 10.19» |
| H24 | 1033–1062 | §12.1 table; §12.2 header | code column merged; ranges; «Four» → «Five readers» |
| H25 | 1072–1080 | §12.2 rows | reader 4 row 7 634; two rows of reader 5 added; «·» → «;» |
| H26 | 1085–1094 | §13 | status rewritten |
| H27 | 1112–1119 | Appendix A | versions 2, 3, 4 paragraphs |
| H28 | 1125–1137 | References | [DEGJPP24] → [DEGJPP23]; [GMM19] removed; [GMMY24] shortened |
| H29 | 1141–1151 | References | [MGM19] added in order; [OEIS] access date; [Yue24] «31(1)» → «31» |

Three hunks touch a numbered statement (H5, H9, H17); thirteen touch a proof (H10–H14, H16–H20, H22, H23). Graded in item 1 below.


### Item 1 — no mathematical statement changed: HOLDS

Every hunk was located (table above) and compared with `scratch/normcmp.py` (item 2). The three hunks inside a numbered statement:
- H5, Corollary 1.6: only the key `[GMM19]` → `[MGM19]`. No change.
- H9, Lemma 2.1: the sentence became a display, «and» became the spacing of the display, and «In `R`,» was added. `R := Z[G]`, `G = (Z/2)^n`, is defined three lines above (v4 line 219). No change of symbol, number, quantifier or hypothesis.
- H17, Lemma 9.7: the last formula became a display; the normalized text is identical (the only word difference in H17 is in the proof of Corollary 1.6, below).

The proof steps touched: H11, H12, H14, H18, H22 are identical after normalization; H13 («and» → «,» between two formulas of one display in Proposition 5.3, step 1); H10 (Proposition 3.1(b): «(the last one gives `2(s+1)/(2s+1)!!`)» → «(`2(s+1)/(2s+1)!!` for the last one)»; I re-derived the value: `2^{s+1}/(2^s s!(2s+1)!!)·E^{s+1} = (2(s+1)/(2s+1)!!)·E^{(s+1)}`); H16 (Lemma 9.1: «numbers ≥ 2» → «numbers that are all ≥ 2»); H20 (the run-in heads «Products», «Shifts», «Inverses» of the lemma on `𝒦`; content identical); H23 («Lemmas 10.18–10.19» → «Lemmas 10.18 and 10.19»); H19 (item 4); H21 (Remark (2), citation only).

**The three words «every dancer is» (H17, proof of Corollary 1.6, item 1, v4 line 758): HOLDS.** Proposition 9.6 bounds every big clock of every family at a shift `i ≥ 1` by `g(n − i + 1)`; for `i ≥ 2`, `n − i + 1 ≤ n − 1` and `g` is non-decreasing, so every big clock at a shift `i ≥ 2` is `≤ G = g(n − 1)`. «Every dancer is ≤ …» names a dancer for its pooled big clock, as the same item already does twice («every other dancer is ≤ …», «The dancer `{t_1}` is at `V_0`»). The words make the sentence grammatical and remove the line that began with «≤»; they add nothing false. Optional: «every big clock is», the wording of Proposition 9.6.

### Item 2 — the presentation edits must not change content

See §2 below (the normalizing comparison).

### Item 3 — the new sentences on strictness after Lemma 7.9 (H15, v4 line 674): HOLDS, with one PRESENTATION point

I re-derived each claim against the proofs (v4 lines 637–679, 745).
- «Strictness is not used in this proof: a cut is enough.» Lemma 7.9 uses Lemma 7.2(b) only for real fits (first sentence of 7.2(b), which needs cuts), Lemma 7.3, and for the deletion the definition of a cut (fit = concatenation). HOLDS.
- «As written, strictness is also used in Theorem 7.8 (steps 1 and 3) and in Theorem 7.10, to identify integer fits.» Step 1 (line 639): «These are strict cuts … its integer fit is `X_1`» — the integer part of 7.2(b). Step 3(c) (line 645): «its integer fit is `X_2 = ŷ' + d_2`» and «Lemma 7.2(b), `b'` being a strict cut». Theorem 7.10, `i ≥ 1` (line 678, (U2)) and `i = 0` (line 679, «so `∅` is a level set by itself, and the fit and the integer fit of `x^♯` … are those of `x_{H^♯}` restricted»). All four uses are to identify integer fits. HOLDS.
- «With Lemma 7.9 a cut suffices there (in Theorem 7.8 by a joint induction with Lemma 7.9, which uses the (Cut) of Theorem 7.8).» I checked the joint induction on `|I|`: at level `|I|`, Lemma 7.9 for `H'` makes `fit(x_{H'})` integral, so the real fit `fit(x_{H'}) + d_1` (a cut suffices) is integral and equals its integer fit `ŷ' + d_1`; Theorem 7.8 for `H` (with (Cut) proved, strict or not) follows; then Lemma 7.9 for `H` uses (Cut) for `H'` (first half) and for `H` (penalty shift, deletion). No circularity. In Theorem 7.10 the integer fit of the cell is its real fit `fit(x_H) + shift` (cut suffices) once 7.9 holds. HOLDS.
- «It is indispensable only in Proposition 9.6 (H), twice: in the induction for the base cell, and for the penalty shift.» (H) is about the level sets of the real fit, which integrality does not control; a jump of `d_1` (base cell, through step 1, «with the level sets of `fit(x_{H'})`») or of the penalty shift at a non-strict cut inside the head would split it. Both uses are real. Props 9.3 and 9.4 use step 1 of Theorem 7.8 only for values (9.3: `J ≡ 0`, `d_1` constant; 9.4: covered by «with Lemma 7.9 a cut suffices»). HOLDS.
- **PRESENTATION (P-T1).** The proof of Proposition 9.6 (H) (v4 line 745, unchanged) says «this is where strictness is needed» at the penalty shift only; its base-cell sentence («this follows by induction along step 1 of the proof of Theorem 7.8») does not say that it needs the level sets of step 1, hence strictness. The new sentence of §7.5 says «twice»; (H) names one. Fix: in (H), after «along step 1 of the proof of Theorem 7.8», add «, which keeps the level sets of the child because `d_1` changes only at strict cuts (Lemma 7.2(b))».

### Item 4 — the new sentences in the proof of Lemma 10.6(a) (H19, v4 line 867): HOLDS, with one PRESENTATION point

Clean (§10.3, line 863) means: `P` invertible and `S ≡ 0 (mod 2)`.
- Twist: for `G = F + π(D) + K(D)` the pivot `P = G^{10}` is the identity (only `F` has odd degree; `x^{10}` of `F` is `1`), and `S/2 = G'` is computed in the proof; `G'` is integral, so `S ≡ 0 (mod 2)`, and even (Proposition 4.1: halves of products of two elements of `2A`), so the next move has the same hypothesis. HOLDS.
- Split: I checked that the pivot block of the §10.3 split move (coordinates `b_0 ⊗ b_1 n`, `Dd_n`; sources `A_n`, `C_n`) is that of Proposition 4.2 (the change of basis `B_n = b_0 ⊗ b_1 n − C_n` leaves the `B`-coordinate and all sources unchanged) and equals the identity on every slot (the couplings, of degree 0, never reach a `b_1`-coordinate from a `b_0`-source); «triangular, with the coefficient 1 on each eliminated vector» is true (a fortiori). The Schur complement is unchanged by the row/column operations, and Proposition 4.2 computes it as `2G''` with `G''` even. HOLDS.
- **PRESENTATION (P-T2).** Cleanliness is now proved inside the proof of (a), but the statement of (a) (unchanged) does not mention it, while Remark (2) of §10.5 (H21) now cites «Lemma 10.6(a), with Propositions 4.1 and 4.2» for «every even payment system dances clean». A reader who reads statements only will not find the claim. Not a mathematical change; optionally add to the remark «(proof of Lemma 10.6(a))».

### Item 5 — «Why dance» (H7, v4 line 196): PRESENTATION

«At the start each floor `d` pays the even amount `2^α(i + d)`; each move multiplies the payments of two adjacent floors and halves them, so every payment stays even.»
- Exact for the diagonal payments up to sign: Proposition 4.1 gives `π'_s(f) = −π_s(2f)π_s(2f + 1)/2`, Proposition 4.2 `π''_{(s,A)} = −π_s(2f)π_s(2f+1)/2`, `π''_{(s,C)} = −π_s(2f+1)π_s(2f+2)/2`. The sign is dropped, and «halves them» reads as halving each payment (that would be `/4`); it is the product that is halved.
- Not exact for every move if «payment» has the meaning of §4.1 («the couplings `K_{ss'}` are payments», v4 line 358): the split move creates the couplings `K''_{(s',C),(s',A)}(f) = −π_{s'}(2f + 1)` and `K''_{(u,C),(s',A)}(f) = −K_{us'}(2f + 1)`, single payments, neither multiplied nor halved. With the narrower meaning of §1.7 («a diagonal operator given by a function of the floor») the sentence is exact up to sign.
- «so every payment stays even» is true for all of them (Propositions 4.1, 4.2).
- Fix: «each move replaces the payments of two adjacent floors by minus half their product, so every payment stays even».

### Item 6 — §1.2 «the rounding never acts» and the change of variables (H4, H6): HOLDS, with one PRESENTATION point

- §1.2 (v4 line 64): «(Lemma 7.9, with Proposition 5.3, Lemma 7.5 and Proposition 5.4; see §8)». Chain: for `i ≥ 1`, Prop. 5.3 gives `u_i(D) = k + K + κ(m, K) + x_D`; by Lemma 7.5 `x` is the clock sequence of `Cell(H; r_k(m), r_k(m + K))`; Lemma 7.9 makes its real fit integral; adding a constant keeps it. For `i = 0`, Prop. 5.4 gives `u_0(D) = k + K + x^♯_D` and `x^♯` is `x_{H^♯}` with its first dancer deleted, `H^♯ = (I, k, K − 1, 1)` — the third clause of Lemma 7.9. For `I = ∅` one entry. The block means of PAVA are the values of the real fit. The citation is complete. HOLDS.
- §1.5 item 1 (the mission says «§1.4 item 1»; the sentence is in §1.5, item 1 of «The idea of the proof»): `material/sources/GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt` lines 376–377: «Apply the change of variables ui := xi − 1 to the presentation in Proposition 1.11» — inside the proof of Proposition 2.5 (the same change is used again in the proof of Theorem 2.8, line 482). `∏_{i∈S}(x_i − 1) = (−1)^{|S|} ∏_{i∈S}(1 − x_i) = (−1)^{|S|} s_S`: the sign is exact. HOLDS. (GMMY work after tensoring with `Z/2`, where the sign disappears; the paper's wording is still right over `Z`.)
- **PRESENTATION (P-T3).** §1.8 (v4 line 209, unchanged) still says «their change of variables `u_i = x_i − 1` is the basis we use [GMMY24]», without «up to sign» and without the place; and both sentences call a change of variables «the basis». Fix in §1.8: «the monomials of their change of variables `u_i = x_i − 1` (proof of Proposition 2.5) are, up to the sign `(−1)^{|S|}`, the basis we use».

### Item 7 — the reading record (§1.0, §13, Appendix A): PRESENTATION, one false sentence

- **P-R1 (false sentence, must be fixed).** Appendix A, v4 line 1140: «**Version 3** (this text) states that integrality as Lemma 7.9, …». In version 4 the text is version 4, and the next bullet (line 1141) says «**Version 4** (this text)». The v3 paragraph was rewritten in v4 (H27) and kept «(this text)». Fix: delete «(this text)» in the version 3 bullet.
- **P-R2.** Appendix A, version 3 bullet: «Every number printed in it was checked against an engine (§12).» The same bullet then says that the fifth reader found «three ranges of §12» to correct (one was `λ ≤ 127` where the code ran `λ ≤ 126`). The two sentences, side by side in a paragraph rewritten in v4, contradict each other. Fix: «Every number printed in it was checked against an engine (§12), but three ranges were printed wider or vaguer than the code: …».
- **P-R3.** Appendix A, version 4 bullet: «No mathematical statement changed, and no number, except the ranges of §12 that the fifth reader checked against the code.» True of changes, but silent on what was added: two new rows of §12.2 (the fifth reader's, thirteen new numbers), the new description of the 7 634 cells (which is wrong, item 8), and «Four» → «Five readers». Fix: add «; §12.2 gains the two rows of the fifth reader».
- **P-R4.** §1.0 (line 32): «It found one gap, in the proof of Lemma 7.2(b).» Appendix A (line 1138): «the integer part of Lemma 7.2(b) is false as stated». A false statement is not a gap in its proof; the gap was in the four proofs that used it. Fix: «It found one gap: the integer part of Lemma 7.2(b) was false as stated, and four proofs used it; no theorem was affected.» (Unchanged sentence in a rewritten paragraph.)
- **P-R5.** §1.0: «it also found that every fit used in the proofs is integral (Lemma 7.9)»; Appendix A (version 2 bullet): «It also found that the fit of every house is integral»; §13: «Lemma 7.9 in its new form …, found and proved by the fourth reader». Three different extents for one finding (every fit used / every house / the strengthened lemma, proved). One wording should be used in all three places.
- **P-R6 (record of the author, not of the paper).** §13 lists the *statements* changed in version 3 (Lemma 7.9, Lemma 10.6(a), Lemma 10.10). `CORRECTIONS_v3_to_v4.md` §5 says that the rewording of Lemma 3.5 made in version 3 «is listed in §13 of version 4»; it is not — and rightly not: that rewording was in the *proof* of Lemma 3.5 («`C(3, r) = 1, 3, 3, 1`» → «`1, 3, 3, 1` (that is, `C(3, r)`)», REPORT_COLD_5 §3, read in Part 4). §13 is exact; `CORRECTIONS` §5 is wrong. In the same file, line 22: «(items 7, 8 and 11 below)» — §1 of `CORRECTIONS` has items 1–10 only.
- **P-R7 (added in Part 4).** Appendix A, version 4 bullet: «… except the ranges of §12 that the fifth reader checked against the code». The new parenthesis of reader 4's Lemma 7.9 row («7 874 less the 240 with `i = 0`») was not checked by the fifth reader, who wrote that the 7 634 cells were «not checkable from the paper» (REPORT_COLD_5 §1.10, point 3): the author composed it, and it is wrong (item 8).
- Checked and exact: «The changes of version 4 have not yet been read cold» (§1.0, §13 last bullets, Appendix A); §13 «Changed in version 4, audited, not yet read cold»; the attribution of the missing «even» in Lemma 10.6(a) to the author (§1.0 and Appendix A agree); «Five readers» (§12.2) against the five cold readers of Appendix A; the dates; «The work took four days, from 2 to 5 October 2026».
- **P-R8 (added in Part 4).** §1.0: the fifth reader «found points of presentation and defects of typesetting, all corrected in this version 4». Against `REPORT_COLD_5.md` §4 (§6.1 of this report): of its 8 global and 28 specific defects, 33 are fixed, row 25 only partly, and rows 1 (the blank of p. 7) and 20 (the broken definition of `R_𝒮`) are not; two of its minor notes remain (a sentence opening with a formula; `b_0 ⊗ / b_1 n`). «All corrected» is not exact; «corrected, except …» would be.

### Item 8 — §12.1 and §12.2, the changed rows: one ERROR of the record (reader 4's Lemma 7.9 row), three PRESENTATION points

Own recount: `scratch/cells.py` (exact integers and fractions; definitions as printed in §1.2, §5, Prop. 5.4, §7.3), `logs/cells.log` (VIGIA-FIN-OK); sealed S-3 to S-7, all hits.

- **§12.1, Propositions 5.2 · 5.3 · 5.4: HOLDS, one PRESENTATION point.** The counts fit the new ranges exactly: `Σ_{λ=1}^{63} 3^{|I|} = 1 365`, `× 40 × 2 = 109 200` (pairs `b ⊆ a`, `i = 1…40`, `α = 1, 2`); `Σ 2^{|I|} = 364`, `× 40 = 14 560`; `Σ (2^{|I|} − 1) = 301` at `i = 0`. **P-C1:** the 301 «entries» of 5.4 are dancers `D ≠ ∅`, so the check covers the clock identity `u_0(D) = k + K + x^♯_D` of Prop. 5.4, not its valuation formula for the entries of `M(λ, 0)` (which would be `Σ (3^{|I|} − 1) = 1 302` entries). The row names «Proposition 5.4» whole. (Confirmed in Part 4: `gate_sections5to7.py` lines 154–158 test only `u_0(D) = k + K + R^♯(D) − R^♯(I ∖ D)` for `D ≠ ∅`; the valuation loop runs for `i ≥ 1` only. Sealed S-18, hit.) Also «entries» means matrix entries for 5.2 and clocks for 5.3–5.4.
- **§12.1, Theorem 7.8, `λ ≤ 126`: HOLDS.** Houses with `I ≠ ∅` and `k ≤ 6` are those with `λ + 1 ≤ 127`; `λ = 126` (`127 = 64 + 63`) is the largest. `16 002 = 3·Σ_{k=1}^{6}(2^k − 1)2^k` (every `ℓ < 2^k`, `α ≤ 3`) and `48 006 = 3 × 16 002`: consistent.
- **§12.2, Lemma 7.9, reader 4: ERROR (of the record; no mathematical consequence).** «the 7 634 cells with `i ≥ 1` of the row above (7 874 less the 240 with `i = 0`)». The row above is `λ ≤ 127`, `i ≤ 30`, `α = 1, 2`: `127 × 31 × 2 = 7 874` cells (my count; the pooling counts 1 876 and 1 834 of readers 3 and 4 are reproduced exactly by the same cell set, S-4). Of these, **254** have `i = 0`, not 240; **7 620** have `i ≥ 1`, not 7 634. The 240 are the cells with `i = 0` and `I ≠ ∅` (`120 × 2`). So the 7 634 cells are the 7 620 with `i ≥ 1` plus the 14 with `i = 0` and `I = ∅` (where `M = 0` and there is nothing to pool). The sentence added in v4 to make this row exact is false. Fix: «the 7 634 cells of the row above other than the 240 with `i = 0` and `I ≠ ∅`» — or, better, state what reader 4 actually checked, which this text cannot know (the reader's log is not given).
- **§12.2, the first row of reader 5: HOLDS on its numbers, PRESENTATION on its words.** `65 532 = 3·Σ_{k=1}^{7} 4^k` and `741 = 3·Σ_{k=1}^{7}(2^k − 1)` are the houses and the deletions; the control 1 942 of 16 380 is reproduced exactly by my code (S-7). **P-C2:** «penalties `P_r, P_c ≤ 4` for `k ≤ 6` (192 024 cells)»: `192 024 = 8 001 × 24`, the non-zero penalty pairs on the 8 001 houses with a boundary only (§12.1 says so: «24 on each house with a boundary»); here it reads as all penalty cells with `k ≤ 6` (`16 380 × 24 = 393 120`). Fix: «on the 8 001 houses with `k ≤ 6` that have a boundary (192 024 cells)». The control «strictness one dancer after the boundary fails in 7 967 of 30 078» repeats reader 4's numbers digit for digit; not reproduced here (its definition is not printed); checked against the log in §6.
- **§12.2, the second row of reader 5: HOLDS on its numbers, PRESENTATION on its words.** `10 455 = 255 × 41`, `10 200 = 255 × 40`; my code finds 0 non-integral block means in the 10 455 cells (S-6) and the identities of Props. 5.3 and 5.4 in all of them, and reproduces the control 2 316 of 9 880 exactly (S-5). **P-C3:** «of 9 880 cells» is not explained: they are the cells with `I ≠ ∅` and `i ≥ 1` (`247 × 40`). The control tests integrality only; (H) and Lemma 7.5 have no control — the row should say so («control: for the integrality»).
- **§12.1 conventions (PRESENTATION, minor).** The header defines «none» for a row without control; the row of Remark (2) has «—». §12.2 uses «—» and «fires» without definition.
- Numbers of the fifth reader's rows against its log: §6 below.

### Item 9 — the references: HOLDS

`scratch/refs.py` (own code; control with a fake key `[Zzz99]` fires): 32 keys listed, 32 cited, none uncited, none unlisted, alphabetical (case-insensitive), no occurrence of `[GMM19]` or `[DEGJPP24]` left; `[MGM19]` cited 3 times (§1.1, Corollary 1.6, §1.8 item 3), `[DEGJPP23]` once (§1.8). Against the sources: the poster lists «Jared Marx-Kuo, Jiyang Gao, and Vaughan McDonald, Joint Mathematics Meetings, January 16-19, 2019, Baltimore, MD» and conjectures `c_{n+1}(Q_n) = max_{x<n−1}{v_2(x) + x}` for `n ≥ 4`, which is `g(n − 1)`: the key, its order and its use in Corollary 1.6 are right. `arXiv:2310.09227` is from October 2023 (the copy given is v2, 18 Nov 2024); «(2023)» is the year of v1 — acceptable. The journal data of [GMMY24] and [Yue24] are not in the sources given; not checked.
- **PRESENTATION (minor, unchanged text).** «their 2019 poster» (§1.0 table, §1.1): «their» is Gao, Marx-Kuo, McDonald and Yuen; the poster is by three of them. Fix: «the 2019 poster of Marx-Kuo, Gao and McDonald».

## 2. The presentation edits: content unchanged? (§2 items 1–2, with your comparison)

**Verdict: HOLDS.** Every presentation edit keeps the mathematics; the only word changes inside statements and proofs are the ones listed in item 1, and none changes a symbol, a number, a quantifier or a hypothesis.

**How the comparison works** (`scratch/normcmp.py`, log `logs/normcmp.log`, VIGIA-FIN-OK). It parses the unified diff into its 29 hunks; for each hunk OLD = context + «−» lines and NEW = context + «+» lines. Normalization N1 deletes every backtick and every whitespace character (spaces, tabs, line breaks) and compares the two strings: equal means the hunk changes only line breaks, spaces and the backticks of the md. For a hunk that is not equal, it prints a word-level diff (tokens = the whitespace-separated words after deleting backticks, `difflib` opcodes, 4 words of context), so that every changed word is read by a person. N1 is deliberately strict: it does not forgive a comma for an «and», nor a run-in head.

**Control that can fail** (`logs/normcmp_control.log`): the script changes one character (`2f+1` → `2f+2`) inside the second line of the hand-split display of H11; H11 then reports CHANGED and the count of layout-only hunks drops from 5 to 4. It fired.

**Result** (sealed S-2 before the run, hit): exactly five hunks are identical under N1 — H11 and H12 (the displays of the proofs of Propositions 4.1 and 4.2 split by hand into two lines), H14 (Proposition 5.4), H18 (Proposition 10.3), H22 (Lemma 10.20 split into two lines, Corollary 10.21 made a display). The other statement/proof hunks differ only in these words:

| hunk | where | words changed (old → new) | mathematics |
|---|---|---|---|
| H3 | §1.2, definition of `m_λ(n)` | «and» → «,» (two formulas of one display) | same |
| H5 | Corollary 1.6 | `[GMM19]` → `[MGM19]` | same |
| H9 | Lemma 2.1 | + «In `R`,»; «and» deleted | same |
| H10 | proof of Prop. 3.1(b) | parenthesis reworded | same (value re-derived) |
| H13 | proof of Prop. 5.3, step 1 | «and» → «,» | same |
| H16 | proof of Lemma 9.1 | + «that are all» | same |
| H17 | proof of Corollary 1.6, item 1 | + «every dancer is» | same (judged in item 1) |
| H20 | proof of the lemma on `𝒦`, (a) | «Products:» → «*Products.*», idem «Shifts», «Inverses» | same |
| H21 | Remark (2) of §10.5 | «(Proposition 4.1, Lemma 10.6(a))» → «(Lemma 10.6(a), with Propositions 4.1 and 4.2)» | same claim |
| H23 | proof of Theorem 10.22 | «10.18–10.19» → «10.18 and 10.19» | same |

The split displays (H11, H12, H22) start their continuation line with the binary operator or the relation (`− Σ…`, `− 2π…`, `= δ(…)`): that is the TeX convention for a broken display, and the pieces concatenate to the old formula character for character. How the pdf sets them is graded in §4.

**One presentation point of the md, found by the comparison (H20).** The proof of the lemma on `𝒦` (v4 lines 938–941) now sets «*Products.*», «*Shifts.*», «*Inverses.*» as run-in heads on their own lines inside part (a), but parts (b) and (c) continue on the «*Inverses.*» line («… `(−2χ/a)^j`. (b) The product rule …»), so (b) looks like a sub-item of «Inverses». Fix: start «(b)» and «(c)» on lines of their own, as (a) is. (Checked on the page in §3.)

## 3. The pdf, page by page (summary; the full list is `checks/PAGES.md`)

**All 49 pages were looked at, in order**, at 90 dpi (`scratch/p90/`), with 200–600 dpi crops of every doubtful region (`scratch/p200/`, about 90 crops). Every page has a line in `checks/PAGES.md`; the global defects are numbered GD1–GD32 in `checks/PDF_DEFECTS.md`.

**Verdict: the pdf is not perfect.** No page is free of defects a typesetter of a top journal would mark: every page lacks a page number (GD32) and carries instances of the global defects (straight apostrophes GD1, italic number sets GD2, the end-of-proof mark GD12, …); only p. 8, p. 9 and p. 24 have nothing beyond instances of the global defects.

The defects that a reader of the mathematics would trip over (in order of weight):
1. **GD3 — misplaced accents make symbols unreadable.** The bar of `K̄`, `X̄`, `N̄`, `L̄` and the hat of `d̂` (58 occurrences, `logs/accents.log`) sit on the left stem or the ascender of the italic letter. At reading size the fold law reads «X(2l + 1, j) ≅ 2X(2l + 1, j)» (Corollary 10.17, p. 39), «If X(λ, i) ≅ 2X(λ, i)» (Proposition 10.3, p. 32), «(N := N ⊗ F_2)» (p. 14), «Let L be the Laplacian of the folded cube» (p. 41), and `d̂_r` reads «đ_r» (p. 21–22).
2. **GD11 — bold statements with light formulas** leave stray bold words: «**for**» in Corollary 1.6 (p. 6), «**if**» in Theorem 4.4 (p. 17), «**with** … **entrywise**» (Theorem 10.12), «**at every level**» (Lemmas 10.18, 10.19).
3. **GD25 — the new display of the proof of Proposition 10.3 (H18)** sets the n-ary direct sum «⊕(2X)^{m_λ}» as the small binary sign (p. 32).
4. **GD26 — matrices written as lists** «[[X, 0], [(Y − X)/2, Y]]» (12 places, §10) and the code «column 1 += column 2».
5. **GD28 — «=:» split into «= :»** (Lemma 4.5, p. 18; proof of Theorem 10.15, p. 38); **GD19** a binary «+» without spaces (p. 22); **GD20/GD21** words and letters run together or isolated in displays and scripts (p. 19, p. 23).
6. **Breaks the mission forbids:** inside short bracket groups (p. 12 twice, p. 20, p. 36, p. 37, p. 44 twice), a formula split across a page (p. 30/31, GD24), a citation key hyphenated (p. 22, GD18), a citation split inside its brackets (p. 44), hyphenation inside a hyphenated compound (p. 1, p. 35, GD5), two-letter hyphenation (p. 13, p. 27, GD13).
7. **Display style not complete:** `max`, `min`, `mean` with limits at the side in displays (p. 26, 29, 30; GD23); text-size delimiters around display-size sums (p. 15, 16, 29, 40; GD16); conditions at one word space after displays (GD15).
8. **Loose lines** visible at 90 dpi on about 20 pages (listed per page); runt last lines (`I).`, `2A. ∎`, `a_n. ∎`, `and so is μ. ∎`, `at 0. ∎`); single letters alone in table cells (`h`, p. 7; `b`, p. 46); numbers cut from their nouns in the §12 tables (GD29).
9. **Count.** 64 page-specific defects: one per lettered item of `checks/PAGES.md` that is not just an instance of a global defect (each loose line counted once).
10. **Short pages:** p. 7 and p. 42 (accepted by the author) — I would not accept either as a typesetter (both fixable by letting a table start on the page, as the §12 tables already do); and pages the author's table does not list — see page fill in §5.

## 4. The setting of the mathematics (§3 items 2–3)

**Verdict: much better than version 3, not yet TeX quality.** The main promise of version 4 is kept: letters are italic; digits, brackets and operator names (`max`, `min`, `coker`, `Syl`, `dim`, `mod`, `exp`, `tanh`, `rank`, `Hom`, `Ext`, `Dist`, `next`, `sat`, `glue`, `Cell`, `out`, `in`, `mult`, `ch`, `Ch`, `Sh`, `diag`, `GL`, `Mat`, `ker`) are upright; scripts are stacked at the right height, third-level scripts (`2^{2^t}`, `2^{1−2^{h+1}}`) are legible; the spacing of relations, binary operators and punctuation is fixed and right almost everywhere; `Σ`, `∏`, `⊕` in displays carry their limits under; the hand-split displays (H11, H12, H22) follow TeX's `multline` (first line at the left gap, continuation flush right, the operator opening the continuation). `𝟙`, `𝒦`, `𝒮`, `𝒯`, `𝒜`, `𝔅`, `𝔡`, `𝔞`, `ℓ`, `ℎ` are the right glyphs. What a TeX user would still mark (details and places in `checks/PDF_DEFECTS.md` and `checks/PAGES.md`):

| item of the mission | finding | defects |
|---|---|---|
| letters italic, operators upright | number sets `Z`, `Z_2`, `Q`, `Q_2`, `F_2` italic, where TeX uses ℤ, ℤ₂, ℚ₂, 𝔽₂ — and italic `F_2` collides with the operator `F`; math in headings set as text (`SL₂`, `F₂` with Unicode subscripts, upright `M`); the two-letter block name `Dd` | GD2, GD14 |
| accents | combining bars and hats (58: `K̄`, `X̄`, `N̄`, `L̄`, `d̂`, `χ̄`, `b̄`, …) sit on the left stem or the ascender; `X̄(λ, i) ≅ 2X(λ, i)` reads as `X ≅ 2X`, `N̄ := N ⊗ F_2` as `N := N ⊗ F_2`, `d̂_r` as `đ_r` | GD3 (most serious) |
| spaces | «=:» printed «= :» (twice); a binary «+» with no spaces (`‖z − y‖^2+2Σ`); no space after commas and operator names in scripts (`1≤λ≤n,λ≡n`, `minΔ`, `lastL positions ofP`); conditions after displays at one word space (`… x ι_s (x ∈ N)`); a variable isolated by quads in a display with words (`of  x  is`); `x +  const` | GD28, GD19, GD9, GD21, GD15, GD20 |
| display style | `max`, `min`, `mean` with limits at the side in three displays; text-size brackets and parentheses around display-size sums and products (Prop. 4.1, its proof, Prop. 9.3, Lemma 10.20); the n-ary `⊕` of the new display of Prop. 10.3 (H18) set as the binary sign; solidi before full-size products; `½` | GD23, GD16, GD25, GD27, GD17 |
| multi-line displays | `multline` right (H11, H12, H22); two-column displays centred line by line, columns not aligned (p. 12, p. 25); Theorem 4.4 runs its two cases into one line instead of `cases`; the tag «(K)» bold and glued to the formula (p. 11) | p. 12, 17, 25, 11 |
| ellipses and matrices | `≥ …`, `… +` on the baseline (TeX `⋯`); twelve 2 × 2 matrices written as lists `[[X, 0], [(Y − X)/2, Y]]`, and «column 1 += column 2» | GD10, GD26 |
| bold | bold statements with light formulas leave stray bold words («**for**», «**if**», «**at every level**») | GD11 |
| end-of-proof mark | a tall bar from the fallback font STIXGeneral, set one space after the text, never at the right margin | GD12 |

**Line breaking inside formulas (§3 item 3).**
- *Breaks inside short bracket groups* (the builder's own rule says never inside a group of ≤ 12 characters; a typesetter would not break these either): «(0 ≤ / r ≤ m + 1)» and «b_1(4FE + / 2w + 1)n» (p. 12), «s_2(K − 1 + / o_E)» (p. 20), «[o_X, o_Y + / K − 1]» (p. 36), «[F^{(m)} : m ≥ / 1]» (p. 37), «{1: / 6, 3: 4, …}» (p. 44), and the citation «[Lar24, / §2]» (p. 44).
- *A formula split across a page:* «if n ≡» / «3 (mod 4)» (p. 30/31, GD24).
- *Other bad splits:* «n − / 2» (p. 31), «2 · / Syl_2 K(Q_n)» (p. 42), the pure tensor «b_0 ⊗ / b_1n» (p. 16), the range «l = 2, / …, 63» (p. 39).
- *No line of running text starts with a relation or a binary operator* — `formula_lines.py` (read and run, `logs/tool_formula.log`) flags only display continuations (legitimate) and script bands; I saw none on the pages. *No exponent or index separated from its base* — none seen. *No relation with ≤ 3 characters alone at a line end* — none (the tool's one «ALONE» is a script band).
- *Runt last lines* of one short formula: «I).» (Lemma 5.1), «∇_A(1).» (Lemma 2.4), «2A. ∎», «a_n. ∎», «and so is μ. ∎», «at 0. ∎», «(Z/2^a)^{…}. ∎».

## 5. The pdf, the other checks (§3 items 4–10)

All seven tools of `material/tools/` were read before use (their limits are noted below) and run unchanged under the watchdog (`logs/tool_*.log`); my own checks are `scratch/pdfcheck.py`, `lines2.py`, `stmt_cmp.py`, `xref2.py`, `codenames.py`, each with a control that fires.

- **Item 4 — margins: HOLDS.** Measured from the body: left edge 54.5 pt (1 184 lines), right edge 542.0 pt (812 lines), first line top 55.3 pt, lowest line bottom 784.5 pt. **Largest `xMax` = 541.93 pt** (p. 41, «con‐»); no word beyond the right edge, none in the margins (`logs/pdfcheck2.log`; `margins.py` agrees, sealed S-10 hit).
- **Item 5 — loose lines: PRESENTATION.** `gaps_text_words.py` gives 10 lines above 6 pt and 0 above 7 pt (sealed S-9, hit), the author's figures. But the median word space of the 705 measured lines is **3.18 pt** (`logs/lines2.log`): 45 lines exceed 1.5 × the median and **6 lines reach twice the median** (6.4–6.9 pt; p. 14, 16, 17, 29, 33, 40). A 7 pt threshold is 2.2 × the normal space and hides lines that the eye sees: I marked visibly loose lines on about 20 pages (p. 3, 4, 5, 6, 7, 10, 17, 25, 26, 27, 30, 31, 36, 47, …). TeX's default tolerance does not allow word spaces of twice the natural width.
- **Item 6 — structure.**
  - no heading alone at the foot of a page (`structure.py`, `lines2.py`, and by eye) — HOLDS;
  - no numbered statement split across pages: `structure.py` places 64 of 68 and cannot place 4 (Props. 4.1, 4.3, Lemmas 7.1, 10.10), which I saw whole on pp. 15, 16, 22, 36; the tool does not examine the boxed statements (it reads only lines that start with «**»), and I saw all seven whole (Main Theorem p. 4; Theorem DW, Corollaries 1.4, 1.5 p. 5; 1.6, 1.7 p. 6; Theorem D p. 18) — HOLDS;
  - no table row split, cut or overflowing; the long tables of §12 repeat their header — HOLDS;
  - no widow or orphan (`widows.py`: only the chapter start of p. 2; by eye) — HOLDS;
  - no two consecutive displays separated by a page break (`lines2.py`, two false positives checked; by eye) — HOLDS;
  - but an inline formula is split across a page (p. 30/31, GD24), and **the pdf has no page numbers** (GD32);
  - **page fill** (`logs/pdfcheck2.log`): under 90 % are p. 1 (title, 61 %), p. 7 (84 %), **p. 23 (89 %)**, p. 42 (75 %), p. 49 (last, 89 %). p. 23 is not in the author's table (one line short; harmless). **p. 7 and p. 42, judged as a typesetter: not acceptable in a journal.** p. 7 leaves a sixth of a page blank inside §1, p. 42 a quarter page before §12; in both cases the next table could start on the page (the §12 tables already break row by row with their header repeated). Fix: allow the §1.7 table and the §12.1 table to begin on the short page.
- **Item 7 — glyphs and fonts.** `pdffonts` (`logs/pdffonts.log`): 114 fonts, **all embedded and subset, all with a ToUnicode map**; 112 are Type 3 (STIX Two Text, STIX Two Math, STIXGeneral), 2 are CID TrueType (Menlo, for code). No missing-glyph box on any page. **Two wrong fallbacks**: the end-of-proof mark «∎» is drawn from **STIXGeneral-Regular** (STIX 1.x) on exactly the 30 pages that carry a «∎» (`logs/pdffonts_pages.log`, `logs/qed_pages.log`) — hence the tall thin bar — and the bold «∇» of p. 11 from STIXGeneral-Bold (GD12, GD31). *Does Type 3 matter, and to whom?* Not to the printed page or to copy and search (the ToUnicode maps are present: `pdftotext` recovers the text). It matters to on-screen readers (Type 3 glyphs are not hinted, so small sizes render less crisply in many viewers), to publishers' preflight (several journal systems reject or flag Type 3 fonts), and to archiving. Since a journal will re-typeset, it matters little to the journal; it matters to every reader of the preprint, for which this pdf is the version of record.
- **Item 8 — md and pdf say the same: HOLDS (for the characters).** `md_vs_pdf.py`: the numbers of the five tables of §1 and §12 agree as multisets (the order fails only where `pdftotext` reads stacked scripts out of order); it does not check the boxed statements. My `stmt_cmp.py` compares **all 75** numbered statements of the md (boxed ones included) with the pdf as multisets of characters: no character of the md is missing from the pdf in any statement; the 5 residual differences are text of the following proof or paragraph that falls into the window (`logs/stmt_cmp2.log`; control: a «≥» changed into «>» in Lemma 9.7 is caught). The caveat is GD3: the characters are there, but the bars of `X̄`, `N̄`, `L̄` and the hat of `d̂` are not legible.
- **Item 9 — cross-references and citations: HOLDS, with one PRESENTATION point.** `xref2.py` resolves all **625** internal references (statements, their parts (a)–(d), sections, Remarks (n)); 0 unresolved; control fires. (`xrefs.py` reports 21 «MISSING TARGET», all false: it does not read boxed statements, and it counts the numbering of other papers.) Citations: 32 keys listed and cited, alphabetical (`refs.py`, item 9 of §1). I checked that the target «says what is claimed» for every reference in the changed hunks and for the «Where» columns of the tables of §1.0 and §1.7 (all right). **P-X1:** the «first use» column of the §1.6 table gives the wrong section for six symbols in three rows: `D` (the floor operator) is first used in §2.2 (md 237), not §4; `σ^{(α)}_i` in §3.4 (md 342), not §4; `q_k` and `a_k(Δ)` in §4.4 (Theorem 4.4), not §4.5; `R_μ(D)` and `x_D` in §1.2 (md 84), not §5; and `k_0 = F_2` is never used in the paper (`logs/firstuse2.log`).
- **Item 10 — file names, references, metadata.** All 12 code names print as whole words, never hyphenated (`logs/codenames.log`) — HOLDS. But a citation key is hyphenated («[ABER-/S55]», p. 22, GD18) and a citation is split inside its brackets («[Lar24, / §2]», p. 44). The reference list is set consistently in fonts and punctuation, with two inconsistencies (GD30: labels not in a column; arXiv numbers given for some journal papers and not for others). Metadata (`pdfinfo`): Title «The Dancing Sand Theorem», Subject «The 2-part of the sandpile group of the hypercube, for every n», Author «Rafael Amichis Luengo», 49 pages, A4, PDF 1.4, tagged — HOLDS; the Creator field is Chrome's user-agent string and there are no Keywords (minor).
- **Hyphenation** (own scan of the 118 line-end hyphens, `logs/pdfcheck2.log`; sealed S-15, failed — I predicted more): 8 that TeX would not make: «non-in-/creasing» (p. 1) and «lev-/el-h» (p. 35) inside hyphenated compounds; «reducibili-/ty» (p. 13), «monotonici-/ty» (p. 27), «fami-/ly» (p. 42), «list-/ed» (p. 48) with two letters carried over; «[ABER-/S55]» (p. 22) inside a citation key; «o-/order» (p. 3) a defined term broken after one letter.

## 6. After everything else (§5): the defects of reading 5, the builder, the author's checks

Opened only after §1–§5 of this report were written (`logs/DIARY.md`, «PART 4 BEGIN»). Read: `REPORT_COLD_5.md` (whole), `PAGES.md` (whole), `gate_cold5.py` (the counting loops), `gate_cold5_full.log`, `md2html_v4.py` (rules (1)–(42)), `phtml.py` (whole), `pmath.py` (its tables), `build_v4.sh`, `chrome_pdf.sh`, `pdf_meta.py`, the four author checks, and `gate_sections5to7.py` (the checks of Propositions 5.2–5.4 and Theorem 7.10).

**Two facts that change the reading of §1.** (i) The new sentences on strictness after Lemma 7.9 (item 3) and the new sentence of «Why dance» (item 5) are, nearly word for word, the fixes proposed by cold reader 5 (REPORT_COLD_5 §1.2 and §1.9). My presentation points P-T1 and item 5 therefore apply to the reader's wording as adopted. (ii) The parenthesis «(7 874 less the 240 with `i = 0`)» of reader 4's row (item 8, ERROR) is **not** from cold reader 5, who wrote only «Not checkable from the paper; worth one word of explanation (which cells)» (§1.10, point 3; sealed S-20, hit): the author composed it. So Appendix A's «no number [changed], except the ranges of §12 that the fifth reader checked against the code» is inexact for this row too: it was not checked by the fifth reader, and it is wrong.

### 6.1 The defects of reading 5 — fixed in version 4?

| defect (REPORT_COLD_5 §4) | in v4 | where (v4) |
|---|---|---|
| G1 everything italic | **fixed** (letters italic, the rest upright); new point GD2: number sets italic | everywhere |
| G2 scripts not stacked | **fixed** | everywhere |
| G3 bold formulas | **fixed**, but the fix left stray bold words (GD11) | p. 6, 17, 33, 37–41 |
| G4 no quad between formulas of a display | **fixed**, one residue: `M_w(Σ) = 𝔡_1·𝒜·𝔡_2, (𝔡_1)_D = …` | p. 36 |
| G5 slanted floor/ceiling brackets | **fixed** | p. 32–33 |
| G6 stretch inside formulas | **fixed** (fixed math spacing); loose word spaces remain (§5 item 5) | — |
| G7 words in formulas italic | **fixed** | p. 2, 10 |
| G8 upright `i` in italic labels | **fixed** | p. 20, 27, 41 |
| 1 p. 7 a quarter blank | **not fixed** (now 16 %; the proposed fix — start §1.7 on p. 7 — not applied) | p. 7 |
| 2 inline formula split after «=» across a page | that instance fixed; **the defect recurs**: «n ≡» / «3 (mod 4)» | p. 30/31 |
| 3 loosest line (7.4 pt) | fixed (now 4.9 pt) | p. 14 |
| 4, 5 displays wrapped by the renderer | **fixed** (split by hand, `multline`) | p. 16 |
| 6, 10, 13, 14, 23 statements split | **fixed** | p. 16, 20, 23, 24, 40 |
| 7 heading §4.4 with one line under it | fixed | p. 17 |
| 8 line beginning with «+» | fixed | p. 20 |
| 9 «Σ h_t = 0.» alone | fixed | p. 20 |
| 11 «min» / «D» split | fixed | p. 20 |
| 12 blank and widow p. 20/21 | fixed | p. 21 |
| 15 lead-in «By Lemma 7.3,» separated from its display | fixed | p. 25 |
| 16 line beginning with «≥ 2» | fixed (words added, H16) | p. 28 |
| 17 «step» / «1» | fixed | p. 29 |
| 18 line beginning with «≤ g(n − i + 1)» | fixed (H17), but the new line is loose | p. 30 |
| 19 line beginning with «≤ max» | fixed | p. 30 |
| 20 break between «]» and «[» in `R_𝒮` | **not fixed in substance**: the «][» break is gone, the formula now breaks inside «[F^{(m)} : m ≥ / 1]» | p. 37 |
| 21 same break in `R_{Z/4}` | fixed (break after «:=») | p. 39 |
| 22 line beginning with «≡ 0» | fixed | p. 40 |
| 24 sixth of p. 41 blank | fixed (table rebuilt) | — |
| 25 §12.1 table unbalanced | **partly**: column merged; cells still centred, numbers cut from their nouns (GD29) | p. 43–46 |
| 26 last row alone under a repeated header | fixed | p. 44 |
| 27 path broken at «/» | fixed | p. 44 |
| 28 references as bullets | fixed; labels still not in a column (GD30) | p. 48–49 |
| notes C: §1.0 opens with a formula; «a_n is …» | **not fixed** (GD8) | p. 2, 5 |
| notes C: «b_0 ⊗» / «b_1 n» | **not fixed** | p. 16 |
| notes C: intervals broken inside brackets (p. 17) | **not fixed** | p. 17 |
| notes C: proof of Theorem 10.15 one paragraph; slanted `□` | fixed | p. 38, 42 |
| §5 items 9, 11, 12 (change of variables, five reference points, Author field) | fixed | p. 6, 48–49, metadata |

Count: of the 8 global and 28 specific defects, **33 are fixed, 1 partly (row 25), 2 not (rows 1 and 20)**; G3's fix created GD11; the defect class of row 2 recurs elsewhere; two of the minor notes remain. (Sealed S-16, hit.) Version 4's §1.0 says these defects were «all corrected in this version 4»: inexact (item 7).

### 6.2 The two rows of the fifth reader in §12.2, against its log

Every number is in `gate_cold5_full.log`, exactly (sealed S-17, hit): 65 532 houses; 192 024 penalty cells; 741 deletions; C1 1 942 of 16 380; C3 7 967 of 30 078; 10 455 real cells; S6 «0 of 10200»; C5 2 316 of 9 880. The code (`gate_cold5.py`) shows what two of them count, which the rows do not say: the 192 024 penalty cells are taken only on houses with a boundary (line 129, `if k <= KPEN and b is not None`; sealed S-19, hit), and the 9 880 control cells are those with `i ≥ 1` and at least two dancers (`I ≠ ∅`). See item 8, P-C2 and P-C3.

### 6.3 The builder: for each defect, the rule that should have prevented it, or the rule that is missing

Mechanisms marked † were confirmed by running the author's `phtml.py` on the formula (`logs/phtml_probe.log`).

| defect (this report) | rule | diagnosis |
|---|---|---|
| GD1 straight apostrophes | none | no smart-quote rule for `'` in text |
| GD2 italic number sets | (27), `ital()` | every Latin letter outside `NAMES` is made italic; missing: `Z`, `Q`, `F` as number sets → ℤ, ℚ, 𝔽 |
| GD3 misplaced accents | (27); `phtml.parse`, `kind == 'acc'` | the combining mark is appended to the italic letter (`atoms[-1].h += val`) and left to the font, which does not position U+0304/U+0302 over math italic letters; missing: an accent box over the letter, skewed as TeX's `\bar` |
| GD5, GD13 hyphenation in compounds, two-letter remainders | none (Chrome's `hyphens: auto`) | missing: `hyphenate-limit-chars: 6 3 3` (TeX's `\lefthyphenmin`/`\righthyphenmin`) and no hyphenation inside words that contain «-» |
| GD8 sentences opening with a formula | none | a writing rule, not a builder rule |
| GD9, GD21 no space in scripts («minΔ», «lastL positions ofP») | (6), G6 of `phtml.py` | «none in scripts» suppresses also the thin space after an operator name and the word spaces of text in scripts; TeX keeps both |
| GD10 `…` between relations | none | missing: `…` between two binary operators or relations → `⋯` |
| GD11 stray bold words | (36) | (36) drops the bold of the formulas only; the words of the same bold span stay bold. Missing: drop the bold of a span that is mostly formula, or bold math throughout |
| GD12 end-of-proof mark | (7) | (7) only joins «∎» to the word before; missing: right alignment, and a glyph from STIX Two Math (it falls back to STIXGeneral) |
| GD14 mathematics in headings | (27) | headings are not passed to `phtml.py` |
| GD15 condition after a display at a word space | (28) | (28) puts a quad between two formulas, not between a formula and a parenthetical condition |
| GD16, GD27 delimiters not sized; solidus before `∏` | (27) | no delimiter sizing in `phtml.py`; missing: `\big`-sized brackets around a display-size operator, `\frac` for a solidus before one |
| GD17 «½» | none | the md character is passed through |
| GD18 citation key hyphenated; citation split in its brackets | (10), (25) | (10) joins «Lemma 7.2»; (25) protects file names; citation keys and «[Key, §n]» are protected by neither |
| GD19 binary «+» set as unary † | G6, `opening_fence` | `opening_fence` counts earlier bars with the same `src`, script included, so the third closing «‖» with an exponent is taken for an opening bar and the «+» after it becomes unary |
| GD20 variable isolated by quads in a display with words | (28) | the quad of (28) is applied around every code span of a display line, also around a one-letter span inside the words |
| GD22 bullets and labels | none | missing: a «- (X) …» item as a labelled list |
| GD23 `max`/`min`/`mean` limits at the side in displays | G2 of `phtml.py` | only the atoms of `BIG` (`Σ ∏ ⊕ ⋃ ⋂`) take limits under; missing: operator names with a subscript in display style |
| GD24, «n − / 2», «2 · / Syl», «b_0 ⊗ / b_1n» | `to_html` break rules | a break is allowed after any relation or binary operator outside a group of ≤ 12 characters; missing: no page break inside an inline formula (the v3 fix (14)/(16) did not cover it), and no break that leaves a two-character operand |
| GD25 n-ary `⊕` set binary † | G2, `parse` | `⊕` is large only when followed by a script; after a relation and before «(» it becomes unary and small. Missing: `⊕` at the start of an operand is the n-ary sum (or write `⊕_λ` in the md) |
| GD26 matrices as lists | none | missing: `[[a, b], [c, d]]` → a matrix |
| GD28 «=:» split † | `pmath.tokenize` | only «:=» is one token; «=:» becomes «=» and «:», two relations with their margins. Missing: «=:» as one relation |
| GD29 numbers cut from nouns in tables | (3), (17), (29)–(30) | (3) joins digit groups only; nothing joins a number to the next word |
| GD31 STIXGeneral fallbacks | `CSS .mx` | the font stack `"STIX Two Math", "STIXGeneral"` lets Chrome fall back silently; missing: a check that every glyph comes from STIX Two |
| GD32 no page numbers | `chrome_pdf.sh` | Chrome is called with `--no-pdf-header-footer`; missing: a footer with the folio |
| breaks inside short bracket groups («(0 ≤ / r ≤ m + 1)», «[F^{(m)} : m ≥ / 1]», «{1: / 6, …}») | `short_groups` (≤ 12 characters) | the limit was lowered from 40 (rule (12)) to 12 «measured: 40 left 8 lines with gaps > 7 pt, 12 leaves 5»: the looseness measure overruled the line-breaking rule; these groups have 13–16 characters |
| p. 7 and p. 42 short | (38), (31) | (38) lets a long table leave two rows at the foot, but the §1.7 table has 23 rows and its introduction is kept with it by `p:has(+ table)`; missing: let the heading, introduction and table start on the short page |
| loose lines (2 × the median word space) | (20) dropped | justification without `text-wrap: pretty` and with the narrow measure of the tables; the measure used (> 7 pt) is above twice the normal space |
| Theorem 4.4 as one line; «(K)» glued | none | missing: `cases`, equation tags |

### 6.4 The author's checks — do they measure what `CORRECTIONS_v3_to_v4.md` §6 says?

| row of §6 | check | verdict |
|---|---|---|
| statements split across pages: 0 | `structure.py` | it examines the 68 statements whose md line starts with «**», not the 7 boxed ones (Main Theorem, Theorem D, Theorem DW, Corollaries 1.4–1.7); and it cannot place 4 of the 68. The «0» holds (I saw all 75 whole), but the tool measures less than the row says |
| elements past the text block: 0 | `overflow.sh` | measures that (every listed element against the body's right edge + 0.5 px). Its header also claims «every display or nowrap piece wider than its container»; the code does not test containers (a nowrap formula wider than its table cell would pass). I did not run it (it calls `chrome_pdf.sh` in a folder this reading may not open) |
| largest right edge 541.93 | `margins.py` | measures that; reproduced |
| gaps > 6 / > 7 pt: 10 / 0 | `gaps_text_words.py` | measures that (gaps between two plain words); reproduced. It is blind to lines with few plain words and its thresholds sit at 1.9 × and 2.2 × the normal space (§5 item 5) |
| mean gap > 7 pt: 0 | `loose2.py` | measures that (gaps with a word on one side, scripts dropped) |
| widows and orphans: 0 | `widows.py` | measures that; reproduced |
| **pages under 90 % full: p7 (84 %), p42 (75 %)** | `fill.py` | **does not measure that**: it flags pages under **85 %**. Its own output (`logs/author_fill.log`) prints p. 23 at 89.3 % without a flag, so the row omits p. 23 (and p. 49, the last page, 88.6 %). Sealed S-21, hit |
| numbers of the tables OK | `md_vs_pdf.py` | measures that (as multisets); it does not check the boxed statements |
| references 32 / 32 / alphabetical | `xrefs.py` | measures that; but the same run prints 21 «MISSING TARGET» (all false: boxed statements, other papers' numbering), which the row passes over |

`CORRECTIONS_v3_to_v4.md` itself: §1 says «items 7, 8 and 11 below» (there is no item 11); §5 says the rewording of Lemma 3.5 «is listed in §13 of version 4» — it is not, and rightly so, since that rewording was in the *proof* of Lemma 3.5 (REPORT_COLD_5 §3, v2 line 293), not in its statement; §2 says rows 11 and 17 (a number separated from its word) are fixed by rules (29), (30), (32) — they are in the text, not in the tables (GD29).

### 6.5 The gates

I did not run any gate of the paper. The doubts raised by the changed rows of §12 were settled by reading: `gate_sections5to7.py` checks Proposition 5.4 only through its clock identity (lines 154–158; sealed S-18, hit), so the §12.1 row «Propositions 5.2 · 5.3 · 5.4» says more than the code for 5.4 (P-C1); and the other changed rows are confirmed by my own recount (`logs/cells.log`) and by the fifth reader's log.

## 7. Sealed predictions, hits and failures

All 21 predictions were written to `checks/SEALED.md`, with odds, before the measurement they predict; the outcome was added after it, citing the log. **19 hits, 1 failure, 1 split.** Most were sealed after reasoning (for example S-3 after the arithmetic by hand), so a hit confirms a computation rather than a blind guess; the odds say how sure I was.

| # | prediction (short) | odds | outcome |
|---|---|---|---|
| S-1 | the given diff is `diff -u` of the two md | 95 % | hit |
| S-2 | exactly H11, H12, H14, H18, H22 layout-only under N1 | 75 % | hit |
| S-3 | 7 874 cells, 254 with `i = 0`, 240 with `i = 0` and `I ≠ ∅`, 7 620 with `i ≥ 1` | 90 % | hit |
| S-4 | pooling acts in 1 834 cells with `i ≥ 1`, 1 876 in all | 70 % | hit |
| S-5 | reader 5's control 2 316 of 9 880 reproduced | 65 % | hit |
| S-6 | no non-integral block mean in 10 455 cells | 98 % | hit |
| S-7 | control 1 942 of 16 380 reproduced | 65 % | hit |
| **S-8** | **a page other than 1, 7, 42, 49 under 90 % — «I expect p. 11»** | 75 % | **split: the claim held (p. 23, 89 %), the named page failed (p. 11 is 97 % full)** — my eye misread the downscaled views (E-3) |
| S-9 | `gaps_text_words.py`: 10 / 0 | 85 % | hit |
| S-10 | largest `xMax` 541.93 | 90 % | hit |
| S-11 | `structure.py`: 0 split, ≥ 4 unplaced | 80 % | hit |
| S-12 | `xrefs.py` false alarms on boxed statements | 60 % | hit (21 false) |
| S-13 | `widows.py`: only the chapter start | 70 % | hit |
| S-14 | no page numbers | 85 % | hit |
| **S-15** | **my hyphen scan finds ≥ 3 bad hyphenations beyond those I had seen** | 60 % | **failure: only 2 new (p. 42, p. 48)** |
| S-16 | ≥ 3 defects of reading 5 not (fully) fixed | 60 % | hit |
| S-17 | every number of reader 5's rows in its log | 80 % | hit |
| S-18 | the gate checks only the clock identity of Prop. 5.4 | 70 % | hit |
| S-19 | 192 024 = penalty cells on houses with a boundary only | 65 % | hit |
| S-20 | «240 with `i = 0`» not written by reader 5 | 50 % | hit |
| S-21 | the author's `fill.py` shows p. 23 under 90 % without flag | 75 % | hit |

## 8. My errors

- **E-1.** I typed `echo =====` in zsh (a word starting with «=», forbidden by the mission); the command failed halfway, no file was written; redone with quoted separators (`logs/DIARY.md`).
- **E-2.** I ran a small python count of apostrophes outside `vigia.sh`; re-run under the watchdog (`logs/apos.log`), same result.
- **E-3.** In `checks/PAGES.md` I first wrote that p. 5, p. 11 and p. 15 ended 12–18 % blank, judging by eye from the downscaled 90-dpi views; the measured fill is 99 %, 97 % and 95 % (`logs/pdfcheck2.log`). Corrected in place, marked «CORRECTED … E-3». It also made S-8 half wrong.
- **E-4.** An empty `python3 - <<EOF` (a no-op) ran outside the watchdog before two `perl` edits; no computation.
- **E-5.** The first version of my hyphenation scan took a band of sub/superscripts for «the next line» and missed three bad hyphenations I had seen (p. 13, 27, 35); I found the bug by comparing with my page notes and fixed it (`scratch/pdfcheck.py`, log `pdfcheck2.log`; the first version is kept as `pdfcheck_v1.py`).
- **E-6.** The first version of `stmt_cmp.py` matched labels at their first mention (the §1.0 table, «Proposition 9.6 (H)» in §7.5), which produced false differences; fixed with a monotonic search (`logs/stmt_cmp2.log`).
- **E-7.** Two crops at 400–600 dpi were taken at wrong coordinates (p. 14) and repeated; no consequence.
- Not an error of mine but worth saying: the mission speaks of «§1.4 item 1» for the change of variables; the sentence is in §1.5, item 1.

## 9. What I did not read

- **The unchanged mathematics.** As the mission says (§4), I did not re-grade unchanged statements. I read closely what the changed sentences depend on: §1, §4.1–§4.4, §5, §7 (all), §8, §9.1–§9.2, the proof of Lemma 10.6 and §10.3, §11–§13, Appendix A, the references. §2, §3, §6, §9.3, §10.1–§10.2 and §10.4–§10.8 I looked at only as typesetting, on the pages.
- **Sources:** only the GMMY preprint (Proposition 2.5 and its proof, Theorem 2.8), the JMM poster (author line and conjectures), and the first lines of `SubsetIntersection_arXiv2310.09227.txt` and `Adinkras2rank_arXiv2301.02517.txt`. The journal data of [GMMY24] and [Yue24] are not in the sources and were not checked.
- **The v4 html** and **the v3 pdf**: not opened. The v3 md only through the diff.
- **`material/read_after/`:** not read — the gates other than `gate_sections5to7.py` (lines 128–172 only): `gate_dance.py`, `gate_direct.py`, `gate_lemma72.py`, `gate_section10.py`, `gate_section9.py`, `gate_strict_cut.py`, `gate_theoremO.py`, `rule_abs.py`, `remark2/*`; `md2html_v4.py` beyond its header and first 140 lines; `pmath.py` beyond its tables; `gate_cold5.py` beyond its counting loops; §7–§10 of `REPORT_COLD_5.md`. No gate was run. `overflow.sh` was read but not run (it calls a script in a folder this reading may not open).
- **The pages at 200 dpi:** I zoomed every doubtful region (about 90 crops), not every page whole at 200 dpi; at 90 dpi every page was seen whole.

## 10. Files with md5

Every file I wrote is listed with its md5 in **`checks/MD5_COLD6.txt` (260 files, md5 `4199a3bf6eb6d6a4081b3d78158ece1b`)**: this note, the checks, 108 logs, my scripts and drafts, the text extractions, 49 page renderings at 90 dpi and 72 crops. Three files cannot be in it: this report (its md5 is the last line of `logs/DIARY.md`), `logs/DIARY.md` itself (it is written after), and the log of the run that wrote the list. The material was checked against `MANIFEST_md5.txt` at the start and at the end (`logs/manifest_md5.log`, `logs/manifest_md5_end.log`): all 72 files unchanged.

The files a reader of this report needs:

| file | md5 |
|---|---|
| `ESTADO.md` | `eb8329f45a3b67b2f5af4de0b2db8929` |
| `checks/SEALED.md` | `b67bb50b67b8295e09bf344ce0a82159` |
| `checks/PAGES.md` | `09cf25aa3a707e6b749af55038f01342` |
| `checks/PDF_DEFECTS.md` | `a1c6fd7e326add4219266604fab14deb` |
| `scratch/normcmp.py` · `logs/normcmp.log` · `logs/normcmp_control.log` | `4e20e44d53f484783329600c3d0c2bc0` · `fa0f1d7d29ed2f5e818abc2ea4e97b36` · `a50b758a047d1345b43adb8c1bd4b25a` |
| `scratch/cells.py` · `logs/cells.log` | `76e34979f0553281363e26dfb8d90e6b` · `58f725fa65ca2af5ec074312a613b216` |
| `scratch/refs.py` · `logs/refs.log` · `logs/refs_control.log` | `3b17fbc8dfcf73db412118771bdaf982` · `fdd8ddf758e0398ed248858b54fb2f67` · `b4e3f6c82bac7c478a65ee08abfe01fd` |
| `scratch/pdfcheck.py` · `logs/pdfcheck2.log` | `342e193ed16e4cde4eb75cce1db228e5` · `58cca0f4c5c1fc9422030a152063916f` |
| `scratch/lines2.py` · `logs/lines2.log` | `83108ee0f76afc10e8b91f7ed8908dd2` · `b717bc8de428ca229d37fc316f97b08e` |
| `scratch/stmt_cmp.py` · `logs/stmt_cmp2.log` · `logs/stmt_cmp2_control.log` | `e48e75103f1283b20a633be75a101f51` · `ab4efa0ebe797e551ebfc470fdb02734` · `9f01bbdf773d3591b9878792a95c7d53` |
| `scratch/xref2.py` · `logs/xref2.log` · `logs/xref2_control.log` | `107cdddcd6fb1e68294aa44f48ff3858` · `0a1f1fb10e64f77966576a4c4a3493b6` · `c75ef7f2c6fd41965bc84cf31b910e16` |
| `scratch/codenames.py` · `logs/codenames.log` | `4eb8fc2726694f047abb5c60a5ee561f` · `020ed5a1e36ca57bca0cc95c7daded0f` |
| `scratch/accents.py` · `logs/accents.log` | `9218144b74f4e9c4cb214e5fa5aacfcd` · `5a282ff28ccd1dbbb85e93458e255963` |
| `scratch/boldmix.py` | `e2e1da50c3fca965c7eb35653f43185a` |
| `scratch/apos.py` | `3d8a0aeda4e92dc2849422cbe217f3e3` |
| `scratch/phtml_probe.py` · `logs/phtml_probe.log` | `42e65e341db84a71b349b729f1578419` · `00a9573df1696787e97134cf8e16f66d` |
| `logs/pdffonts.log` · `logs/pdffonts_pages.log` · `logs/qed_pages.log` | `653fba35fe94842cc1a392b548e2e3d9` · `0bb2a0b22de8b22749a34e3ed77af458` · `0fa8525a6d30247b1d87321d1b481076` |
| `logs/author_fill.log` | `5b83c73cceca73caf16d4ef350d235b0` |
| `logs/regen_diff.log` | `265ef2b660424ff74caa21d11933849e` |
