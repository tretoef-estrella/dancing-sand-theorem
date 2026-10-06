# REPORT_COLD_5 — cold reading 5 of «The Dancing Sand Theorem», version 3 (the changes, and the pdf)

Reader: Grepy Muchas Pilas. Started 2026-10-05 18:35 CEST. Material verified against `MANIFEST_at_launch.txt` (all md5 equal) at 18:35:34.

## 0. First lines

- **Do the changes hold as written: HOLDS.** The mathematics of every change of version 3 holds; I found no GAP and no ERROR. Lemma 7.9 (integrality) holds: I re-derived it (induction on `|I|`, with (Cut), the first part of Lemma 7.2(b) and Lemma 7.3; no circularity), and my own gate, written from the text alone, finds 0 non-integral fits on 65 532 houses (`k ≤ 7`, `α ≤ 3`), 192 024 penalty cells, 741 deletions and 10 455 real cells (`λ ≤ 255`, `i ≤ 40`), with controls that fire. Every use of Lemma 7.9 (§8, Theorem 7.10, Proposition 9.6 (H), (K)) gets what it needs; the cases of Theorem 7.8 step 3 are exhaustive; «even» in Lemma 10.6(a) is used exactly where the proof divides by 2 and is missing nowhere else; the [Aky26] quotation is exact. No counterexample to any numbered statement: the Stop rule was not triggered.
  About twenty points of PRESENTATION in the text, none mathematical. The main ones: the paragraph after Lemma 7.9 says strictness is now needed «only» in Proposition 9.6 (H), while the text still cites it in Theorem 7.8 and Theorem 7.10, and it is needed twice in 9.6 (H) (§1.2); the reading record (§1.0, §13, Appendix A) is inexact in six sentences, among them that the Main Theorem is graded «read cold» while its printed proof passes through Lemma 7.9, and that the finding in Lemma 10.6(a) is the author's, not reader 4's (§1.8); «Why dance» in §1.7 states a payment that holds only for the first system (§1.9); two rows of §12.1 under-describe their range (§1.10, §6).
- **Is the pdf perfect: NO** — 8 global defects (formulas set wholly in italic, indices not stacked, bold formulas, no space between formulas of one display, slanted brackets, the line stretch going inside formulas, words in formulas italic, upright `i` in italic labels), **28 specific defects** (five numbered statements split across pages; five lines that begin with a relation or an operator; two breaks between «]» and «[»; two long displays wrapped by the renderer with a centred continuation; three blanks to fix, on p7, p20 and p41; the unbalanced table of §12.1; the references set as bullets; and others, §4), and 8 minor notes. Clean: margins (no word past the margin), every font embedded, every glyph present, md and pdf identical in tables and statements, every cross-reference and citation right.
- **Is version 3 ready for publication: AFTER CORRECTIONS** — of presentation and typesetting only; no correction of mathematics is needed. The specific defects can be fixed in the md and in the builder's rules (§6 maps each to its rule). The global ones (G1, G2) need a real math renderer; without it the pdf cannot meet a top journal's typesetting standard, though its mathematics would not change.

## 1. The mathematics of the changes (§2, item by item)

*Honesty note.* The mission asked me to prove Lemma 7.9 before reading its proof. My first pass over `DIFF_v2_to_v3.txt` (Part 1) showed me the new proof before I tried. My own derivation below is therefore not blind; I wrote it in my own words and checked each step against the definitions, not against the text.

### 1.1 Lemma 7.9 (integrality) — HOLDS

My derivation. Induction on `|I|`, for the house statement only; the two other statements follow at the same `I`.
- `I = ∅`: one dancer, `x_H(∅) = R_H(∅) − R_H(∅) = 0`; the fit is `(0)`.
- `I ≠ ∅`, `c = max I`, `H' = (I', c, ℓ mod 2^c, α)` (a house). In o-order the dancers without `c` come first (`o < 2^c`), in the o-order of `H'`. Lemma 7.7 gives the first half `x_{H'} + d_1`, with `d_1(D_0) = −τ − [T=1]κJ'(D_0) + [T=0]κJ'(I'∖D_0)` (I re-derived it from the two rulers: `I∖D_0 = (I'∖D_0) ∪ {c}`).
- `d_1` is an integer, non-increasing (`J'` is an up-set; `J'∘mirror` is a down-set), and constant except at the cut position `p(b')` of the first dancer `b'` with `J' = 1` (term `T = 1`) or at its mirror position `N' − p(b')` (term `T = 0`); constant if `J' ≡ 0`. Both are cuts of `x_{H'}` by (Cut) for `H'` (non-strict cuts suffice).
- First part of Lemma 7.2(b) (cuts only, no integrality needed): `fit(x_{H'} + d_1) = fit(x_{H'}) + d_1`. By induction `fit(x_{H'})` is integral, so `Z_1` is integral, and Lemma 7.3 gives `fit(x_H) = [max(Z_1, 0), min(Z_2, 0)]`, integral.
- Penalty cell: the shift `−P_r J_H(D) + P_c J_H(I∖D)` is an integer, non-increasing, and changes only at the cut position of the first dancer with `J_H = 1` and at its mirror; these are cuts by (Cut) for `H`; first part of Lemma 7.2(b) again.
- Deletion (`ℓ = 2^k − 1`, `I ≠ ∅`): `J_H(D) = [D ≠ ∅]`, so the first dancer with `J_H = 1` is `{t_1}`, at position `1`; a cut at position `1` means `fit(x) = fit(x_0) ++ fit(x_{≥1})`, so the fit without `∅` is the restriction of `fit(x_H)`.
- On a level set with integral value `z` and `p` positions, `S = pz`, `S mod p = 0`, and the rounding returns `z`.

**No circularity.** Lemma 7.9 uses (Cut) of Theorem 7.8 (for `H'` and for `H`); Theorem 7.8 does not use Lemma 7.9 (it uses the strict cuts of `H'` and the integer part of Lemma 7.2(b) in step 1). I checked every citation of Lemma 7.9 in the text: none is inside Theorem 7.8.

**Base case:** right. **Real part of Lemma 7.2(b) at non-strict cuts:** right; it needs only that `δ` is non-increasing and constant between consecutive cut positions (I re-derived the multi-cut case from Lemma 7.2(a) and (c); the text says «(a) applies», which is one cut at a time — fine). **Lemma 7.3:** applied to `x = x_H`, antisymmetric, `Z_1 = fit(first half)`: right. **Penalty shifts, deletion:** right.

### 1.2 Every use of Lemma 7.9 — HOLDS; the claim about strictness is right in substance, inexact as written (PRESENTATION)

- **§8:** «The fits are integral, so the integer fits are the fits themselves, and they are non-increasing (Lemma 7.9).» Needs exactly: the integer fit of the clocks of the real cell (`i ≥ 1`; a penalty cell by Lemma 7.5, plus the constant `k + K + κ(m, K)` by Proposition 5.3) and of the deleted sequence (`i = 0`; `x^♯ = x_{H^♯}` restricted to `D ≠ ∅`, Theorem 7.10) is non-increasing. Lemma 7.9 gives it. HOLDS.
- **Theorem 7.10:** «Lemma 7.9 gives monotonicity» — the hypothesis of Theorem 6.5. HOLDS. (Its (U2) still argues the integer fit through strict cuts and the integer part of Lemma 7.2(b); with Lemma 7.9 a cut suffices. Not wrong.)
- **Proposition 9.6 (H):** «the mean `μ` … which is an integer (Lemma 7.9)» — the largest big clock is the value of the first level set of the real fit of the cell clocks plus a constant, i.e. the mean of `u_i` over the head; Lemma 7.9 makes it an integer, so no `⌈ ⌉` is needed. HOLDS.
- **Proposition 9.6 (K):** «every term of the mean is `≤ g(n − i + 1)`, and so is `μ`» — a mean of numbers `≤ g` is `≤ g`; integrality is not even needed here. HOLDS.
- **«Strictness is needed only in Proposition 9.6 (H)».** *Is it needed there?* Yes, by the argument as written, and in two places, not one: (i) in the base-cell induction («the first level set of the first half is the child's first level set»), which needs `d_1` constant on every level set of `fit(x_{H'})`, i.e. the strict cuts of `H'` (second part of Lemma 7.2(b)); (ii) for the penalty shift, as the text says. A jump at a cut inside the head would cut the head at the boundary position, which need not be a power of `2` (measured in §2 below). *Is it needed anywhere else?* Logically no: with Lemma 7.9, every other use of the integer part of Lemma 7.2(b) — Theorem 7.8 step 1 («its integer fit is `X_1`») and step 3(c) («its integer fit is `X_2`»), Theorem 7.10 (U2) and its `i = 0` case — can be done with cuts, the integer fit being the real fit. **But the text still invokes strictness in all those places**, and in Theorem 7.8 the replacement needs a joint induction (Theorem 7.8 and Lemma 7.9 together on `|I|`), because Lemma 7.9 is proved after Theorem 7.8 and uses its (Cut). So the paragraph after Lemma 7.9 («It is used where the level sets themselves matter, in Proposition 9.6 (H)») is true of what is *indispensable*, and misleading as a description of the text. **PRESENTATION, proposed fix:** «As written, strictness is also used in Theorem 7.8 (steps 1 and 3) and in Theorem 7.10, to identify integer fits; with Lemma 7.9 a cut suffices there (in Theorem 7.8 by a joint induction with Lemma 7.9). It is indispensable only in Proposition 9.6 (H), twice: in the base-cell induction, and for the penalty shift.»

### 1.3 §1.2 «the rounding never acts in the cube», and the vocabulary row — HOLDS (one PRESENTATION point)

It follows from Lemma 7.9 *together with* Proposition 5.3 (`u_i = k + K + κ(m, K) + x_D`), Lemma 7.5 (the real cell is a penalty cell) and Proposition 5.4 / Theorem 7.10 (`u_0` is `x_{H^♯}` without `∅`, plus a constant); and no more. The bare citation «(Lemma 7.9)» skips the identification. **PRESENTATION:** cite «(Lemma 7.9, with Proposition 5.3, Lemma 7.5 and Proposition 5.4)», or «(§8)». The vocabulary row «which in the cube is always an integer sequence (Lemma 7.9)» has the same omission; it is a table, so the short citation is acceptable there.

### 1.4 §7.1, «a strict drop of the fit is a cut», and the proof of Lemma 7.2(b) — HOLDS

If `z = fit(x)` drops strictly at `b`, no level set of `z` crosses `b`; so `z_{<b}` is non-increasing and its level sets are level sets of `z`, each satisfying the conditions of Lemma 7.1 for `x_{<b}`; the «if» direction of Lemma 7.1 gives `z_{<b} = fit(x_{<b})`; likewise after `b`. So `x` is cut at `b`. «Strict cut ⟺ no level set contains `b − 1` and `b`» follows. In Lemma 7.2(b), «a strict cut stays strict»: `fit(x + δ) = fit(x) + δ` drops strictly at `b` because `fit(x)` does and `δ` is non-increasing, and a strict drop is a cut. HOLDS.

### 1.5 Theorem 7.8, step 3, cases (c) and (d) — HOLDS; the cases are exhaustive

From Lemma 7.7, `J_H = ([T=1]·sat·J', sat·([T=1] + [T=0]J'))`. (a) `T=1, sat=1, J' ≢ 0`; (b) `T=1, sat=1, J' ≡ 0`; (c) `T=0, sat=1, J' ≢ 0`; (d) `sat = 0`, or `T = 0` and `J' ≡ 0`. The union is everything, and in (d) `J_H ≡ 0` in both sub-cases. In (c) I re-derived `d_2 = −(d_1 ∘ mirror)` and `X_2(b' ∪ {c}) = ŷ'(b') − α2^c ≤ −α`. One remark, not new in version 3: in (c) the sentence «changes only at cuts of `x_{H'}`; so … its integer fit is `X_2 = ŷ' + d_2`» needs the integer part of Lemma 7.2(b), i.e. strictness (stated two lines later) or Lemma 7.9; it is also simply the mirror-negative of step 1. Fine.

### 1.6 Proposition 9.6 (H): «`Z_1 ≤ 0`», and «the largest big clock is the integral mean `μ`» — HOLDS

`Z_1` is non-increasing, so if its first level set (the child's, shifted by the constant value of `d_1` there) has value `≤ 0`, then `Z_1 ≤ 0` on the whole first half, `fit(x_H) = 0` on the first half and `min(Z_2, 0) = 0` on the second: one level set, `{D ⊆ P_s}`. The new wording («`Z_1 ≤ 0`» in place of «every value of `X_1` is `≤ 0`») is the right object: the statement is about the real fit. The largest big clock is the value of the first level set of the (real) fit, i.e. the mean `μ` of the raw clocks over the head, an integer by Lemma 7.9. HOLDS.

### 1.7 «Even» payment systems: Remarks (1), (2) of §10.5 and Lemma 10.6(a) — HOLDS (one PRESENTATION point)

- In Lemma 10.6(a) evenness is used exactly where the proof divides by `2`: `S = Dd − BP^{−1}C = 2F − B·C` with `P = 1`; `S ≡ 0 (mod 2)` (cleanliness) and `S/2 = G'` even (so that the next move applies) both need `B·C ∈ 4·Mat`, i.e. the evenness of the payments and couplings (Proposition 4.1: «halves of products of two elements of `2A`»). The algebraic identity `S/2 = G'` itself holds for any payment system over `Q_2`. **PRESENTATION:** the proof never says that the move is clean; add «`P = 1` is invertible and `S = 2G'` with `G'` even (Proposition 4.1), so the move is clean». For the split move the `V`-split creates a coupling `1` (odd), and cleanliness comes from the identification with Proposition 4.2, which needs evenness; fine.
- Remark (2) «every even payment system dances clean, whatever its payments (Proposition 4.1, Lemma 10.6(a))»: right; add Proposition 4.2 for the split moves (PRESENTATION, minor).
- Remark (1): right («an even payment system»).
- **Is «even» needed anywhere else in §10 and missing?** I read every occurrence of «payment system» in the text (12, listed in `scratch/`): every statement that needs evenness has it. Lemma 10.6(b) applies (a) to `σ^{(α)}_c`, which is even (`α ≥ 1`). Nothing missing.

### 1.8 The reading record: §1.0, §13, Appendix A — three inexact sentences (PRESENTATION)

- **Attribution.** Appendix A, version-2 bullet: «It found one false sentence (Remark (2) of §10.5 … ; the same word was missing in Lemma 10.6(a))» attributes both findings to cold reader 4. The author's own list (`CORRECTIONS_v2_to_v3.md` §1.1) says: «The reader found the missing word in Remark (2). I found the same gap in Lemma 10.6(a)». **Fix:** «…where Proposition 4.1 needs an even one; the author then found the same word missing in Lemma 10.6(a)».
- **«One false sentence, in a remark used nowhere»** (§1.0, and Appendix A) understates: the same missing hypothesis was in Lemma 10.6(a), a numbered lemma that *is* used (Lemma 10.6(b), Theorems 10.12, 10.16). It was harmless — its only application is to `σ^{(α)}_c`, which is even — but a statement of the paper was false as written in version 2. **Fix:** «one false sentence in a remark used nowhere, and the same missing hypothesis in Lemma 10.6(a), harmless because its only use is for an even system».
- **§13, first bullet** grades the Main Theorem «read cold», while its printed proof in version 3 rests on Lemma 7.9 (§8, Theorem 7.10), which the second bullet lists as not yet read cold. Before this reading the printed proof had one link not read cold. (After this reading — if this report is accepted — the sentence becomes exact; it should then name this reading.)
- **Appendix A, version-3 bullet:** «keeps the repair of version 2 as it was read» — the text of the repair was edited (§7.1, the proof of Lemma 7.2(b), Theorem 7.8 step 3 (c)–(d), Proposition 9.6 (H)). The mathematics was kept; the words were not. **Fix:** «keeps the mathematics of the repair of version 2 as it was read, with the clarifications listed above».
- §1.0 calls reader 4's other findings «points of presentation»; two of them were rows of §12.1 that said more than their code — a matter of the verification record, not presentation. Minor.
- **§13, second bullet:** «No statement of a theorem changed in version 2 or in version 3; Lemma 7.2(b) was restated in version 2, and Lemma 7.9 was strengthened in version 3.» The list of changed statements is incomplete: in version 3 the statement of Lemma 10.6(a) also changed (the hypothesis «even» was added, `DIFF_v2_to_v3.txt` lines 379–380), and Lemma 10.10 gained the quantifier «For every `L ≥ 0` and every floor `f`» (lines 400–401). Both are lemmas, so the sentence about theorems stays true. **Fix:** add «and Lemma 10.6(a) gained the hypothesis "even"» (found while looking at p45).

### 1.9 §1.7 and §1.8 — three rewordings HOLD, one is inexact (PRESENTATION); the [Aky26] quotation HOLDS

- **Covariant system:** «coefficients depend only on `Δ = D ∖ D'`, on `m` and on the position of the target» = the definition of §10.5 (which also requires `G[D, D'] = 0` unless `D' ⊆ D`; acceptable in a table). HOLDS.
- **The fit:** see 1.3. HOLDS.
- **«At every step each floor pays an even amount, `2^α(i + d)` at the floor `d`»** — inexact. `2^α(i + d)` is the payment of the *first* system `σ^{(α)}_i` only. After a move the payments are `−π(2f)π(2f+1)/2` (Proposition 4.1), products of the original payments over windows (Theorem 4.4), still even. **Fix:** «At the start each floor `d` pays the even amount `2^α(i + d)`; each move multiplies the payments of two adjacent floors and halves them, so every payment stays even, and at the end…».
- **«the tensor product of `V` with a Frobenius twist»:** matches Proposition 3.1(c) (strictly `(T(l) ⊗ F_2)^{[1]}`; the twist is of the reduction). HOLDS.
- **[Aky26]** against `material/sources/TwoAdicAllOnesSquare_arXiv2609.10625.txt`, lines 559–567 (§4 «Further directions», paragraph «Reflections and the exceptional prime»): the quotation «a natural place to look for additional structure under an involution» is exact; the question «Can an analogous integral description with fixed vertices explain both the folded all-ones class and the remaining 2-primary factors?» is exact and whole; «Their reflections of odd grids have fixed vertices, so their fold is not a regular double cover» is a faithful paraphrase of «Our odd-grid reflections have fixed vertices, however, so the fold is not a regular double cover and their splitting theorem does not apply directly». Section number `§4` right; authors, title and arXiv number of the reference right. HOLDS. (The text drops «and their splitting theorem does not apply directly»; it does not change the meaning.)

### 1.10 §12.1 and §12.2 — the rows are consistent; two PRESENTATION points (the controls are judged against the code in §6)

I recomputed every count of the changed rows from its stated range (`scratch/` and my gate):
- Theorem 7.10, `λ < 64`, `i ≤ 12`, `α = 1, 2`: `63 × 13 × 2 = 1 638` cells (so `λ = 1..63`, `i = 0..12`). ✓
- Theorem 7.8, «houses with `I ≠ ∅` and `k ≤ 6`, `α ≤ 3`»: `3·Σ_{k=1}^{6} 4^k − 3·Σ_{k=1}^{6} 2^k = 16 380 − 378 = 16 002`; `48 006 = 3 × 16 002`. ✓
- strict (Cut), «every house with `k ≤ 6`, `α ≤ 3`»: 16 380 ✓; «192 024 non-zero shifts (24 on each house with a boundary)»: `24 × 8 001` ✓ (24 = `5^2 − 1`, `P_r, P_c ≤ 4`); deletions `3·Σ_{k=1}^{6}(2^k − 1) = 360` ✓. My own gate finds the same 192 024 cells.
- reader 4, `k ≤ 7`: `3·Σ_{k=1}^{7} 4^k = 65 532` ✓; `777 240 = 24 × 32 385` ✓ (my gate: 32 385 houses with a boundary); deletions 741 ✓; `721 872 = 24 × 30 078` ✓ (my gate: 30 078 houses where «one dancer after the boundary» exists, and the same 7 967 failures).
- reader 3, «all houses with `k ≤ 7`, `α = 1, 2`»: `2·Σ_{k=0}^{7} 4^k = 43 690` ✓ (this one counts `k = 0`).
- Theorem 6.2, `|I| ≤ 5`, every `r`: `Σ_{s=0}^{5}(2^s + 1) = 69` ✓.

PRESENTATION:
1. **«`k ≤ 6` (`λ ≤ 127`)»** (§12.1, Theorem 7.8 row): `k ≤ 6` means `λ + 1 < 128`, i.e. `λ ≤ 126`. Write «(`λ ≤ 126`)» or drop the parenthesis (a house is not tied to a `λ`).
2. **Propositions 5.2 · 5.3 · 5.4, range «`λ < 64`»:** the printed counts fix the other ranges, which the row does not state: `109 200 = 1 365 × 40 × 2` (pairs `b ⊆ a`, `i = 1..40`, `α = 1, 2`), `14 560 = 364 × 40` (`α = 1`, `i = 1..40`), `301 = Σ(2^{|I|} − 1)` (`i = 0`). The range column should say «`λ < 64`, `i ≤ 40` (`α = 1, 2` for 5.2)». (To be confirmed against the code in §6.)
3. Reader 4's Lemma 7.9 row says «7 634 cells», its Theorem 7.10 row «7 874 cells» on the same range. Not checkable from the paper; worth one word of explanation (which cells).
4. §12.2, reader 3's row of Corollaries 1.5–1.7: the range «`n ≤ 300 · e ≤ 8`» uses the middle dot between two ranges, where elsewhere in the tables it separates statements; write «`n ≤ 300`; `e ≤ 8`» (found on p44).

Not stated more strongly than a check can show: no row claims a proof; «0 failures» rows are stated with their range. The rows «none» are honest («none» means no control).

## 2. My own gate (with controls)

Code: `checks/gate_cold5.py` (written from §1.2, §5, §7.1 and §7.3 alone, before opening `material/read_after/`; exact integer arithmetic, pool-adjacent-violators with block sums compared by cross-multiplication). Log: `logs/gate_cold5_full.log`, ends `VIGIA-FIN-OK exit=0 pico_kb=10416 t=7s`. Predictions sealed before any code in `checks/SEALED.md` (S1–S15).

| check | range | result | control (must fire) |
|---|---|---|---|
| tools: `(3,4,3,4)` is cut at `2` but not strictly, fit `7/2`; `(5,1,3)` → `(5,2,2)` | — | pass | — |
| Lemma 7.9: fit of `x_H` integral | every house `1 ≤ k ≤ 7`, `α ≤ 3`, every `ℓ`, every `I` (65 532) | 0 non-integral | `x_H` with `+1` at its first dancer (not a house): non-integral in 1 942 of 16 380 houses `k ≤ 6`; random antisymmetric integer sequences of length 8: non-integral in 3 299 of 10 000 |
| (Cut): cut at the boundary `b` and at `N − b`, both strict | the 32 385 houses with a boundary | 0 missing, 0 non-strict | strictness tested one dancer after the boundary fails in 7 967 of 30 078 |
| Lemma 7.9 for penalty cells, and Lemma 7.2(b) `fit(x + δ) = fit(x) + δ` | every house `k ≤ 6`, `α ≤ 3` with a boundary, `(P_r, P_c) ∈ [0,4]^2 ∖ {(0,0)}` (192 024 cells) | 0 non-integral, 0 shift failures | — |
| Lemma 7.9 for the deletion (`ℓ = 2^k − 1`, `I ≠ ∅`): integral, and equal to the restriction of `fit(x_H)` | `k ≤ 7`, `α ≤ 3` (741) | 0 failures | — |
| §1.2 «the rounding never acts»: the raw clocks `u_i(D)`, computed from §1.2 alone | every family `1 ≤ λ ≤ 255`, every shift `0 ≤ i ≤ 40` (10 455 cells) | 0 non-integral level sets | raw clocks with `+1` at the first dancer: non-integral in 2 316 of 9 880 |
| Proposition 5.3 (`u_i = k + K + κ(m, K) + x_D`, §5 rulers), Lemma 7.5 (§5 clocks = penalty cell of `(I, k, m mod K, 1)` with `r_k(m)`, `r_k(m + K)`), Proposition 5.4 (`u_0 = k + K + x_{H^♯}`) | the same | 0 mismatches | — |
| Proposition 9.6 (H): the head of the fit is `{D ⊆ P_l}` (length a power of `2`) | the 10 200 cells with `i ≥ 1` | 0 non-dyadic | — |

**The claim of item 2, measured.** In the 2 572 real cells with a boundary and a non-zero penalty, the position of the boundary is not a power of `2` in 1 734 cells (S14), and the head ends **exactly** at a jump of the penalty shift in 1 034 cells and never goes past one (S15, `logs/head_vs_jump.log`). So the head routinely touches the place where the shift jumps, at positions that are often not powers of `2`: the dyadic head depends on the jumps falling on level-set boundaries, which is what strictness provides. This supports «strictness is needed in (H)» as a statement about the argument. (My counterfactual S13 — the jump moved one dancer *later* — never split a head; it was badly designed, since the head always ends at or before the jump. A jump one dancer *earlier* would be the right counterfactual; I did not run it.)

**Agreement with the record, found afterwards.** My control C1 gives 1 942 houses, the number printed in §12.1 for `gate_strict_cut.py`; my strictness control gives 7 967 of 30 078 (`k ≤ 7`), the numbers printed in §12.2 for reader 4; my 192 024 penalty cells and 741 deletions are the counts printed in §12.1 and §12.2. Independent code, same numbers.

**Verdict on item 12:** Lemma 7.9 and the strict (Cut) hold on every house with `k ≤ 7` (penalties for `k ≤ 6`), and the claim of §1.2 holds on every family `λ ≤ 255` at every shift `i ≤ 40`, computed from the rule of §1.2 itself.

## 3. The presentation edits: content unchanged? (§2 item 11)

**Method.** `checks/hunks_normalized.py` (log `logs/hunks_normalized.log`, `VIGIA-FIN-OK`). For each of the 38 hunks of `DIFF_v2_to_v3.txt`, the removed text and the added text are each joined into one string, and from each I remove only: every whitespace character (so line breaks, indentation and spaces), a blockquote marker `>` at the start of a line, and a list bullet `- ` at the start of a line. Bold markers, backticks, punctuation, words and symbols are kept. The two strings are then compared character by character (`difflib`, no junk heuristic), and every difference is printed. I then read every differing hunk by eye against the author's list (`CORRECTIONS_v2_to_v3.md`).

**Result.** 9 hunks are identical after normalization (pure displays): the hunks at v2 lines 47, 323, 438, 493, 651, 771, 905, 940, 949. 18 hunks are the changes of content that the author lists (version line; §1.0; §1.2 pooling; the vocabulary header and two rows; «Why dance», «Why dry and wet»; [Aky26]; §7.1; Theorem 7.8 step 3 (c)–(d); Lemma 7.9; §8; Proposition 9.6; Lemma 10.6; Remarks of §10.5; §12.1; §12.2; §13; Appendix A). 11 hunks are presentation hunks in which **words or punctuation changed, but no symbol and no number**:

| v2 line | place | change | listed by the author? |
|---|---|---|---|
| 116 | Corollary 1.6, «In particular» as a list | «and» before the last item dropped | yes (list) |
| 261 | Proposition 3.1(b) | «(`e = 0, 1`)» after the first formula moved into the lead-in «for `s ≥ 0` and `e = 0, 1`:»; the second and third formulas name `b_0`, `b_1` explicitly, so the scope change is harmless | yes (display) |
| 277 | Lemma 3.2, Lemma 3.3 | comma after «by (K)» dropped; «gives the exact sequence» for «gives» | yes (display) |
| **293** | **Lemma 3.5, proof** | «`C(3, r) = 1, 3, 3, 1`» → «`1, 3, 3, 1` (that is, `C(3, r)`)» | **no**: Lemma 3.5 is not in the author's list of display edits («Proposition 3.1(b), Lemmas 3.2–3.3, §3.3, Theorem 3.8»). Same content. |
| 448 | Proposition 5.3, step 1 | one display split over two lines; the second line begins with «`= K + o_I …`» | yes (display) |
| 601 | Theorem 7.8, step 5 | «by (Λ) for `H'`» moved from the end to the front | yes |
| 670 | Proposition 9.3, proof | colon after «step 1 reads» dropped | yes (display) |
| 702 | Corollary 1.6, proof step 3 | «. And `g(n − 2) = G`, because» → «, which is `G` because» | yes (part 11, «reworded with the same content») |
| 730 | Corollary 10.2 | the statement reordered: quantifier first, formula displayed | yes |
| 758 | Lemma 10.4(b), proof | «, `u_f` odd» → «, where `u_f` is odd» | yes |
| **821** | **Lemma 10.10** | **«For every `L ≥ 0` and every floor `f`,» added** — a quantifier made explicit. Correct and harmless, but it is a change of statement wording, not of layout | listed only as «display» |

**Verdict on item 11:** no presentation hunk changes a symbol or a number; none changes the mathematics. Two hunks change words beyond what the author's list says: Lemma 3.5 (unlisted rewording) and Lemma 10.10 (an added quantifier, listed only as a display). **PRESENTATION (record):** add both to `CORRECTIONS_v2_to_v3.md`.

## 4. The pdf, page by page (summary; the full list is `checks/PAGES.md`)

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


## 5. The pdf, the other checks (§3 items 2–12)

Every check below was run under the watchdog; scripts in `checks/`, logs in `logs/`, the bbox file in `scratch/v3_bbox.html`.

**Item 2, margins — HOLDS.** `checks/margins.py` (`logs/margins.log`): the body right edge is 542.0 pt (879 lines end there); the largest `xMax` in the paper is 541.95 pt (p17, «the»); **no word passes 542.5**. Left edge 54.3 pt; page 594.96 × 841.92 pt (A4).

**Item 3, loose lines — the author's figures are confirmed, and the measure is blind to half of the problem.** `gaps_text_words.py` (read first: it averages only the gaps between two plain words, regex `W`, on full justified lines) gives on the v3 bbox: 723 lines; mean gap > 5 pt: 51; > 6 pt: 13; **> 7 pt: 1 (7.4 pt, p14); > 8 pt: 0** — exactly as the author says. `gaps_all.py`: 727 lines, mean > 5: 69, > 6: 17. But (a) the one line above 7 pt is **visible to the eye** (§4, row 3; zoom `scratch/z/p14_loose-14.png`); and (b) the tool cannot see the stretch that goes **inside formulas**, which is the commoner fault here (§4, G6; visible on p19, p20, p29, p40 at 200 dpi). My attempt to measure it automatically (`checks/gaps_inside_formulas.py`) is **not usable**: `pdftotext` extracts sub- and superscripts and the limits of `Σ` as separate words at other heights, which leaves false «gaps» of 20–30 pt where the indices sit. I report the visual instances only.

**Item 4, formulas — DEFECTS.** `checks/formula_lines.py` (`logs/formula_lines.log`) lists the lines of the pdf that begin with a relation or a binary operator, consist of a relation alone, or end with a word that should not end a line. Confirmed at 200 dpi: lines beginning with «+» (p19), «≥» (p27), «≤» (p29, twice), «≡» (p38); line ends «min» (p20) and «step» (p28). No relation or «= 0» alone on a line; no proof mark alone on a line. Also: displays wrapped by the renderer with the continuation centred (p15, p16); breaks between «]» and «[» (p36, p38); an inline formula split across a page break (p11→12). Long formulas are generally displays; the exceptions are the lines of G6.

**Item 5, structure — DEFECTS.** `checks/structure.py` (`logs/structure.log`): of 68 numbered statements, **five run across a page break** — Propositions 4.2 and 5.4 (found by the script), Lemmas 7.3, 7.6, 10.20 (seen on the pages). Headings at the foot: §4.4 (p16) has one line under it; §2.2, §3.3, §10.3, §10.5 have two lines or more (acceptable). `checks/widows.py`: one widow (top of p21); no orphan. Tables: no row is split, headers repeat on continuations, no table overflows the margin; the §12.1 table is badly balanced (§4, rows 24–27).

**Item 6, the two accepted blanks — both TO BE FIXED.** p7: §1.7 could start on p7 (§4, row 1). p41: the blank comes from the unbalanced §12.1 table (§4, rows 24–25). A third one, not mentioned by the author: p20 (§4, row 12).

**Item 7, fonts and glyphs — HOLDS, one minor note.** `pdffonts` (`logs/pdffonts.log`): 125 font objects, **all embedded and subset** — STIX Two Text (regular, italic, bold, bold italic), STIX Two Math, STIX General (regular, bold; fallbacks), Menlo (code). All are Type 3 (Chrome/Skia output): fine on screen, less crisp in print, and refused by some journal systems; re-export with OpenType/CID fonts if the pdf is to be printed or submitted. No missing-glyph box: the four «□» of the text are the box product of §11 item 2. `𝟙`, `𝔅`, `𝔡`, `𝒜`, `𝒦`, `𝒮`, `Ξ`, `Θ`, `Γ`, `η`, `ŷ`, the arrows and the scripts all render.

**Item 8, md and pdf say the same — HOLDS.** `checks/md_vs_pdf.py` (`logs/md_vs_pdf2.log`): every number of the five tables (§1.0, §1.6, §1.7, §12.1, §12.2) is present in the pdf text of the same section with at least the same multiplicity; the prose of all 68 numbered statements appears in the pdf in order (four apparent misses were artefacts of the extraction — a word split by a superscript, «ob-…-tains» — and were found by a second search). No difference.

**Item 9, cross-references and citations — HOLDS, one inexact pointer.** `checks/xrefs.py` (`logs/xrefs.log`): every internal «Lemma / Theorem / Proposition / Corollary x.y», every lettered theorem (D, O = 6.2, U = 7.4, F = 7.8, DW), Lemma W = 3.2, Lemma K = 9.5, and every «§x.y» exist. External items checked in `material/sources/`: [Bai03] Theorems 1.1–1.3; [GMMY24] Propositions 1.9, 2.5, 2.12, Remark 2.13 (quotation exact), Theorems 4.1, 4.2, Conjectures 4.14, 5.4; [IKKY23] Proposition 37; [CSX17] §5.2 (quotation exact); [Aky26] (report §1.9). 32 keys in the list, 32 cited, none missing either way, no duplicate, alphabetical. **PRESENTATION:** §1.4 item 1 (md line 133) cites «the change of variables `u_i = x_i − 1` of [GMMY24, Proposition 2.5]»; the change of variables is in the *proof* of Proposition 2.5 (its statement is about multiplicities), as §2.1 (md line 225) correctly says; and `s_S = ∏(1 − x_i)` is that change up to the sign `(−1)^{|S|}`. Web checks (`checks/QUERIES.md`): the DOI of [GMMY24] resolves (302 to tandfonline.com); OEIS A193134 is «Numbers of spanning trees of the folded cube graphs», 1, 16, 4096, …, so the paper's caveat about `n = 2` (K₂ against a double edge) is right. All nine arXiv numbers are well formed and match the sources.

**Item 10, file names and code — one minor defect.** No code or file name is hyphenated; the path «`remark2/gate_remark2.py`» is broken at its slash in the §12.1 table (§4, row 27).

**Item 11, references — consistent, with five minor inconsistencies.** (a) only [GMMY24] gives an issue («no. 10») and a DOI; (b) the key [GMM19] reads as Gao first, while the entry (rightly) keeps the poster's order Marx-Kuo, Gao, McDonald (`material/sources/GaoMarxKuoMcDonald_JMMposter2019.txt`); (c) [DEGJPP24] dates arXiv:2310.09227 «(2024)», the date of its v2 — write «v2» or «(2023)»; (d) [OEIS] has no access date; (e) [Yue24] alone gives an issue, «31(1)». The bibliographic data I could check are right: the authors and titles of the fourteen papers whose text is in `material/sources/` (first pages read), and, from memory only, the journal data of the classical entries.

**Item 12, metadata — one minor defect.** Title «The Dancing Sand Theorem» ✓, 47 pages ✓, A4 ✓, tagged. No Author field, although the paper has one: add «Rafael Amichis Luengo» (and the subtitle as Subject).


## 6. The author's gates and builder (§5)

Opened only after §1–§5 were written (diary, entry «OPENING material/read_after/»).

**`gate_strict_cut.py` — checks what §12.1 says; its controls can fail; its numbers and mine agree exactly.** Read whole. Over every house with `k ≤ K_MAX`, every `I`, every `ℓ`, `α ∈ {1, 2, 3}` it computes the real fit with exact fractions and checks: the strict drop of the fit at the boundary `b` of `J_H` and at its mirror (with §7.1, «a strict drop of the fit is a cut», this is strict (Cut)); the penalty shifts `P_r, P_c ≤ P_MAX` (integer fit, real fit and level sets shift exactly); the deletion of `∅` in the house `ℓ = 2^k − 1`; and integrality of every fit (Lemma 7.9). Run under the watchdog (`logs/author_gate_strict_cut.log`, `6 4`, 40 s): 16 380 houses, 8 001 boundaries, 192 024 shifts, 360 deletions, 0 failures; controls: strictness one dancer later fails in 1 911 of 7 038, the shift one dancer late in 18 606 of 192 024, `x_H + e_0` non-integral in 1 942 houses; the reader's counterexample `(3,4,3,4)` shows the integer shift failing at a non-strict cut. **Every number of the two §12.1 rows reproduces.** My own gate at the same range (`logs/gate_cold5_k6.log`) gives the same 16 380 / 8 001 / 192 024 / 360 / 1 942 / 1 911 of 7 038, by independent code (integer block sums, and an explicit cut test, not only a strict-drop test). At `k ≤ 7` my numbers are exactly reader 4's (§12.2). The controls are real: each negates something one would be tempted to believe and fires. One remark: the strictness check alone does not test that the fit is cut at `b`; it relies on §7.1 for that — legitimate, since §7.1 is proved, and my gate tests the cut directly (0 failures).

**`gate_sections5to7.py` — checks what §12.1 says; its controls can fail; two rows of §12.1 under-describe their range.** Read whole. Run under the watchdog: the fixed part (`logs/author_gate_s57_fixed.log`, 11 s) and the houses at `λ ≤ 127, α ≤ 3` (`logs/author_gate_s57_full.log`, 57 s). All printed numbers reproduce: Proposition 5.2 109 200 entries, 5.3 14 560, 5.4 301, 0 bad; Theorem 7.10 1 638 cells, 0 bad, raw clocks rejected in 322 of 322; Theorem 7.8: 48 006 house-checks (16 002 houses × three prices `lo`, `hi`, `mid`), 0 failures in (E), (M), (G), the cut, the bound `|ŷ| ≤ α(2^k − 1)`, the integer separation, and the walk of step 1 (139 266 recursive calls), and no empty price interval; controls: without gold (G) fails in 164 houses, with `c_F := v'(I')` in 24. Findings:
1. The code confirms my inference of §1.10: Propositions 5.2–5.4 are checked at `λ < 64`, **`i = 1, …, 40`** (5.2 at `α = 1, 2`; 5.3 at `α = 1`) and `i = 0`, `α = 1` (5.4). The range column of §12.1 says only «`λ < 64`». PRESENTATION.
2. «`k ≤ 6` (`λ ≤ 127`)»: 127 is the command-line bound; `λ = 127` has `I = ∅` and gives no house, so the last `λ` with a house is 126. PRESENTATION (as §1.10).
3. Proposition 5.2 is checked against `closedM` (the closed form of Theorem 4.4, from `gate_dance.py`), not against the dance itself; the dance is checked against the closed form in `gate_dance.py` (row 2 of §12.1). The chain is complete, but the row could say «against the closed form of Theorem 4.4».
4. The file also counts golden bijections for `|I| ≤ 3` plus six sets (61 cases); §12.1 rightly cites `gate_theoremO.py` (69 cases) for Theorem 6.2.

**The builder (`md2html.py`, rules (1)–(26), and `build_v3.sh`).** For each pdf defect of §4, the rule that should have prevented it, or the rule that is missing:

| defect (§4) | rule | diagnosis |
|---|---|---|
| G1, G5, G7 (italic digits, brackets, operator names, words) | none | every code span is set in one italic font; a math renderer (or a class per token: digits, brackets, operator names and words upright) is missing |
| G2 (scripts not stacked) | none | HTML `sup`/`sub` cannot stack; needs MathML `msubsup` or KaTeX/MathJax |
| G3 (bold formulas) | none | the md bold is passed into formulas; missing: no bold inside math |
| G4 (no quad between formulas) | (19) | (19) allows the break at the comma but adds no space; missing: a quad |
| G6 (stretch inside formulas) | (13), dropped | (13) was dropped «after measuring», with the measure `gaps_text_words.py`, which averages only gaps between two plain words — **it cannot see the stretch that dropping (13) lets into the formulas**. TeX's math glue does stretch, but by at most 2 mu (medium) and 5 mu (thick) per space, far less than the two to three times normal seen here. Missing: a limited stretch inside formulas, measured with a tool that sees math gaps |
| G8 (upright `i` in italic labels) | (11) | italic inside italic toggles to upright; missing: math inside an italic label stays italic |
| 1 (p7 blank) | (22) + `p:has(+ table)` in `build_v3.sh` | the rule «a table never leaves fewer than three rows at the foot of a page», chained with the keep of the introduction and the heading, pushes all of §1.7 to p8; acceptable to relax to two rows here |
| 2 (formula split across a page after «=») | (14), (16) | they allow a break after a relation, also at a page break; missing: no page break inside an inline formula (or display it) |
| 3, 8 (p14 loose; p19 line starting with «+») | (14) | **likely mechanism (consistent with the html and with UAX #14; not tested by a rebuild):** the html has `|D|&nbsp;+ s_2(ξ)`; rule (14) puts the no-break space before the operator, but the ASCII bar `|` has Unicode line-break class BA («break after»), and a break is allowed between a BA character and a following no-break space (UAX #14, LB12a). So every `|…|` in a formula is a hidden break point. Missing: use `∣`/`‖` or wrap `|…|` in a word joiner |
| 4, 5 (displays wrapped, continuation centred) | none | a display wider than the measure is wrapped by Chrome and centred; missing: the builder should fail (or warn) when a display does not fit one line, so that it is broken by hand |
| 6, 10, 13, 14, 23 (statements split) | (22) | (22) keeps *blockquote* statements together (Main Theorem, Theorem D, DW, Corollaries 1.4–1.7); the numbered lemmas and propositions are plain paragraphs and are not covered. Missing: keep a statement (label to proof) together |
| 7 (heading with one line) | none | missing: a heading keeps two lines of what follows |
| 9 (`Σ h_t = 0.` alone) | (24) | (24) protects «= 0» after a relation inside one formula; here the whole short formula is the last line. Missing: no paragraph ends with a line holding only a short formula |
| 11 (`min` / `D`), 17 (`step` / `1`) | (10) | (10) joins «Theorem O», «Lemma 7.2» and the like; missing: operator names (`min`, `max`, `mod`, `dim`, `rank`, `log`) and «step n», «case n», «item n» |
| 12 (widow in a list item) | none | missing: widow and orphan control for list items |
| 15 (lead-in separated from its display) | none | missing: keep a paragraph ending in «:» or «,» with the display that follows |
| 16, 18, 19, 22 (lines starting with `≥`, `≤`, `≡`) | (14) | (14) works *inside* a formula; here the code span itself begins with the relation («numbers `≥ 2`», «is `≤ max…`», «which is `≡ 0 (mod 4)`»), so the break is in the text before the span. Missing: a span that begins with a relation is joined to the preceding word by a no-break space |
| 20, 21 (break between «]» and «[») | (23) | (23) forbids only «)(»; missing: no break between any closing and opening bracket |
| 24–27 (§12.1 table) | (9), (25) | (9) fixes the column widths of this table, and the chosen widths make «result» too narrow; (25) protects file names «without /», so the path `remark2/gate_remark2.py` is not protected. Missing: better widths; extend (25) to paths |
| 28 (bulleted references) | (26) | (26) sets the size and the ragged right; missing: a hanging list without bullets |
| metadata (no Author) | — | the builder passes only the title (`argv[3]`); missing: the author |
| p6 «cheapest `r`-» / «matching» | (15) | (15) protects «-th» only; extend to every compound «formula-word» |


## 7. Sealed predictions, hits and failures

All in `checks/SEALED.md`, sealed with the time from `date` before the corresponding run; scores written after the runs.

| # | prediction (short) | odds | result |
|---|---|---|---|
| S1 | every house fit integral, `k ≤ 7`, `α ≤ 3` | 97 % | HIT (65 532 houses) |
| S2 | penalty cells and deletions integral | 97 % | HIT (192 024 cells, 741 deletions) |
| S3 | strict cut at the boundary and its mirror | 97 % | HIT (32 385 houses) |
| S4 | raw clocks of §1.2 have integral level sets, `λ ≤ 255`, `i ≤ 40` | 95 % | HIT (10 455 cells) |
| S5 | Propositions 5.3 and 5.4 from the definitions | 96 % | HIT (0 mismatches) |
| S6 | Proposition 9.6 (H): the head is `{D ⊆ P_l}` | 93 % | HIT (10 200 cells) |
| S7 | control: `x_H + e_0` non-integral somewhere | 95 % | HIT (1 942 of 16 380) |
| S8 | control: random antisymmetric sequences non-integral ≥ 10 % | 85 % | HIT (3 299 of 10 000) |
| S9 | control: strictness one dancer later fails somewhere | 92 % | HIT (7 967 of 30 078) |
| S10 | a head ending at a non-dyadic boundary | 55 % | **FAILED** (0) — ill-posed: it contradicts S6, as I recorded before the run |
| S11 | a house whose fit is identically 0 | 70 % | HIT (949) |
| S12 | a level set of length ≥ `2^{k−1}` | 75 % | HIT |
| S13 | the jump moved one dancer later makes a head non-dyadic | 65 % | **FAILED** (0 of 2 084) — ill-designed: the head never reaches past a jump (S15), so moving the jump later cannot touch it |
| S14 | the boundary position is not a power of 2 somewhere | 97 % | HIT (1 734 of 2 572) |
| S15 | the head reaches a jump of the penalty shift somewhere | 50 % | HIT (1 034 of 2 572; never past it) |

**Marker: 13 hits, 2 failures.** Both failures are mine, in the design of the bets. The real risks were S10–S13 and S15; of these, S11, S12 and S15 hit. **The pdf measurements of §5 carried no sealed prediction** (see §8).



## 8. My errors

1. **The page look at 90 dpi missed nine defects** that the scripts of §5 found and the 200-dpi zooms confirmed: the loose line of p14, the splits of Propositions 4.2 and 5.4, the line beginning with «+» on p19, the widow at the top of p21, and the lines beginning with «≥» (p27), «≤» (p29, twice) and «≡» (p38). I had written «p. 21 — OK»; corrected in the ADDENDA of `checks/PAGES.md`. Lesson: a page look at 90 dpi finds layout, not the start of a line.
2. **No sealed prediction for the pdf.** The mission asks to seal every prediction before measuring; I sealed none for §5 (margins, loose lines, formula lines, splits). The numbers there are measurements without a bet.
3. **S10 ill-posed and S13 ill-designed** (§7), both recorded before scoring.
4. **The diff showed me the proof of Lemma 7.9 before I proved it** (Part 1); my derivation in §1.1 is in my own words but not blind (stated at the top of §1).
5. **An automatic measure that does not work:** `checks/gaps_inside_formulas.py` reports false gaps of 20–30 pt where `pdftotext` takes the indices and the limits of `Σ` out of the line. I did not use it as evidence.
6. **A sloppy assertion** in the first version of `tool_controls` of my gate (`… is True or True`), replaced by a real check before any result was used.
7. Two small slips in my notes, corrected before they reached the report: the line beginning with «≡» on p38 is in the proof of Lemma 10.18 (I first wrote 10.19), and the line on p27 is in the proof of Lemma 9.1.
8. A first `python3` edit of the report failed on unescaped quotes (nothing was written); redone from a file.



## 9. What I did not read

- **Not read:** the statements that did not change in version 3, except where a changed item depends on them (mission §4); the Main Theorem against the graphs (mission §4).
- **Cited papers:** I checked the cited items, the three quotations ([Aky26], [GMMY24] Remark 2.13, [CSX17] §5.2) and the authors and titles of the fourteen papers whose text is in `material/sources/`; I did **not** read them in full, and the journal data (volume, pages) of their published versions are not in those texts. The data of the other eighteen references ([ABERS55], [BBBB72], [Bie93], [Big99], [Cla40], [Don93], [EL91], [Hum72], [Jan03], [Kli18], [Kos66], [Kum52], [Lor91], [Str28], [TW21], [vSt40], [Wil90]; [OEIS] was checked on the web) were checked against my memory only, not against a source.
- **The pdf:** every page at 90 dpi; 200 dpi only in the doubtful regions and in the regions flagged by the scripts — not every page at 200 dpi. The html was looked at only for one formula.
- **The other gates** (`gate_dance.py`, `gate_direct.py`, `gate_lemma72.py`, `gate_section9.py`, `gate_section10.py`, `gate_theoremO.py`, `remark2/`, `rule_abs.py`): not read and not run (outside mission §5).
- **The web:** only the DOI of [GMMY24] and OEIS A193134 (`checks/QUERIES.md`).
- **Version 2:** read only through `DIFF_v2_to_v3.txt`; its pdf was not compared page by page with version 3.


## 10. Files with md5

The complete list — 145 files: 13 scripts and records in `checks/`, 33 logs in `logs/`, the 47 page renders `scratch/p90/`, 39 zooms `scratch/z/`, and 13 notes and extractions in `scratch/` — is `checks/MD5_FILES_WRITTEN.txt`, md5 `c9717e23a415b57b7dfef75808aa4596`. Not listed there, because they change after this line: `REPORT_COLD_5.md` (its md5 is the last line of `logs/DIARY.md`), `logs/DIARY.md` and `ESTADO.md` (living files).

The main files:

| md5 | file |
|---|---|
| `0345f371e692f1e7af136e3d61036aef` | `checks/PAGES.md` |
| `6d6723f7accc1a8293dea37c138ce7c4` | `checks/QUERIES.md` |
| `08220161d3c47ace11799f44302cc889` | `checks/SEALED.md` |
| `ad637dd5ae0ea7c82966e4796be996d5` | `checks/formula_lines.py` |
| `a4acb1ca6c18f3448149bdfff0257ff6` | `checks/gaps_inside_formulas.py` |
| `b1d349a71e2a0514faac435e4c42f86d` | `checks/gate_cold5.py` |
| `1ad5ec06a21d770b35c27bcac4d813d3` | `checks/head_vs_jump.py` |
| `018f95e4445fd0104b1ac8d3e0dc4f73` | `checks/hunks_normalized.py` |
| `1dd4e8b726fc88ebe0752955c61b6d82` | `checks/margins.py` |
| `e614f0b0bfb056e8f52c59c5ec011d39` | `checks/md_vs_pdf.py` |
| `c810a6f2b658ca64af2ef573a76e0cf0` | `checks/structure.py` |
| `4f544c1310519eb2c659be052733ffa1` | `checks/widows.py` |
| `f47fd32d6c989dafa5683dab252d6737` | `checks/xrefs.py` |
| `c19c2199e4acc646c387b7616b10e39a` | `logs/author_gate_s57_fixed.log` |
| `ed662ca551a99e5363b164d5541aafd7` | `logs/author_gate_s57_full.log` |
| `4ebefe3c0109cc6e26aa8f114f720fa3` | `logs/author_gate_strict_cut.log` |
| `37dce948b27891ddec77d8ec8b081fbe` | `logs/formula_lines.log` |
| `1cc95ac554752cf60119107722c04259` | `logs/gaps_text_words.log` |
| `b1cad51a29852b492d1f8ee86a3abddc` | `logs/gate_cold5_full.log` |
| `45e1628d0379c1c2a4b371a6db479160` | `logs/gate_cold5_k6.log` |
| `520e525b9e4a8063432e61b4bdd94f15` | `logs/head_vs_jump.log` |
| `726a50f30e25b86e35d8bbc7a261fc37` | `logs/hunks_normalized.log` |
| `c5158d6b60dda10475a9f26cae0f3d53` | `logs/margins.log` |
| `c42632bd5651992ef5d89c80b9c46862` | `logs/md_vs_pdf2.log` |
| `525da27c6feb3a16aa2bda5e8a501d0f` | `logs/pdffonts.log` |
| `040d83ec2a8c3008075660950c8d13a6` | `logs/pdfinfo.log` |
| `2bfa27553431138004577905c4cb9193` | `logs/structure.log` |
| `70adf470280acf527898a3e1270053e5` | `logs/widows.log` |
| `69c7a741db1648499fe912bd0287fdba` | `logs/xrefs.log` |
| `8f2104723ef500c7ffc1138673610c76` | `scratch/part1_notes.md` |
| `8479974a7e2b43104114fd1246d2238c` | `scratch/sec5_notes.md` |

Material: every file of `MANIFEST_at_launch.txt` (54 entries: `material/`, `MISSION.md`, `vigia.sh`) still has its md5 at the end of the reading; the one «changed» entry is the manifest itself, which lists its own md5 as that of the empty file (`d41d8cd9…`, computed while it was being written). Nothing in `material/` was modified.

— Grepy Muchas Pilas, cold reader 5
