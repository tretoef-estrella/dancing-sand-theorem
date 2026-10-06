# REPORT_COLD — cold reading of the changes of version 2 of «The Dancing Sand Theorem»

Reader: «Grepy el lector frío del cubo 4». Started 2026-10-05.

## 0. First line

- **Do the changes hold as written: HOLDS WITH GAPS.** The repair holds: I re-derived the restated Lemma 7.2(b), the counterexample, strict (Cut) in every case of step 3, and its uses in Lemma 7.9, Theorem 7.10 and Proposition 9.6 (§1), and checked them by machine on 65 532 houses (`k ≤ 7`, `α ≤ 3`) and against the true Smith form of `M(λ, i)` in 7 874 cells (`λ ≤ 127`, `i ≤ 30`), with controls that fire (§2). No statement of a theorem changed; every renaming and cross-reference is clean; every quotation is verbatim; the four references are right (§3, §4). What keeps it from a plain «holds»: **one false sentence** in the rewritten Remark (2) of §10.5 («every payment system dances clean, whatever its payments» — it must say *even*; the remark is used nowhere, §3.3), and points of presentation, the substantive ones being: §13 grades as «read cold» results whose proofs now contain the not-yet-read repair (§3.0); the cases (a)–(d) of the strict (Cut) proof are one unbroken block in the pdf (§5); two rows of §12.1 state more than their code (393 120 shifts of which 201 096 are zero vectors; «1 550 cells» on a range wider than run) and the strict-cut row's control does not control the house check (§6). **New observation (§2.5):** in every house the real antitonic fit is already integral (a two-line induction), so the v1 integer claim was true wherever it was used and the repair could be shorter; the paper should say so.
- **Is version 2 ready for publication: AFTER CORRECTIONS** (all minor: one word in Remark (2), the §13 wording, the layout of step 3, two rows of §12.1, the optional integrality remark, and the small items of §3–§5). Beyond this reading, the paper itself says it still lacks a human referee.

## 1. The repair as I read it (§2 of the mission, item by item)

Line numbers are those of `THE_DANCING_SAND_THEOREM_v2.md`. «I re-derived» means: I wrote the step again myself, from the definitions of §5 and §7, before looking at the next sentence of the text.

### 1.1 §7.1: strict cuts and Lemma 7.2 (l. 522–529)

- **Definition of a strict cut (l. 522).** «Cut at `b` (`0 < b < N`)» now has its range; «strict» = `fit(x)_{b−1} > fit(x)_b` = no level set contains both `b − 1` and `b` (the two are equivalent because `fit(x)` is non-increasing and level sets are maximal runs of equal values). **HOLDS.**
  Remark: a position that no level set crosses is automatically a cut (Lemma 7.1 is a condition on each level set separately, so the restrictions of `fit(x)` to both sides satisfy it for the two pieces). The text uses this silently twice: in «that is» and in «a strict cut stays strict» (l. 529, where one must know that `x + δ` is still *cut* at a strict cut `b` of `x` that is not among the listed `b_j`). One line would close it. **PRESENTATION (minor).**
- **Lemma 7.2(a), (c)** unchanged; not re-graded (they are used below; I re-checked (c) in passing: correct).
- **Lemma 7.2(b), real part** (unchanged): **HOLDS** (I re-derived it: the multi-cut concatenation follows from two-cut concatenations by (c); each piece shifts by a constant; (a) re-glues).
- **Lemma 7.2(b), restated integer part (l. 526).** My own proof: let `δ` be integer, non-increasing, constant on every level set of `z = fit(x)`. Then `z + δ` is non-increasing, and adjacent level sets with values `μ_A > μ_B` get `μ_A + δ_A > μ_B + δ_B` (as `δ_A ≥ δ_B`), so the level sets of `z + δ` are those of `z`; Lemma 7.1 is invariant under adding a constant on a level set, so `fit(x + δ) = z + δ` (this even dispenses with the cut hypothesis: a `δ` constant on level sets only changes at strict cuts). On a level set of `p` positions and sum `S`, the integer fit of `x + δ` uses `S + pδ_L`, whose residue mod `p` is that of `S`, and `⌈(S + pδ_L)/p⌉ = ⌈S/p⌉ + δ_L`, same for `⌊·⌋`. So the integer fit shifts by `δ`. And a level set never straddles a strict cut, so «changes only at strict cuts» ⟹ «constant on every level set». This is the text's proof. **HOLDS.**
- **The counterexample `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)` (l. 529).** By hand with PAVA: `fit(x) = (7/2)^4` (prefix sums of `x − 7/2`: `−1/2, 0, −1/2, 0`); `fit(3, 4) = fit(3, 4) = (7/2, 7/2)`, so `x` is cut at `2`, not strictly. `δ` is integer, non-increasing, constant between the cuts of `x` (the only cut is at `2`: at `1` and `3` the concatenations `(3, 4, 7/2, 7/2)`, `(7/2, 7/2, 3, 4)` are not the fit). `x + δ = (4, 5, 3, 4)`, fit `(9/2, 9/2, 7/2, 7/2)` = `fit(x) + δ` (the real part holds), integer fit `(5, 4, 4, 3)`; integer fit of `x` is `(4, 4, 3, 3)`, plus `δ` gives `(5, 5, 3, 3)`. All four numbers in the text are right, and the example shows exactly what the text says: the v1 integer claim (with only «constant between consecutive cut positions») is false, and the new hypothesis is not met (`δ` is not constant on the level set `{0, 1, 2, 3}`). **HOLDS.**
- **Does (b) say what its uses need, and no less?** I listed every use and what each needs:
  1. Theorem 7.8 step 1 (l. 598): real fit `fit(x_{H'}) + d_1` *with the same level sets*, integer fit `ŷ' + d_1`. Given by (b). ✓
  2. Theorem 7.8 step 3(c) (l. 604): same for `x_{H'} + d_2`. ✓
  3. Lemma 7.9 (l. 630): level sets kept and shifted by integers. ✓
  4. Theorem 7.10 (U2) (l. 634): integer fit shifted by the penalty. ✓
  5. Proposition 9.6 (H) (l. 691): the level sets (in particular the first one) are kept. ✓
  The deletion at `i = 0` (Theorem 7.10, Lemma 7.9) is not an application of (b) but of «a level set by itself can be removed» (again Lemma 7.1 locality). The conclusion «strict cuts of `x` are strict cuts of `x + δ`» is used nowhere that I can find; harmless. **(b) says what is needed, not less. HOLDS.**

### 1.2 Theorem 7.8: strict (Cut) and its proof (l. 593, 596–606)

- **`b ≠ ∅` (l. 593).** `J_H(∅) = [ℓ + 0 ≥ 2^k] = 0` because a house has `ℓ < 2^k`. So the first dancer with `J_H = 1`, if any, has position `≥ 1`, the cut position is in `(0, N)`, and so is its mirror `N − pos(b)`. In case (c) the same argument gives `b' ≠ ∅` for `H'`. **HOLDS.**
- **Step 1 (l. 598) and the induction.** The induction is on `|I|`, and the statement proved for `H` includes strict (Cut) and (Λ); step 1 uses them for `H'` only. Where `d_1 = −τ − [T = 1]κJ'(D_0) + [T = 0]κJ'(I' ∖ D_0)` changes: for `T = 1` at the position of `b'` (first dancer with `J' = 1`), for `T = 0` at the position `N' − pos(b')` (the mirror, since `J'(I' ∖ D_0) = 1 ⟺ pos(D_0) ≤ N' − 1 − pos(b')`). Both are strict cuts of `x_{H'}` by the induction hypothesis (the second by antisymmetry). `d_1` is integer and non-increasing. So Lemma 7.2(b), restated, applies exactly. No circularity: (Cut) for `H` is proved in step 3 from step 1 and (Λ) for `H'`. **HOLDS.**
- **Case (a)** `T = 1`, `sat = 1`, `J' ≢ 0` (l. 602). Re-derived: `κ = h`, `τ = h − α2^c − h = −α2^c`, `d_1 = α2^c − hJ'`. At `b^−` (exists since `b = b' ≠ ∅`), `X_1(b^−) = ŷ'(b^−) + α2^c ≥ −α(2^c − 1) + α2^c = α ≥ 1`; an integer-fit value `≥ 1` forces the real value of its level set to be `> 0`, so `Z_1 > 0` on `[0, b)`. Cut: `fit(x_H)_{<b} = max(Z_1, 0)_{<b} = (Z_1)_{<b} = fit((x_H)_{<b})` (the first half `x_{H'} + d_1` is cut at `b` by (b)), then (c). Strict: `Z_1(b^−) − Z_1(b) = [fit(x_{H'})(b^−) − fit(x_{H'})(b)] + h ≥ h ≥ 1`, and `Z_1(b^−) > 0`, so `max(Z_1, 0)` drops strictly (whether `Z_1(b)` is positive or not). **HOLDS.**
- **Case (b)** `T = 1`, `sat = 1`, `J' ≡ 0` (l. 603). `J_H = (0, 1)`: the boundary is `{c}`, position `N'`. `d_1 ≡ α2^c`, `X_1(I') ≥ α`, so `Z_1 > 0` on the whole first half, `fit(x_H)_{<N'} = Z_1 = fit(first half)`, cut by (c). Strict: `fit(x_H)(I') = Z_1(I') > 0 ≥ min(Z_2({c}), 0) = fit(x_H)({c})`. **HOLDS.**
- **Case (c)** `T = 0`, `sat = 1` (l. 604). Re-derived: `τ = h − α2^c`; second half `= x_{H'} + d_2`, `d_2 = τ − κJ'` (I checked `d_2` is the mirror-negative of `d_1` and that `X_2 = ŷ' + d_2` agrees with the mirror-negative of `X_1`). `X_2` at `b' ∪ {c}` is `ŷ'(b') − α2^c ≤ −α ≤ −1`, so the real value there is `< 0`, and `Z_2 < 0` from `b' ∪ {c}` on; cut by (c) (second form). Strict: since `b' ≠ ∅`, the dancer before `b' ∪ {c}` is `(b')^− ∪ {c}`, in the second half; `Z_2 = fit(x_{H'}) + d_2` drops there by `≥ κ = h ≥ 1` and is negative at `b' ∪ {c}`, so `min(Z_2, 0)` drops strictly. **HOLDS.**
  Presentation: case (c) is headed «`T = 0`, `sat = 1`» without «`J' ≢ 0`»; if `J' ≡ 0` then `b'` does not exist, `J_H ≡ 0`, and the situation belongs to (d). Add «`J' ≢ 0`» to the head of (c). **PRESENTATION (minor).**
- **Case (d)** (l. 605). By Lemma 7.7 both halves of `J_H` carry the factor `sat`, so `sat = 0` gives `J_H ≡ 0`; and `T = 0`, `sat = 1`, `J' ≡ 0` gives `J_H ≡ 0`. These are all the remaining cases. **HOLDS.**
- **The mirror by antisymmetry (l. 606, l. 531).** `x_H` antisymmetric ⟹ `fit(x_H)` antisymmetric; `fit(N − b − 1) = −fit(b)` and `fit(N − b) = −fit(b − 1)`, so a strict drop at `b` is a strict drop at `N − b`. **HOLDS.**
- **Verdict on Theorem 7.8 (Cut), strict:** every case proved; I found no missing step beyond the two minor presentation points above. **HOLDS.** Machine check in §2.3.

### 1.3 Lemma 7.9 (l. 628–630)

- The claim «a non-increasing integer shift that is constant on every level set preserves the property» is exactly what step 1 + Lemma 7.2(b) give: the level sets of `fit(x_{H'})` are kept and shifted by integers `δ_A ≥ δ_B`, and `⌊μ_A + δ_A⌋ = ⌊μ_A⌋ + δ_A ≥ ⌈μ_B⌉ + δ_B = ⌈μ_B + δ_B⌉`. (The one-line computation is not printed; it is immediate.) ✓
- **Gluing (Lemma 7.3).** Level sets of `fit(x_H)`: the positive level sets of `Z_1` (property inherited), the central set (value `0`; `⌊μ_A⌋ ≥ 0` for `μ_A > 0` and `0 ≥ ⌈μ_B⌉` for `μ_B < 0`), and mirrors (the property is symmetric under `μ ↦ −μ`: `⌊−μ_B⌋ = −⌈μ_B⌉ ≥ −⌊μ_A⌋ = ⌈−μ_A⌉`). ✓
- **The junction case** (no central set, i.e. `Z_1 > 0` on the whole first half): the two adjacent level sets have values `μ > 0` and `−μ`, and `⌊μ⌋ ≥ 0 ≥ ⌈−μ⌉`. ✓ (The text writes «`μ ≥ 0`»; here `μ > 0`, harmless.)
- **Penalty shifts.** `−P_r J_H(D) + P_c J_H(I ∖ D)`: the first term is non-increasing and changes at `b`, the second is non-increasing and changes at `N − pos(b)`; both are strict cuts by (Cut). ✓
- **Deletion at `ℓ = 2^k − 1`.** For `H^♯ = (I, k, 2^k − 1, α)`, `J(E) = [o_E ≥ 1] = [E ≠ ∅]`; the first dancer with `J = 1` is `{t_1}` at position `1`; the strict cut there makes `{∅}` a level set by itself; removing it leaves the other level sets and their adjacencies unchanged. ✓
- **Verdict: HOLDS.**

### 1.4 Theorem 7.10 (l. 632–635)

- **(U2) for `i ≥ 1`.** By Lemma 7.5, `x_D = x_H(D) − P_r J_H(D) + P_c J_H(I ∖ D)` (I re-derived it from `R_m = R_H − P_r J_H`, `R_{m+K} = R_H − P_c J_H`). The penalty shift is integer, non-increasing, and changes only at `b` and its mirror, both strict cuts of `x_H` (Theorem 7.8 (Cut)); Lemma 7.2(b) gives integer fit `= ŷ_H + shift = v(D) − w(I ∖ D)`. (U1) from (M) and `J_H` an up-set; (U3) from (G), with equality on loops (`γ(∅) = 0`). **HOLDS.**
- **The case `i = 0`.** Row `∅` vanishes (window `[0, K − 1]` contains `d = 0`), and every window of a row `D ≠ ∅` starts at `o_D ≥ 1`, so every supported entry of `M^♯` is non-zero. `R^♯ = R_{H^♯}` with `ℓ = K − 1`. The strict cut at `{t_1}` isolates `∅`, so the real *and* integer fits of `x^♯` (length `N − 1`) are the restrictions of those of `x_{H^♯}` — and strictness is genuinely needed here: without it the level set of `∅` could spill into position `1` and the integer fit of the shortened sequence would differ. For `r ≤ N − 1`, `L_r ∌ ∅` and `F_r ∌ I`, so Lemma 6.1, Theorem O, Corollary 6.3 (with `U^♯`), Lemma 6.4 (with the level sets of `x^♯`) and Theorem 7.4 (`v = w = V`; in Theorem 7.4 `Σ_R v` is minimised over subsets of rows `≠ ∅` by `L_r`, which avoids `∅`) go through. `I = ∅` ⟹ `M = 0`, exponent `∞` only. **HOLDS.**

### 1.5 Proposition 9.6, step (H) (l. 691)

- The first level set of the base house is dyadic by induction along step 1: the first half has the level sets of `fit(x_{H'})` (strict cuts), so its first level set is the child's, `{D ⊆ P_l}`, if its value is positive; if not, `Z_1 ≤ 0` everywhere, `fit(x_H) ≡ 0` and the first level set is everything, `{D ⊆ P_{s}}` at that level. The penalty shift keeps the level sets because it changes only at strict cuts — and this is where strictness is needed: a non-strict cut inside the first level set, with a jump of the shift there, would split the head into a non-dyadic prefix. So the strict (Cut) gives exactly what (H) uses. The rest of (H) («the largest big clock is `⌈μ⌉`») follows because the integer fit puts `⌈S/p⌉` first. (The sentence «every value of `X_1` is `≤ 0`» would be cleaner as «`Z_1 ≤ 0`»; it is unchanged from v1.) **HOLDS.**
- Steps (M) and (K) are unchanged except for the renaming `τ → ψ` and the extraction of Lemma K as Lemma 9.5 (same text); not re-graded.

### 1.6 Verdict on the repair (pencil)

The repair is correct: the restated Lemma 7.2(b) is true, the counterexample is right and shows what it claims, strict (Cut) is proved in every case of step 3, and every former use of the false integer claim now passes through a hypothesis that is proved. Remarks: two minor presentation points (the implicit «no level set crosses ⟹ cut», and «`J' ≢ 0`» missing in case (c)). Machine checks of my own in §2.

## 2. My own gates (with controls)

All my code is in `engines/` (written from the text, never from the author's gates, which I have not opened). Exact arithmetic only (Python integers and `Fraction`). The fit is computed by PAVA and every result is re-verified against the characterization of Lemma 7.1 (`fitlib.check_lemma71`), so a wrong PAVA would stop the run.

### 2.1 A new counterexample of my own (mission §2, item 6, first part)

1. **By hand, before any code** (sealed S1): `x = (1, 2, 0, 3)`. `fit(x) = (3/2)^4` (prefix sums of `x − 3/2`: `−1/2, 0, −3/2, 0`). `fit(1, 2) = (3/2, 3/2) = fit(0, 3)`, so `x` is cut at `2`, not strictly. `δ = (1, 1, 0, 0)`. `x + δ = (2, 3, 0, 3)`, fit `(5/2, 5/2, 3/2, 3/2)` = `fit(x) + δ` (the real part holds), integer fit `(3, 2, 2, 1)`; integer fit of `x` is `(2, 2, 1, 1)`, plus `δ`: `(3, 3, 1, 1)`. **Different.** Confirmed by `engines/fitlib.py` (log `logs/fitlib_selftest.log`).
2. **A less similar one, from the engine, re-done by hand:** `x = (−1, 2, 1, 0, 1, 1)`, `δ = (2, 2, 2, 0, 0, 0)` (jump `2`, length `6`). `fit(x) = (2/3)^6`; `fit(−1, 2, 1) = (2/3)^3 = fit(0, 1, 1)`: cut at `3`, not strict. `x + δ = (1, 4, 3, 0, 1, 1)`, fit `(8/3, 8/3, 8/3, 2/3, 2/3, 2/3)`, integer fit `(3, 3, 2, 1, 1, 0)`; integer fit of `x` is `(1, 1, 1, 1, 0, 0)`, plus `δ`: `(3, 3, 3, 1, 0, 0)`. **Different.**
3. **Smallest size** (exhaustive, `engines/gate_l72_mine.py` part A): no counterexample of length `≤ 3` exists (a non-strict cut whose common value is not an integer needs at least two positions on each side; when the value is an integer the integer fit equals the real fit and nothing can go wrong); 38 of length 4 with entries `0..5`. The first in lexicographic order, `(0, 1, 0, 1)`, is the text's `(3, 4, 3, 4)` minus `3` — I do not count it as new.

### 2.2 The restated Lemma 7.2(b) on random inputs, with controls

`engines/gate_l72_mine.py`, seed `20261005`, 50 000 integer sequences of length `2..10`, entries in `[−R, R]`, `R ∈ {2, 3, 4, 6, 9}`; `δ` = a random constant plus random jumps `1..3` at a random subset of the **strict** cuts. Log `logs/gate_l72_mine.log` (ends `VIGIA-FIN-OK exit=0`, 140 s, 11.6 MB).

| check | result |
|---|---|
| `fit(x + δ) = fit(x) + δ` | 0 failures / 50 000 |
| same level sets | 0 failures |
| every strict cut of `x` is a strict cut of `x + δ`; every cut stays a cut | 0 failures |
| integer fit of `x + δ` = integer fit of `x` + `δ` | 0 failures |
| **control B1**: one jump at a *non-strict* cut | integer claim fails in **736 / 9 939** (7.4 %); real part holds in all 9 939 (as the lemma says) |
| **control B2**: one jump at a position that is *not a cut* | real part fails in 45 043 / 45 043 |

The controls can fail and do. **Verdict: the restated (b) HOLDS on every test; the v1 integer claim is false in 7.4 % of random non-strict jumps.**


### 2.3 Theorem 7.8 with strict (Cut), Lemma 7.9 and the integer shifts, on every house with `k ≤ 6` (mission §2, item 6, last part)

`engines/gate_houses_mine.py` (with `engines/fitlib.py`, `engines/fitfast.py`), written from the definitions of §7.3 only: `R_H`, `J_H`, `x_H`, `γ`, `ĉ_H` from their formulas; `ŷ_H` by my PAVA; `V` by steps 1–8 of the proof, recursively over the top digit. Log `logs/gate_houses_k6.log` (ends `VIGIA-FIN-OK exit=0`, 36 s, 142 MB). Houses `H = (I, k, ℓ, α)` with `1 ≤ k ≤ 6`, every `I ⊆ [0, k)`, every `0 ≤ ℓ < 2^k`, `α = 1, 2, 3`: **16 380 houses**.

| claim | how | result |
|---|---|---|
| (E), (M), (G), (Λ) for `V`, `c_F` = lower end of the interval | definitions; (G) on every arrow `b ⊊ a` | 0 failures / 16 380 |
| the same, `c_F` = upper end | | 0 failures / 16 380 |
| step 7: `F_1` a final segment containing `I'`; `c_3 = max_{F_1} v'`; `c_4 = min_{F_2} v'`; `v'(p^*) < v'(p)`; interval non-empty | at every level of every house | 0 failures |
| Lemma 7.7: first half of `x_H` = `x_{H'} + d_1`, `d_1` from the window data; antisymmetry | | 0 failures |
| step 1: `fit(x_{H'} + d_1) = fit(x_{H'}) + d_1`, same level sets, integer fit `ŷ' + d_1`; Lemma 7.3 gluing of the integer fit | | 0 failures |
| **strict (Cut)** at the first dancer with `J_H = 1` and at its mirror, by the *definition* of a cut | 8 001 houses with `J_H ≢ 0` | **0 failures**; `b ≠ ∅` in all 8 001 |
| case count of step 3 (houses with `I ≠ ∅`) | | (a) 2 547, (b) 2 907, (c) 2 547, (d) 8 001 |
| penalty shifts `−P_r J_H(D) + P_c J_H(I ∖ D)`, all 24 pairs `(P_r, P_c) ∈ [0, 4]^2 ∖ {(0,0)}`: integer fit shifts, same level sets, Lemma 7.9 separation, integer fit non-increasing | 8 001 × 24 = **192 024** non-trivial shifts | 0 failures |
| deletion of `∅` at `ℓ = 2^k − 1`: `∅` alone in its level set, real and integer fits restrict, separation | **360** houses | 0 failures |
| Lemma 7.9 separation on `x_H` itself | 16 380 | 0 failures |
| my integer PAVA against my `Fraction` PAVA; my fast «all cuts» against the definition | 16 380; 3 000 | agree |

**Controls (each must be able to fail, and does):**
- wrong price of the central flat: `c_F` = upper end + 1 breaks (M) or (G) in **2 358** houses; lower end − 1 in **2 358**; `c_F := v'(I')` in **140**;
- the penalty shift moved one position after the strict cut breaks the integer-shift identity in **17 354 / 168 912** trials;
- the strict-cut claim checked one position after `b` fails in **1 911 / 7 038** houses;
- and strictness is not automatic in houses: **3 180** of the 16 380 houses have a non-strict cut somewhere (17 238 non-strict cut positions in all). A check of «the cut at `b` is strict» could therefore have failed.

**Extension to `k = 7`** (log `logs/gate_houses_k7.log`, `VIGIA-FIN-OK exit=0`, 284 s, 143 MB; same code, with the top-level houses not cached — I re-ran `k ≤ 3` after that change and the log is identical, `logs/gate_houses_k3_again.log`): **49 152 houses** (`k = 7`, every `I`, every `ℓ`, `α = 1, 2, 3`), 24 384 with `J_H ≢ 0`, 585 216 non-trivial shifts, 381 deletions: **0 failures**. Controls: `c_F` = top + 1 fires in 8 016 houses, bottom − 1 in 8 016, `c_F := v'(I')` in 660; shift one position late fires in 60 716 / 552 960; strict cut at `b + 1` fails in 6 056 / 23 040; 9 793 houses have a non-strict cut somewhere.

**Verdict: Theorem 7.8 with strict (Cut), Lemma 7.9 and the shifts of Theorem 7.10 / Proposition 9.6 HOLD on every house with `k ≤ 7`, `α ≤ 3` (65 532 houses).**

A count I can already make from the text alone: §12.1 reports «393 120 shifts» for the author's gate. `393 120 = 24 × 16 380`, i.e. 24 shifts on *every* house, while only the 8 001 houses with `J_H ≢ 0` have a non-zero shift: `24 × 8 001 = 192 024` (my count). The other 201 096 «shifts» are the zero vector. See §6 for whether the author's code does this.

### 2.4 Theorem 7.10 against the true Smith form of `M` (beyond the mission's minimum; I had the time)

`engines/gate_t710_mine.py`: `M^{(α)}(λ, i)` built from the closed form of Theorem 4.4 (`q_k` by its recursion, windows, payments `2^α(i + d)`, the power `2^{1 − K + o(Δ)}`), its Smith exponents over `Z_2` by min-valuation elimination in `Z/2^P` with `P = v_2(det) + 8` (above every exponent), compared with Theorem 7.10's prediction from the rulers of §5 and Proposition 5.4, pooled by my PAVA; and, for `α = 1`, with the Main Theorem's rule (raw clocks `u_i(D)` of §1.2, pooled, plus `k`). I also checked the `λ = 6` example table of §4.4 by hand against Theorem 4.4 (all ten entries agree).

| range | cells | result | controls |
|---|---|---|---|
| `1 ≤ λ ≤ 63`, `0 ≤ i ≤ 12`, `α = 1, 2` (`logs/gate_t710_63_12_v2.log`, 2 s) | 1 638 (114 with `i = 0`) | **0 failures**; rule route 756 / 756 | raw clocks rejected 306 / 306 cells where pooling acts; penalty moved one position late rejected 232 / 232 |
| `1 ≤ λ ≤ 127`, `0 ≤ i ≤ 30`, `α = 1, 2` (`logs/gate_t710_127_30.log`, 350 s) | 7 874 (240 with `i = 0`) | **0 failures**; rule route 3 810 / 3 810; Lemma 7.5 («the cell is the penalty cell») 0 failures | raw clocks rejected 1 834 / 1 834; late penalty rejected 1 904 / 1 904 |

Cells with `i ≥ 1` where the repaired step is really exercised (non-zero penalty shift *and* a level set of size `≥ 2`): 125 of 1 524 (first range), 978 of 7 634 (second range).

My cell count for the second range, 7 874, is the count printed in §12.2 for reader 3's row «Theorem 7.10 on the matrices `M`». Reader 3's «1 876 cells where pooling acts» differs from my 1 834 (cells with `i ≥ 1`); the difference, 42, would be the `i = 0` cells where pooling acts if reader 3 counted them — I did not count those, so I cannot confirm.

**My error, published:** my first version of this gate had a second control, «round the level sets floors-first», and it never fired — because I compared sorted lists, and the two roundings of a level set are the same multiset. That control could not fail. I replaced it by the «late penalty» control, which fires. (Log of the bad version: `logs/gate_t710_63_12.log`.)

### 2.5 An observation the text does not make: in every house the real fit is already an integer sequence

Measured first (`logs/scan_nonintegral.log`, 65 532 houses `k ≤ 7`, `α ≤ 3`, every `ℓ`; and the 7 634 real cells with `i ≥ 1` above): **no level set of `fit(x_H)` has a non-integer mean**, nor in the `i = 0` sequences with `∅` deleted.

Then proved (my own two lines, using only real-fit statements of the paper): by induction on `|I|`, `fit(x_H)` takes integer values. For `I = ∅` it is `(0)`. For `I ≠ ∅`, the first half of `x_H` is `x_{H'} + d_1` with `d_1` integer, non-increasing and changing only at cuts of `x_{H'}` ((Cut) for `H'`, strictness not needed), so its real fit is `fit(x_{H'}) + d_1` (real part of Lemma 7.2(b)), integer-valued by induction; and Lemma 7.3 gives `fit(x_H) = [max(Z_1, 0), min(Z_2, 0)]`, integer-valued. Penalty shifts are integer, and the deletion at `i = 0` is a restriction at a cut. ∎

Consequences for the reading:
1. In every place where the paper applies it, the integer fit *equals* the real fit (`S mod p = 0` on every level set). So the v1 integer claim of Lemma 7.2(b), false as a general lemma, was **true in every application**; the v1 gap was a gap of proof, never of conclusion — consistent with Appendix A's «No theorem is affected».
2. The repair is correct (§1), but a shorter repair was available: state and prove integrality (the two lines above), after which Lemma 7.2(b)'s integer part is needed only for integral fits, where it is trivial, and Lemma 7.9 is automatic (`⌊μ_A⌋ = μ_A > μ_B = ⌈μ_B⌉`).
3. Strictness is still genuinely used where the *level sets* matter, not the integer values: Proposition 9.6 (H) (the head stays dyadic) and Theorem 7.10 at `i = 0` (the level set of `∅`).
4. The «integer antitonic fit» of §1.2, with its `⌈S/p⌉`/`⌊S/p⌋` rule, never rounds anything in the Main Theorem: the pooled clocks are the antitonic least-squares fit itself. The paper could say so; it would make the rule simpler to state and to believe. Likewise the `2(S mod p)` count in the proof of Corollary 1.7 is always `0`.

Grade: not an error of v2. **PRESENTATION / simplification (substantive):** the paper should state the integrality of the fit.

This also bears on controls: a control that perturbs only the rounding (as my failed one, or any variant that changes only `⌈·⌉`/`⌊·⌋`) cannot fail on houses or cells. The author's random-sequence gate for Lemma 7.2(b) is not affected (random sequences are not houses).

## 3. The other changes, hunk by hunk

### 3.0 Part 1 — §1.0, §13, Appendix A, and the first pass (written 2026-10-05, Part 1)

Integrity: the 49 files of `MANIFEST_md5.txt` match (log `logs/md5check.log`). I regenerated `diff -u v1.md v2.md` myself: its body is byte-identical to `DIFF_v1_to_v2.txt` (log `logs/regen_diff.log`), 45 hunks. So the diff I grade is the true diff of the two texts I was given.

- **§1.0 (status paragraph), v2 l. 32.** States: v1 read cold as a whole, «holds with gaps», one gap in Lemma 7.2(b), repaired in §7.1, §7.4, repair not read cold. Consistent with §13 and Appendix A. Small point: the uses of the repaired lemma include Proposition 9.6 (§9.2), which the pointer «(§7.1, §7.4)» omits. **PRESENTATION (minor).**
- **§13, bullet 1 vs bullet 2, v2 l. 1026–1027.** Bullet 1 gives the grade «pencil, audited, read cold» to the Main Theorem, Theorems O and F, and Corollaries 1.5–1.7. But the proofs of the Main Theorem (through Theorem 7.10 and Lemma 7.9), of Theorem F (Theorem 7.8 is its core), and of Corollary 1.6 (through Proposition 9.6) now contain the repaired steps that bullet 2 says are «not yet read cold». Read literally, bullet 1 says that the v2 proofs of these results were read cold, which they were not (the v1 proofs were, and had the gap). The two bullets should be reconciled, e.g. «read cold in version 1 (one gap, repaired in version 2, repair not yet read cold)». Also: Corollaries 1.5–1.7 moved from «pencil, audited» (v1) to «read cold»; Appendix A justifies it (read cold «as text with version 1»). **PRESENTATION.**
- **§13, bullet 2.** Lists as «repaired, not yet read cold» only the Lemma 7.2(b)/(Cut) repair. Other changes of v2 also add new mathematical argument that no one has read cold: the weight-space decomposition by Newton interpolation in Lemma 3.3, the new identification `X_1 ≅ Δ_A(m+1)` in Lemma 2.4, the faithfulness argument in §10.3 (now invoked for the multiplicativity of the twist map), and the corrected count in step 3 of the proof of Corollary 1.6. Bullet 4 («Not done: a cold reading of the changes of this version») covers them, so this is not wrong, only incomplete. I grade those items in §3 below. **PRESENTATION (minor).**
- **Appendix A.** Consistent with §1.0, §13 and with `CORRECTIONS_v1_to_v2.md`. Which are the «four entries of the verification record [that] said more than the code did» I cannot tell from the material: comparing the two §12's, candidates are the v1 Theorem 6.2 row («`|I| ≤ 4`, 61 cases», while the code did `|I| ≤ 3`, CORRECTIONS §4), the v1 Theorem 7.8 row («48 006 houses», which are 16 002 houses × 3 prices), and the rows that rested on code not printed (Lemma 10.8, Theorem 10.15 «≈ 10^6 pairs», Lemma 10.20, Theorem 10.22 «flight 9»), which left §12.1. (A first version of this paragraph named four of them as if certain; corrected, §8.) **HOLDS as a description; not verifiable beyond the two texts.**
- **First pass on the diff.** No hunk changes the statement of a numbered theorem, proposition, lemma or corollary, except: Lemma 7.2(b) (restated — the repair), Theorem 7.8 (Cut) (strengthened to strict — the repair), and the renamings (`σ_r → β_r` in Theorem 6.2, `ε_L → e_L` in Lemma 10.10, `κ_h, ρ_h → in_h, out_h` in Lemma 10.8, `φ → ϑ` in Lemma 10.13). The sentence «No statement of a theorem changed» (§13, CORRECTIONS) is true for theorems in the strict sense; Lemma 7.2(b) is a lemma whose statement did change, as §13 itself says. Detail in §3.1.

### 3.1 Hunk by hunk

`v1`/`v2` = line in each file; «meaning» = did the statement of a numbered result change; «refs» = did a reference, number or cross-reference break. Machine checks behind the «refs» column: `logs/oldnames_grep.log` (no old name left: `τ(D)`, `σ_t`, `σ_r`, `κ_h`, `ρ_h`, `doblar`, `paso`, `IKKY22`, `Yue23`, `DHS17`, old numbers 9.5–9.9 — none; the remaining `ε` are the `ε` of `𝒮 = F_2 ⊕ εXF_2[[X]]` and a small `ε` in Lemma 7.1, other objects), and `logs/xref_check2.log` (every internal «Lemma/Theorem/Proposition/Corollary x.y» and every «§x.y» resolves; the only unresolved labels are citations of other papers: GMMY's 1.9, 2.5, 2.12, 2.13, 4.1, 4.2, 4.4, Bai's 1.1–1.3, CSX's §5.2, Humphreys' §26).

| # | v1 → v2 | what changed | right? | meaning | refs |
|---|---|---|---|---|---|
| 1 | 6 → 6 | «version 2» | yes | — | — |
| 2 | 32 → 32; 38 → 38 | §1.0 status paragraph (see §3.0); IKKY quotation now verbatim with «[sic]», label IKKY23 | yes (§4.2) | no | ok |
| 3 | 60 → 60 | PAVA: «adjacent blocks with equal means are merged» | yes: strictly decreasing block means need it | no (makes the definition exact) | ok |
| 4 | 96 → 96 | the v1 remark «why dry and wet» replaced by a pointer to §1.7 | yes | — | ok |
| 5 | 104–112 → 104–112 | «(we checked `3 ≤ n ≤ 12`, §12)»; new paragraph relating Bai's count (invariant factors of `K(Q_n)`) to cyclic factors of `Syl_2`; parenthesis on GMMY's `c_i` | yes (§4.2); `3 ≤ n ≤ 12` is §12.2's reader-2 row (§12.1 has `3 ≤ n ≤ 11`) | no | ok |
| 6 | 128 → 130 | §1.5 item 4 names Lemma 6.4 | yes | — | ok |
| 7 | 149–154 → 151–156 | §1.6: `ψ(E)`, `ϑ(y)`, the list of double meanings (`D`, `K`, `T(·)`, `τ_t`/`τ_i`, «window») | yes; I found no other double meaning | — | ok |
| 8 | — → 158–190 | new §1.7, vocabulary | see §3.2 | — | ok |
| 9 | 156–167 → 192–203 | §1.7 → §1.8; new credits to GMMY; [DHS18]; the [Aky26] paragraph | see §4 | — | ok |
| 10 | 183 → 219 | `(Z ⊕ K) ⊗ Z_2 ≅ Z_2 ⊕ Syl_2 K`, right exactness | yes (the v1 «`Syl_2(Z ⊕ K) ⊗ Z_2`» was garbled) | no | — |
| 11 | 191 → 227 | definition of a lattice: «the module is the direct sum of its weight spaces» | yes (now an explicit part of the definition; Lemma 3.3 proves it for extensions) | no | — |
| 12 | 214 → 250 | Lemma 2.4 proof: `X_1 ≅ Δ_A(m + 1)` via `X_1 ⊗ Q ≅ Δ_Q(m + 1)` and `Δ_A := Dist_A·v` (§2.3); `F^{(s)}(v ⊗ b_1) = F^{(s)}v ⊗ b_1` now an equality | yes, re-derived (Verma quotient of dimension `m + 2` is the simple module; `Δ(F^{(s)})` on `v ⊗ b_1` kills all terms with `F^{(r)}b_1`, `r ≥ 1`) | no | ok |
| 13 | 238 → 274 | Prop. 3.1(d): Weyl's theorem named | yes (characters of simple modules are independent, complete reducibility) | no | — |
| 14 | 242–245 → 278–282 | Lemma 3.2 `φ → f`; Lemma 3.3: extension of lattices is a lattice, via `X ⊗ Q` semisimple and the projections `P(H) = Σ_r (Δ^r P)(w_0) C(H − w_0, r)` | yes, re-derived: `P` takes the values `0, 1` at the integers of `[w_0, w_1]`, so its forward differences at `w_0` are integers; `C(H + c, r) ∈ Dist_Z`; each weight space is a direct summand of a free `Z_2`-module, hence free | no | ok |
| 15 | 265 → 301 | Lemma 3.5: «the construction in the proof of Lemma 3.2, which works verbatim over `F_2`» | yes (weights of `V ⊗ V^{[1]}` lie in `[−3, 3]`; only `F^{(t)}F^{(r)} = C(r+t, t)F^{(r+t)}` and (K) are used) | no | ok |
| 16 | 276 → 312 | Remark (2): Weyl's theorem added to the list of tools | yes, consistent with 13–14 | — | — |
| 17 | 298 → 334 | `f_max → f_{max}` | typographic | — | — |
| 18 | 308–317 → 344–353 | «doblar», «paso» → «the twist move», «the split move» | yes | name only | ok |
| 19 | 326–335 → 362–372 | the same names; Prop. 4.3 proof «half the rank»; new sentence on slot order vs o-order (`∅, {1}, {0}, {0,1}`) | yes: with the slots `(s, A), (s, C)` adjacent, two split moves at `0, 1` give `∅, {1}, {0}, {0,1}`; both orders extend inclusion and `M_{DD'} ≠ 0 ⟹ D' ⊆ D` | no | ok |
| 20 | 350 → 386 | Theorem 4.4 proof: «split move» | yes | name | — |
| 21 | 359 → 395 | Lemma 4.5 proof: «`±1`» for `a_{m+1}({m})` | yes: `a_1({0}) = −a_0(∅) = +1`, and `−1` for `m ≥ 1` | no | — |
| 22 | 376–380 → 409–418 | the `λ = 6` example matrix as a table; «`2^{|I|} ≤ ⌊λ/2⌋ + 1` rows, equality e.g. at `λ = 2^{k+1} − 2`» | yes: all ten entries re-derived from Theorem 4.4 (`q_2 = 1 + 2y_0 − y_1 − y_0y_1`); the bound holds (if `|I| < k`, `2^{|I|} ≤ 2^{k−1} ≤ ⌊λ/2⌋ + 1`; if `I = [0, k)`, equality) and v1's «`(λ + 1)/2`» fails at `λ = 2` | no | — |
| 23 | 409–417 → 451–456 | Prop. 5.3: `τ → ψ`; sign of the zero difference in step 1; «so this is `0`» in step 3 | yes, re-derived: the difference is `k − |I| − G(I) − t_1 = k − t_1 − Σ h_t = 0` | no | ok |
| 24 | 419 → 458 | shift `0`: «both rulers are read at `K − 1`… the house with `ℓ = K − 1`» | yes, consistent with Prop. 5.4 and §7.3 | no | ok |
| 25 | 426 → 464 | Prop. 5.4 proof: which argument of `κ` changes between `i = 1` and `i = 0` | yes: `κ(a − 1, ξ) − κ(a, ξ) = v_2(a) − v_2(a + ξ)` | no | — |
| 26–28 | 437, 446, 455 → 474, 486, 496 | `σ, σ_r → β, β_r` (Theorem 6.2, Cor. 6.3) | yes | name only | ok |
| 29 | 465 → 504 | Lemma 6.4, second case: the missing inequality `d(r_1) − d(r^*) < Y(r_1) − Y(r^*)` | yes, re-derived | no | — |
| 30 | 483–494 → 522–531 | **the repair** (definition, Lemma 7.2(b), antisymmetry of strict cuts) | §1.1 | **Lemma 7.2(b) restated** (stronger hypothesis) | ok |
| 31 | 522 → 561 | Lemma 7.5: «one of the two penalties is `0`» | yes: `m` and `m + K` differ in bit `k` with no carry when it is `0` in `m`, and when it is `1` in `m` the bit `k` of `m + K` is `0` | no | — |
| 32–33 | 527, 538–541 → 565, 576–578 | `σ_t → sat_t` | yes | name only | ok |
| 34 | 554–576 → 593–611 | **the repair**: strict (Cut), its proof, `φ → ω` in step 4 | §1.2 | **(Cut) strengthened** | ok |
| 35 | 590–598 → 628–635 | **the repair**: Lemma 7.9 and Theorem 7.10 proofs | §1.3–1.4 | no | ok |
| 36 | 620–665 → 660–707 | §9.2: `τ → ψ`, `ψ_t`; Lemma K becomes **Lemma 9.5**; Prop. 9.5 → **9.6** with the strict-cut sentence; Lemma 9.6 → 9.7; Cor. 1.6 proof: `A_0` named, the count of step 3 | yes; re-derived the datum `τ_{t_j} = ψ_{t_j}` in the house `(I, k, 0, 1)` (all windows of type `0`, `κ_t = 1`); step 3: `2(n − 2) ≥ n + 1` for `n ≥ 6`, and for `n = 4`, `G = g(3) = 3`, `c_1 = φ(4) − 1 = 5`, and `4` factors at `G` suffice | no | ok |
| 37 | 668–688 → 713–725 | Lemmas 9.7, 9.8, Theorem 9.9 → 9.8, 9.9, 9.10 and the references to them | yes | — | ok |
| 38 | 712 → 760 | Lemma 10.4: `ε → (−1)^j`; `Q = (−1)^{j+1} Sh^{−1}` | yes (`−ε = (−1)^{j+1}`) | no | — |
| 39 | 728 → 776 | `Ψ_{i+1} − Ψ_i = 2(1 + (−1)^i Sh^{−1})` | same as v1 with `ε = (−1)^i` | no | — |
| 40 | 736–756 → 784–804 | §10.3: `p(D)` for the generic function; **new faithfulness argument** («a value `x_m(g)` with `g < m` never acts … the action on all the `T(l)` together is faithful»), now invoked for the multiplicativity of the twist map | yes, re-derived: with `u_g := F^{(g)}u_0` (top vector `u_0` of `T(l)`), `x·u_{g−m}` has coefficient `x_m(g)C(g, m)` on `u_g ≠ 0` for `g ≤ l`; so `x` acting as `0` on all `T(l)` forces `x_m(g) = 0` for every `g ≥ m`. The product rule only reads values at `f ≥ m`, so the identification is compatible | no | ok |
| 41 | 767–776 → 815–824 | Lemma 10.8 `κ_h, ρ_h → in_h, out_h`; Corollary 10.9 | yes | name only | ok |
| 42 | 786, 814–827 → 834, 862–875 | `ε_L → e_L`; `φ → ϑ` in `𝒦` and Lemma 10.13 | yes | name only | ok |
| 43 | 839–850 → 887–902 | Theorem 10.15 proof: «the twist move», «the split move», display on two lines; **Remark (2) rewritten** | see §3.3 | no | ok |
| 44 | 863–889 → 916–942 | `𝔞(ϑ)`; Lemma 10.18 «twist move»; Lemma 10.20 `out`, `in`; Cor. 10.21; Theorem 10.22: `W_+ ≡ I`, `W_− ≡ −I (mod 2)`, so `W_+ − W_− ∈ 2·Mat(Z_2)`; case labels | yes (v1's «`≡ 2I (mod 2)`» meant the same but was badly put) | no | ok |
| 45 | 909–1026 → 962–1088 | §10.8 «we checked `3 ≤ n ≤ 12`»; §11.1 labels; §11.6 wording; §12 rewritten; §13; Acknowledgements; Appendix A; references | §3.0, §3.4, §4.3 | no | ok |

**Conclusion of the table.** No hunk changes the statement of a theorem. The two statements that changed are Lemma 7.2(b) (restated) and (Cut) in Theorem 7.8 (strengthened), as §13 says. Every renaming is complete and every internal reference resolves. The new arguments (Lemmas 2.4, 3.3, 3.5, §10.3, Lemma 6.4, Prop. 5.3, Cor. 1.6) are right.

### 3.2 §1.7 «Vocabulary, and why these names» (v2 l. 158–190)

Each row against the body:
- family/shift (`σ = F + n − H = F + λ − H + 2i` on `T(λ)`, Theorem 3.8 proof l. 326); dance lattice (Remark (1) l. 311); dancers/o-order; floor (l. 227); payment/payment system (l. 334: couplings `K_{ss'}` from `s'` to `s > s'`, lower-triangular); twist/split move (Props. 4.1–4.2, §10.3); the dance (`k` moves, Prop. 4.3); final matrix/window (Theorem 4.4); ruler/gold (Prop. 5.2: row term `R_m(a)`, column term `−R_{m+K}(b)`, `γ`); golden matching (Theorem 6.2, Cor. 6.3); mirror; ceiling/floor (Cor. 6.3 upper bound, Theorem 7.8 lower bound); house/penalties (§7.3); windows/gates (Lemma 7.6); podium; the fold; arms/glue/bend (Lemma 10.5, Lemma 10.20 «the bend»); formal dance/positions/covariant system (§10.3, §10.5); turned lid (§11). **All match.** Two small inexactnesses:
  - «covariant system: a system whose coefficients depend only on the position of the target»: the definition (l. 860) has them depend on `Δ = D ∖ D'`, `m` *and* the position. **PRESENTATION (minor).**
  - «raw clocks; pooling: … their integer antitonic least-squares fit»: the integer fit is a rounding rule applied to the least-squares fit, not a least-squares fit over integer sequences. In this paper the two coincide, since the fit is always integral (§2.5), but the phrase as written is not a definition. **PRESENTATION (minor).**
- **«Why dance»** (l. 188). Exact: reading `λ + 1` from the bottom, a `0` digit is a twist move and a `1` digit a split move (Prop. 4.3 and §3.3), and after `k` digits the slots are the `2^{|I|}` subsets of `I`. Inexact: «at every step each floor pays a power of `2`» — the payment of floor `d` is `2^α(i + d)`, a power of `2` times an odd number (and `0` at `i = d = 0`); only its valuation matters, but the sentence says something else. «records who owes what to whom» and «brings it to rest» are colour, harmless and recognisable as such. **PRESENTATION (minor):** «each floor pays an even amount» or «pays `2^α(i + d)`».
- **«Why dry and wet»** (l. 190). Exact: `F^2 = 2(1 ⊗ F)` on `Φ(N)` (from `F(b_0 n) = b_1 n`, `F(b_1 n) = 2b_0 Fn`, l. 258) — «`F^2` acts as `2F` of `T(l)`» is right; «the cokernel of the Laplacian modulo `2` sees only the number of cyclic factors of the `2`-part» is right (its dimension is that number plus one); the last sentence is Theorem DW. Loose: «the module `T(2l + 1)` is the Frobenius twist `V ⊗ T(l)^{[1]}`» — modulo `2`, `T(2l + 1) ⊗ F_2 ≅ V ⊗ T(l)^{[1]}` (Prop. 3.1(c)); that is `V` tensored with the twist, not «the Frobenius twist». **PRESENTATION (minor).**
- Verdict on §1.7: the dictionary is faithful; the two «why» paragraphs are mostly exact mathematics, with one inexact clause each.

### 3.3 Remark (2) of §10.5 (v2 l. 896–900)

- **«every payment system dances clean, whatever its payments (Proposition 4.1)»** — false as written. Proposition 4.1 is stated for an *even* payment system, and evenness is needed: for a payment system `F + π(D) + K(D)` the twist move has `P = 1` and `S = 2F − (π + K)(2D)(π + K)(2D + 1)` (Lemma 10.6(a)), which is not `≡ 0 (mod 2)` when the payments are odd (e.g. `π ≡ 1`). The intended sentence is «every *even* payment system dances clean, whatever its (even) payments», which is what Remark (1) and Lemma 10.6 use. The remark is labelled «used nowhere», so nothing depends on it. **ERROR (minor, one missing word).**
- The rest is stated as a measurement and no more: the operator, the ranges (`l = 2, …, 63`, four dances per `l`, 248 per case, seed `11` in §12.1), the outcomes (3 unclean at `l = 63`; 79 unclean, first at `l = 32`; 496 / 496 clean with `η_m`), «this is used nowhere», and §13 lists it under «Measured, not proved». The «four experiments» of §12.1 are the two random cases and the two with `η_m` (`496 = 2 × 248`). **HOLDS as a measurement.** The numbers themselves are re-run in §6.
- v1 said «first at `l = 63`, resp. `l = 31`»; v2 says «three dances, all at `l = 63`» and «first at `l = 32`». A different, now documented experiment; consistent with being a measurement.

### 3.4 §12 (Computations), §13, Appendix A

- **§12.1 rows against my own counts.**
  - Theorem 7.8 strict (Cut), `k ≤ 6`, `α ≤ 3`: «16 380 houses, 8 001 boundaries, 360 deletions» — I get exactly these. **«393 120 shifts»** `= 24 × 16 380`: 24 penalty pairs on every house, including the 8 379 houses with `J_H ≡ 0`, where the shift is the zero vector. Non-trivial shifts: `24 × 8 001 = 192 024` (my count). The row states twice as many shift-tests as there are non-trivial ones. **PRESENTATION** (verified against the code in §6).
  - Its control, «`x = (3, 4, 3, 4)` … breaks the integer shift», is a single hand example: it shows the comparison can fail, not that the house check could. My controls on houses (wrong price, late penalty, strictness at `b + 1`) fire (§2.3). **PRESENTATION** (the control is weaker than the row suggests).
  - Lemma 7.2(b) random: control «189 of 2 841» (6.7 %) — the same order as my 736 of 9 939 (7.4 %). Plausible.
  - Theorem 7.8 «16 002 houses» for «`λ ≤ 127`, `α ≤ 3`, every `ℓ`»: `16 002 = 3 × (Σ_{k=1}^{6} 4^k − Σ_{k=1}^{6} 2^k)`, i.e. the houses with `1 ≤ k ≤ 6` and `I ≠ ∅` — exactly my case count (a)+(b)+(c)+(d). The range «`λ ≤ 127`» would also allow `λ = 127` (`k = 7`, `I = ∅`) and `I = ∅` houses; harmless, but the range should read «`I ≠ ∅`, `k ≤ 6`». **PRESENTATION (minor).** «48 006 house-checks» `= 3 × 16 002` ✓.
  - Theorem 6.2: «`|I| ≤ 5`, every `r`, 69 cases» `= Σ_{s=0}^{5}(2^s + 1)` ✓ (the theorem depends only on `s = |I|`).
  - Theorem 7.10: «`λ < 64`, `i ≤ 12`, `α = 1, 2`: 1 550 cells». My count of `(λ, i, α)` with `1 ≤ λ ≤ 63`, `0 ≤ i ≤ 12` is 1 638 (1 524 with `i ≥ 1`). I cannot reproduce 1 550 from the text; see §6.
  - The rows with «none» in the control column say so; «a counter shows …» is described as a counter, not a control. Honest.
- **§12.2** describes other readers' work whose code I do not have; I can only check internal consistency: «all houses with `k ≤ 7`, `α = 1, 2`: 43 690 houses» `= 2 × Σ_{k=0}^{7} 4^k` ✓; «Theorem 7.10 on the matrices `M`, `λ ≤ 127`, `i ≤ 30`, `α = 1, 2`: 7 874 cells» = my count ✓; its «1 876 cells where pooling acts» vs my 1 834 with `i ≥ 1` (§2.4) — not checkable.
- **§13**: see §3.0 (bullets 1 and 2 should be reconciled). «Measured, not proved» now includes Remark (2): right.
- **Appendix A**: consistent with §1.0 and §13. **HOLDS.**

## 4. Sources, citations and references

I checked every quotation and every credit in the changed passages against the text extractions in `material/sources/` (the line numbers below are those of the `.txt` files).

### 4.1 The quotation of Akyar et al. [Aky26] (§1.8, v2 l. 203)

Source: `TwoAdicAllOnesSquare_arXiv2609.10625.txt`, §4 «Further directions», paragraph «Reflections and the exceptional prime» (l. 559–567). Their text: Reiner and Tseng's exact sequence «splits on primary components away from primes dividing the covering degree [22]. This makes the prime 2 a natural place to look for additional structure under an involution. Our odd-grid reflections have fixed vertices, however, so the fold is not a regular double cover and their splitting theorem does not apply directly. Can an analogous integral description with fixed vertices explain both the folded all-ones class and the remaining 2-primary factors?»

- «a natural place to look for additional structure under an involution»: **verbatim**, and v2 now gives its frame (the Reiner–Tseng splitting away from the covering degree) in its own paraphrase, correctly. **HOLDS.**
- «an analogous integral description with fixed vertices»: **verbatim**, but it is a fragment of their question; the question goes on «explain both the folded all-ones class and the remaining 2-primary factors?». v2's paraphrase «they ask for an analogous integral description with fixed vertices» keeps the subject and drops the object. It does not reverse their meaning (v1's trimmed quotation did; this one does not), and v2 no longer claims to answer them: it only says that the antipodal fold has no fixed vertex and is a regular double cover. The mission asks whether it is «quoted whole»: the first sentence is; the question is not. The question is one line; quoting it whole would remove any doubt. **PRESENTATION (minor).**
- «Their own folds of grids have fixed vertices»: they say «Our **odd-grid** reflections have fixed vertices». v2 generalises from odd grids to grids. **PRESENTATION (minor):** write «their reflections of odd grids».
- Bibliographic entry [Aky26] (nine authors, title, arXiv:2609.10625, 2026) agrees with the first page of the source (arXiv:2609.10625v1, 9 Sep 2026). **HOLDS.**

### 4.2 Credits to Gao, Marx-Kuo, McDonald, Yuen [GMMY24] and the other quotations of §1.1 (v2 l. 38, 102–104, 112, 119, 201, 666, 958–960, 966)

Source: `GaoMarxKuoMcDonaldYuen_arXiv1912.06919v3.txt`.
- **Proposition 1.9** (l. 220): for odd `p`, `Syl_p K(G) = Syl_p ⊕_{u≠0} Z/λ_{u,M}` — the odd part of every Cayley graph of `F_2^r` from its eigenvalues. v2's credit (l. 201) and its use for the folded cube (l. 102, with the eigenvalues `2|J|`, `|J|` even, supplied by v2) are right. **HOLDS.**
- **Proposition 2.12** (l. 542): for `M_r = (e_1 ⋯ e_r, e_1 + ⋯ + e_r)` the rank of `L(G(F_2^r, M_r))` (over `F_2`: their base cases `K_4`, `K_{4,4}` have ranks 1 and 2) is `2^{r−1} − 2^{⌊(r−1)/2⌋}`. `G(F_2^r, M_r)` is `Q_{r+1}/⟨𝟙⟩`; with `r = n − 1` this is `a_n`. v2 l. 201 («the `F_2`-rank of the Laplacian of the folded cube») and l. 960 («with their `r = n − 1`») are right. **HOLDS.**
- **Remark 2.13** (l. 604–607): the quotation «We are not sure if that is a coincident, or a special case of some deeper connection» is verbatim (their «coincident» is theirs). **HOLDS.**
- **Remark 4.4** (l. 909–915): `max_{x<n}(v_2 x + x)` need only be inspected at the numbers obtained from `n − 1` by clearing its lowest set bits successively. That is Lemma 9.2(b) for `N = n − 1` (v2 l. 666), and «contains Lemma 9.2(b)» (l. 201) is fair (Lemma 9.2(b) is stated for every `N`). **HOLDS.**
- **Table 1** (l. 1194–1216): «Sylow-2 cyclic factors of K(Q_n) for n ≤ 11 (table from [2])», `[2]` = Bai. v2 «their Table 1 reproduces Bai's table of `Syl_2 K(Q_n)` for `n ≤ 11`» is right. The rows `n = 5, 6` (as far as the garbled extraction can be read) agree with v2's examples `{1: 6, 3: 4, 4: 1, 6: 4}` and `{1: 12, 2: 4, 3: 1, 5: 4, 6: 10}`. **HOLDS.**
- **Theorems 4.1, 4.2, Conjecture 4.14, Conjecture 5.4** (l. 890–898, 1156–1159, 1179–1185): the forms quoted in Corollaries 1.6 and 1.7 agree (`max_{x<n}` = `g(n)`, `max_{x<n−1}` = `g(n − 1)`, `k ↦ e`). Their `c_i(Q_n)` is «the size of the largest cyclic factor in K(Q_n)» and they state `v_2(c_i)`; v2's new parenthesis (l. 112) says exactly that. **HOLDS.**
- **«determining the complete structure still seems out of reach at this moment»** (l. 1168): verbatim. **§2.2** (l. 516–541): non-generic = `𝟙 ∈ ker M`, built from `Q_n/⟨𝟙⟩` by successive codimension-one quotients: v2 l. 966 is right. **Proposition 2.5 and its proof** (l. 370–376): the change of variables `u_i := x_i − 1` is in the proof: v2 l. 219 is right. **HOLDS.**
- **[IKKY23, §7]** (`Adinkras_arXiv2202.02821.txt` l. 1311–1312, inside §7 «The 2-rank of the Laplacian, signed and unsigned», which starts at l. 1293): «the 2-Sylow subgroup of their critical groups, or even the just 2-rank of the Laplacians, has been rather difficult to understand». v2 quotes it verbatim with «[sic]» after «the just» (v1 had silently corrected it to «even just»). **HOLDS.** [IKKY23, Proposition 37] is l. 1343, in §7, and is what GMMY's Lemma 2.11 cites. **HOLDS.**
- **[Bai03, p. 253]** «still unknown» (l. 144–145, between the page headers 253 and 254), **[DJ14]** (l. 308–309), **[CSX17, §5.2]** (l. 850–854), **[GMM19]** «remains a mystery» and the `(n+1)`-th factor `c_{n+1}(Q_n) = max_{x<n−1}{v_2(x) + x}` for `n ≥ 4` (poster l. 13–14): all verbatim and correctly located. **HOLDS.**
- **New paragraph after Corollary 1.5** (v2 l. 110): «in his proof the Smith form of the Laplacian of `Q_n` has `2^{n−1}` entries `1`, and the others are those of a matrix with even entries [Bai03, Lemma 2.2, Corollary 2.3]». Bai's Corollary 2.3 (l. 265–271): exactly `2^{n−1}` ones, the rest from `L_{n−1}(L_{n−1} + 2) ∈ M(2Z)`. Right; and Bai's Theorem 1.1 counts invariant factors of `K(Q_n)` (l. 89, 276). **HOLDS.**

### 4.3 The references whose data changed: [GMMY24], [IKKY23], [Yue24], [DHS18]

Queries and answers in `checks/QUERIES.md` (Crossref metadata, the journal pages and arXiv):
- **[GMMY24]** *Comm. Algebra* 52 (2024), no. 10, 4459–4479, doi:10.1080/00927872.2024.2347582 — Crossref gives exactly volume 52, issue 10, pages 4459–4479, 2024. **HOLDS.** «arXiv:1912.06919v3 (cited by its numbering)»: the numbering I checked in §4.2 is that of v3. **HOLDS.**
- **[IKKY23]** *Adv. in Appl. Math.* 143 (2023), 102450 — Crossref agrees (DOI 10.1016/j.aam.2022.102450, which v2 does not print; optional). **HOLDS.**
- **[Yue24]** *Electron. J. Combin.* 31(1) (2024), P1.38 — Crossref agrees (DOI 10.37236/11758). **HOLDS.**
- **[DHS18]** *Linear Algebra Appl.* 546 (2018), 154–168 — arXiv's journal reference agrees (Crossref was rate-limited). **HOLDS.**
- **The renamed labels in the text.** `IKKY22`, `Yue23`, `DHS17` occur nowhere in v2 (grep, `logs/oldnames_grep.log`); every `[IKKY23]`, `[Yue24]`, `[DHS18]` in the text has its entry. **HOLDS.**
- §11.1 changed «the non-generic ones of [Yue23]» to «in the sense of [GMMY24], see also [Yue24]»: right, the definition is GMMY's §2.2 (`𝟙 ∈ ker M`). **HOLDS.**

## 5. The rendering

`pdftoppm -r 80 -png` on `THE_DANCING_SAND_THEOREM_v2.pdf` (43 pages, A4; log `logs/render.log`), every page looked at, in order, as an image; two crops at 200 dpi where I was in doubt (`logs/render_zoom*.log`); and `pdftotext -bbox` to look for overflow (`engines/margin_check.py`, `logs/margin_check.log`).

**Not found:** no word runs past the right margin (the largest `xMax` is 541.9 pt on every page — the edge of the text block — and 535.4 on p. 40); no cut or overflowing table (the §1.0, §1.6, §1.7, §4.4, §12.1 and §12.2 tables are inside the margins; multi-page tables repeat their header); no heading alone at the foot of a page; no end-of-proof mark alone on a line; no exponent or index separated from its base that I could see at 80 dpi. The `≠` that looks like «=/» at 80 dpi is the italic `≠` glyph (crop of p. 16, Lemma 4.5, and p. 23, (Cut)): fine.

**Found (all PRESENTATION, minor unless said):**
1. **p. 23, the heart of the repair:** in the pdf the cases (a), (b), (c), (d) of step 3 of the proof of Theorem 7.8 and the closing «In each case the mirror cut is strict…» run together as one block of about 25 lines. In the md they are on separate lines, but they are continuation lines of one list item, so Markdown joins them; the pdf is faithful to the md, and hard to read exactly where the reader most needs it. Same on p. 25 for «The case `i ≥ 1`» / «The case `i = 0`» of Theorem 7.10, and on p. 26 for (a)–(c) of Proposition 9.3. **PRESENTATION (worth fixing): put each case in its own paragraph.**
2. Formulas broken inside a bracket, a sum or a fraction (the builder allows breaks in formulas over 28 characters, but these breaks fall inside a sub-expression):
   - p. 11, proof of Prop. 3.1(a): «`F(2` | `b_1 E n)`»;
   - p. 12, Prop. 3.1(c), (d) and Lemma 3.3: «`(w +` | `2j)^2`», «`F(b_1` | `w_s)`», «`Hom_{Dist_{F_2}}(M ⊗` | `F_2, N ⊗ F_2)`»;
   - p. 15, display in the proof of Prop. 4.2: «`2Σ_{u>s'}` | `K_{us'}(2f+1) C_n ι_u`» — a summation sign at the end of a line, its summand on the next;
   - p. 16, Theorem D: «`(α +` | `v_2(i + d))`»;
   - p. 18, the shift `i = 0`: «`Σ_{d=x}^{y−1}` | `v_2(d)`» (again a sum sign separated from its summand);
   - p. 24, step 5 of Theorem 7.8: «`α(2^c` | `− 1)`»;
   - p. 32, Lemma 10.10: «`… η^L /` | `∏_{d=f−L}^{f} π(d)`» (a fraction split at the slash);
   - p. 35, Corollary 10.17, and p. 36, Theorem 10.22, in the statements: «`2X(2l +` | `1, j)`», «`2X(2l +` | `2, i)`»;
   - p. 39, under the §12.1 table: «`{1:` | `6, 3: 4, 4: 1, 6: 4}`»;
   - p. 43, [TW21]: «`440–` | `480`».
3. Breaks at a top-level operator, acceptable but noted: p. 2 (table, `a_n = 2^{n−2} −` | `2^{⌊(n−2)/2⌋}`), p. 4 (Main Theorem display), p. 5 (Corollary 1.7), p. 14 (display in the proof of Prop. 4.1 ending with «`b_0 n ι_u,`» alone on a line), p. 15 (Theorem 4.4).

The ten defects of v1's rendering listed in CORRECTIONS §8 I cannot compare (I do not have the v1 pdf); its claim «No line runs past the right margin» is confirmed.

## 6. The author's gates (§6 of the mission)

Opened only after §2–§5 were written (diary, 2026-10-05 17:10:06). The gates were copied to `scratch/author_gates/` (md5 identical to the originals and to `MANIFEST_md5.txt`) and run there under the watchdog with `PYTHONDONTWRITEBYTECODE=1`, so nothing was written into `material/`. Predictions S15–S18 were sealed after reading the code and before running it; all four hit.

### 6.1 `gate_strict_cut.py` (§12.1 row «Theorem 7.8, strict (Cut); Lemma 7.2(b) where it is applied …»)

Run: `python3 gate_strict_cut.py 6 4` → `{'houses': 16380, 'bnd': 8001, 'strict_fail': 0, 'pen_checks': 393120, 'pen_fail': 0, 'del_checks': 360, 'del_fail': 0}`, controls `True` (log `logs/author_strict_cut_6_4.log`, `VIGIA-FIN-OK exit=0`, 20 s).
- **What it checks.** Over every house with `1 ≤ k ≤ 6`, every `I`, every `ℓ`, `α = 1, 2, 3`, from the definitions of §7.3 (written independently of mine, same results): (1) the strict drop `fit(x_H)_{b−1} > fit(x_H)_b` at the first dancer `b` with `J_H = 1` and at `N − b`; it does not test «cut» separately, but a strict drop is a cut (Lemma 7.1 is local), so this is the strict (Cut) of Theorem 7.8; (2) for all 24 pairs `(P_r, P_c) ∈ [0, 4]^2 ∖ {(0, 0)}`, the integer fit of `x_H + shift` equals `ŷ_H + shift`; (3) at `ℓ = 2^k − 1`, the integer fit of `x_H` without `∅` is `ŷ_H` without `∅`. **That is what the row says.** It does not check «same level sets» or Lemma 7.9's separation after the shifts (my gate does, §2.3); the row does not claim them.
- **The count «393 120 shifts».** The penalty loop sits outside the `if b is not None` test, so it runs on all 16 380 houses; on the 8 379 houses with `J_H ≡ 0` the shift is the zero vector. Non-trivial shifts: `24 × 8 001 = 192 024`, my number. **The row doubles the count of meaningful shift-tests. PRESENTATION:** print «192 024 non-zero shifts (24 on each of the 8 001 houses with a boundary)».
- **Can its control fail?** The only control is the fixed example `x = (3, 4, 3, 4)`, `δ = (1, 1, 0, 0)`: it shows that the comparison of integer fits detects that one counterexample. It is not a control of the house loop: nothing in the run shows that the strict-drop test or the shift test could fail on houses. Moreover, because every `fit(x_H)` is integral (§2.5), the integer-shift test on houses can only fail through the real part, so a «jump at a non-strict cut» can never make it fail there. House-level controls that do fire are easy (mine, §2.3: price outside the interval, shift one position late, strictness tested at `b + 1`). **PRESENTATION (weak control).**
- **Numbers vs mine:** houses, boundaries, deletions identical (16 380, 8 001, 360); shifts 393 120 vs 192 024 non-trivial (explained above).

### 6.2 `gate_lemma72.py` (§12.1 row «Lemma 7.2(b) on random sequences»)

Run: `python3 gate_lemma72.py 9 20000` → «(A) real part: 15746 trials, 0 failures; (B) … 0 failures; control: … 2841 trials, integer part broken in 189; example … True» (`logs/author_lemma72_9_20000.log`, 6 s).
- **What it checks.** Random integer sequences, length `2..9`, entries `[−6, 6]`, seed `2026`: (A) `δ` jumping at random cuts (strict or not): the real part; (B) `δ` jumping only at strict cuts: the integer part. **That is what the row says.** It does not check the new clauses «`fit(x + δ)` has the level sets of `fit(x)`» and «strict cuts stay strict» (mine does, §2.2), and it prints the number of (A) trials but not of (B) trials. Minor.
- **Can its control fail?** Yes, and it does: jumps at non-strict cuts break the integer part in 189 of 2 841 trials — reproduced exactly.
- **Numbers vs mine:** their control rate 189 / 2 841 = 6.7 %, mine 736 / 9 939 = 7.4 % (other distribution and seed); both 0 failures on the restated (b).

### 6.3 `gate_theoremO.py` (§12.1 row «Theorem 6.2: exactly one golden bijection»)

Run: `python3 gate_theoremO.py 5` → «69 (s, r) cases, 0 with a count != 1; control c1 (any subset): … 42 cases; control c2 (any run): … 26 cases» (`logs/author_theoremO_5.log`).
- **What it checks.** For `s = |I| ≤ 5` and every `0 ≤ r ≤ 2^s`, a brute-force count (stopped at 2) of the bijections `L_r → F_r` all of whose arrows are golden, with «golden» coded as «`e ⊆ p` and `p ∖ e` empty or a block of top bits» — exactly the reformulation in the proof of Theorem 6.2 (Theorem O depends only on `s`). **That is what the row says.** `69 = Σ_{s=0}^{5}(2^s + 1)`.
- **Controls:** «any subset» and «any run of digits» in place of «golden» give a count `≠ 1` in 42 and 26 cases: they can fail and do.

### 6.4 The measurements of Remark (2) (`remark2/gate_remark2.py`, seed 11)

Runs (`logs/author_remark2_{generic_rand,oddU_rand,generic_eta,oddU_eta}.log`, 27–68 s each): generic/rand **245 / 248 clean**, the three unclean at `l = 63` (`c = 1, 2, 3`); oddU/rand **169 / 248**, 79 unclean, the first at `l = 32`; generic/eta and oddU/eta **248 / 248** each, 496 in all. **Exactly the numbers of Remark (2).** The driver implements the text's description (`α = 2`, `l = 2..63`, `c = 1..4`, `ζ_m ∈ [−5, 5]`, `q(d) ∈ [−9, 9]` with a draw `0` replaced by `1` — so «non-zero» describes the range, not the distribution, as the driver's header says — and `u(d) = 2·randint(−9, 9) + 1 ∈ [−17, 19]`). I did not read the three engines of flight 9 line by line (§9).

### 6.5 Beyond the three: the «1 550 cells» of the Theorem 7.10 row (`gate_sections5to7.py`, read, not run)

The loop runs over `1 ≤ λ ≤ 63`, `α = 1, 2`, `0 ≤ i ≤ 12`, skips `(i = 0, α = 2)`, and tests the Smith form only when `2^{|I|} ≤ 16` — which excludes `λ = 62` (`I = {0, …, 4}`). `63·13·2 − 63 − 25 = 1 550`. So the §12.1 range «`λ < 64`, `i ≤ 12`, `α = 1, 2`» is wider than what was run (no `λ = 62`, no `i = 0` at `α = 2`). **PRESENTATION:** state the range as run. My gate (§2.4) covers all 1 638 cells of the stated range, including `λ = 62` and `i = 0, α = 2`: 0 failures, so the statement is true on the range as printed.

## 7. Sealed predictions, hits and failures

All sealed in `checks/SEALED.md` before the measurement, with odds; outcomes written there in the same size of type.

| # | prediction (short) | odds | outcome |
|---|---|---|---|
| S1 | my hand counterexample `(1, 2, 0, 3)`, `δ = (1, 1, 0, 0)` | 98 : 2 | **hit** |
| S2 | no counterexample of length ≤ 3; some of length 4 | 90 : 10 | **hit** (but the first one found is the text's own example translated — not new) |
| S3 | restated Lemma 7.2(b): 0 failures on random inputs | 98 : 2 | **hit** (50 000) |
| S4 | control fails in 5–60 % of non-strict jumps | 70 : 30 | **hit** (7.4 %) |
| S5 | strict (Cut) on 16 380 houses, 0 failures; exactly 8 001 boundaries | 97 : 3; 99 : 1 | **hit**, **hit** |
| S6 | (E), (M), (G), (Λ) with both ends of the price interval | 95 : 5 | **hit** |
| S7 | wrong price and late shift controls fire | 90 : 10; 80 : 20 | **hit**, **hit** |
| S8 | Lemma 7.9 after shifts and deletion | 95 : 5 | **hit** |
| S9 | Theorem 7.10 = true Smith form, `λ ≤ 63`, `i ≤ 12` | 96 : 4 | **hit** (1 638 cells) |
| S10 | raw-clocks control rejected; floors-first control rejected somewhere | 95 : 5; 85 : 15 | **hit**; **FAILED — my control could not fail** (sorted multisets; §8) |
| S11 | ≥ 10 % of cells exercise the repaired step | 75 : 25 | **MISS** (8.2 %) |
| S12 | rounded-real-fit control fires; late-penalty control fires; some non-integer level-set mean | 80 : 20; 85 : 15; 85 : 15 | **MISS**; **hit**; **MISS** (there is none, §2.5) |
| S13 | Theorem 7.10, `λ ≤ 127`, `i ≤ 30`: 0 failures | 95 : 5 | **hit** (7 874 cells) |
| S14 | some house has a non-integer level-set mean | 70 : 30 | **MISS** (none in 65 532 houses; then proved impossible) |
| S15 | author's `gate_strict_cut.py 6 4` numbers, incl. 393 120 = 24 × 16 380 | 95 : 5 | **hit** |
| S16 | author's `gate_lemma72.py`: control 189 / 2 841 exactly | 85 : 15 | **hit** |
| S17 | author's `gate_theoremO.py`: 69 / 42 / 26 | 95 : 5 | **hit** |
| S18 | Remark (2): 245, 169, 248, 248 clean | 75 : 25 | **hit** |

Tally: 23 sealed claims (counting the parts of S5, S7, S10, S12 separately), **18 hits, 5 failures** (S10 second part, S11, S12 first and third parts, S14). The failures share one cause: I did not foresee that the fits of houses are integral.

## 8. My errors

1. **A control that could not fail** (S10): in `gate_t710_mine.py` I first compared «floors-first rounding» with the Smith form as *sorted* lists; the two roundings give the same multiset, so the control was blind by construction. Found because it never fired; replaced by the late-penalty control, which fires (§2.4). The bad run stays in `logs/gate_t710_63_12.log`.
2. **A second blind control** (S12 (i)): «round the real fit» cannot differ from the integer fit on houses, because the fit is integral (§2.5). I sealed it before knowing that.
3. **Wrong expectation** (S11, S14): I expected non-integral level sets in houses and a larger share of cells exercising the repair.
4. **A regex bug** in my first cross-reference check (`logs/xref_check.log`): top-level headings «## 8. …» were not recognised, which produced dozens of false «section not found». Fixed and re-run (`logs/xref_check2.log`).
5. **Two render crops missed their target** (`logs/render_zoom.log`); redone (`logs/render_zoom2.log`).
6. **Over-specific claim in §3.0**: I first named «the four entries» of Appendix A as if I knew which they were; corrected to a list of candidates.
7. **A time not noted**: in `checks/QUERIES.md` I did not note when the web queries started (only when they ended), and in §6 I first wrote an approximate time; corrected from the diary.
8. **Commands outside the watchdog.** Every computation ran under `vigia.sh` with its estimate in the diary. Outside it ran only: file writing and editing (the report, the diary, my scripts — via the editor or small `python3` text substitutions), one `ast.parse` syntax check of my own script, `ls`/`grep`/`sed`/`cat` reads, and the `cp` + `md5` of the author's gates into `scratch/` (with a `diff` of the two md5 lists). None of these is a computation of the mathematics, but the syntax check and the md5 comparison are computations in the literal sense of the rule.
9. **Working directory drift**: one `cd engines` in a compound command left the shell in `engines/` for the next call; harmless (the next command used absolute paths), noted for the record.

## 9. What I did not read

- **Unchanged text** (mission §5): §2–§6, §8, §10.1–§10.4, §10.6–§10.8 were not re-graded, except the changed hunks (all graded in §3.1) and what the repair depends on, which I read whole: §5 (Props. 5.2–5.4), §6, §7, §8, §9.2, and §3.1, §3.4, §4.3–§4.5 for the vocabulary and the example. Lemma 7.2(a), (c), Lemma 7.3, Theorem 7.4 and steps 4–8 of Theorem 7.8 are unchanged: I used them, checked them by machine on houses (§2.3), but did not re-derive them by pencil in this reading. Proposition 9.6 (M) and (K) and Lemma 9.5 are unchanged in substance: not re-derived.
- **§10:** only the changed hunks (renamings, the faithfulness argument of §10.3, Remark (2), the `W_±` sentence of Theorem 10.22). The proofs of Theorems 10.12, 10.15, 10.16, 10.22 were not re-read.
- **The Main Theorem against the graphs:** not recomputed (mission §5). I did compare Theorem 7.10 with the Smith form of `M` (§2.4), and the Main Theorem's rule with it for `α = 1`, but not with Laplacians.
- **The author's code beyond the three gates of §6:** `gate_direct.py`, `gate_dance.py`, `gate_section9.py`, `gate_section10.py`, `rule_abs.py` not read and not run; of `gate_sections5to7.py` I read only the Theorem 7.10 loop; the three flight-9 engines of `remark2/` (`fdance.py`, `tilt_dp.py`, `g9_explore.py`) only skimmed (their entry points and `e2`) — I ran them, I did not read them.
- **§12.2:** the other readers' code and logs are not given; those rows I could only check for internal consistency.
- **Sources:** I read the passages cited by changed text (and their surroundings), not the whole papers. Crossref's rendering of the GMMY title (F or Z) not checked.
- **The pdf** at 80 dpi: an index or exponent displaced by a pixel or two could escape me; I zoomed only where in doubt (two crops). I have no v1 pdf, so the ten v1 rendering defects of CORRECTIONS §8 are not compared.

## 10. Files with md5

The report cannot carry its own md5: it is in the last line of `logs/DIARY.md`. Computed under the watchdog (`logs/md5_section10.log`), after the last edit of each file listed. `material/`, `MISSION.md` and `vigia.sh` were re-checked against `MANIFEST_md5.txt` at the end: unchanged (`logs/md5_files.log`). `logs/DIARY.md` keeps growing after this table and is not listed.

| md5 | file |
|---|---|
| `c6b781703ea5f2b9a7a1e63fb310e967` | `CLAUDE.md` |
| `efdfeb67be99d504241e0037d90444f5` | `checks/QUERIES.md` |
| `dd6ddd39c2f2c5a9650aadec5d31b32f` | `checks/SEALED.md` |
| `1a931e5a9564c2335da9f3a8260b9594` | `engines/fitfast.py` |
| `2e1bebf5880ab11a840501867f235d06` | `engines/fitlib.py` |
| `c4f0fc629107d4873fd0a5b63a3c9777` | `engines/gate_houses_mine.py` |
| `2a9c7a176a434098b99875d002db3def` | `engines/gate_l72_mine.py` |
| `90b82c2150abb75889d0db25e09672c6` | `engines/gate_t710_mine.py` |
| `a4ead011e50d486a41d81d39249aedca` | `engines/margin_check.py` |
| `b522f8411c1ef310d267e284b14088bd` | `engines/scan_nonintegral.py` |
| `34baac0beea7b0007dfd99ee6bce2fb8` | `engines/xref_check.py` |
| `d0fae4ce2327bb1653336ed9ff7253b5` | `logs/author_lemma72_9_20000.log` |
| `090adb286476494755b176597964b409` | `logs/author_remark2_generic_eta.log` |
| `ca61bc6883b479b3025a091b22e28190` | `logs/author_remark2_generic_rand.log` |
| `9138bbacfd44e86f98048dc1f2f3d05a` | `logs/author_remark2_oddU_eta.log` |
| `b7ea295e63626b1b44f52fc24a412aac` | `logs/author_remark2_oddU_rand.log` |
| `95a486045eb7888daf0b3e65c0010ec8` | `logs/author_strict_cut_6_4.log` |
| `ccbe6a0cb575c1bafc6e24cfce417ba2` | `logs/author_theoremO_5.log` |
| `7fb2b30c62b3ae9c8a6f2b9700049402` | `logs/fitlib_selftest.log` |
| `1dcf48972bbfbddd17f75b0cb777cb27` | `logs/gate_houses_k3.log` |
| `68d6435d932114a95f5849c813b70c5c` | `logs/gate_houses_k3_again.log` |
| `11877d4b66d9013295529353692a1f70` | `logs/gate_houses_k6.log` |
| `63477179508a79a640c516ece6f15dda` | `logs/gate_houses_k7.log` |
| `f3cce9869e908a2be1311a19f611fee2` | `logs/gate_l72_mine.log` |
| `27bda0b23e97477488bb5e468c0571e5` | `logs/gate_t710_127_30.log` |
| `01fcade0d5fa8d5dd2792c3148da1aa8` | `logs/gate_t710_63_12.log` |
| `42ffa0c257ef768ac0addab5d6ed7f1b` | `logs/gate_t710_63_12_v2.log` |
| `a5fd3594f29ddb9fd3896009048f0eb6` | `logs/margin_check.log` |
| `4f8119c56b26950959d98a159a14b83f` | `logs/md5_files.log` |
| `b98d929fd46c32bdcf79712a1ef35f50` | `logs/md5check.log` |
| `d0103a6a307b4e7c5e27259bd0d51663` | `logs/oldnames_grep.log` |
| `d5fc30c95317bbacc277bf8e602fb1fd` | `logs/regen_diff.log` |
| `0f4e0f28e0af808829125977714c65cc` | `logs/render.log` |
| `ee5f7bc540c636d92a9e951428f2b8a1` | `logs/render_zoom.log` |
| `ec7e96c4a20929cb119cb9e32e6e5fd8` | `logs/render_zoom2.log` |
| `76ca173093a05c6ad1affdf67367ded9` | `logs/scan_nonintegral.log` |
| `d0112a7865ee050967aa49ca5e4791d8` | `logs/xref_check.log` |
| `1ff361cff850d2636f3ddef7ca17ff4c` | `logs/xref_check2.log` |

Scratch files (not deliverables): `scratch/render/` (page images), `scratch/author_gates/` (copies of the author's gates, md5-identical to the originals), `scratch/mydiff*.txt`, `scratch/bbox.html`, `scratch/*md5*.txt`.
